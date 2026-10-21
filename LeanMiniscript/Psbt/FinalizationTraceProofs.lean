import LeanMiniscript.Psbt.FinalizerVerificationProofs
import LeanMiniscript.Psbt.TransactionExtractionProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Extraction

/-- Verification evidence for each supported descriptor, in the transaction
context used when that input was finalized. -/
def FinalInputVerified (config : FinalizerConfig) (decoded : DecodedPsbt)
    (index : Nat) (descriptor : OutputDescriptor) (final : FinalInput) : Prop :=
  match descriptor with
  | .raw _ | .shRaw _ => False
  | .pk _ | .pkh _ | .multi _ _ | .sh _ =>
      LegacyFinalVerified config decoded index descriptor final
  | .wpkh key | .shWpkh key => WpkhFinalVerified config decoded index descriptor key final
  | .wsh _ | .shWsh _ =>
      ∃ compiled spent tx, compileOutputDescriptor descriptor = .ok compiled ∧
        decoded.spentOutput index = .ok spent ∧ decoded.unsignedTransaction = .ok tx ∧
        spent.scriptPubKey = compiled.scriptPubKey ∧
        verifyWitnessV0Final config tx index compiled final spent.amount = .ok ()
  | .tr _ _ =>
      ∃ compiled tx spentOutputs, compileOutputDescriptor descriptor = .ok compiled ∧
        decoded.unsignedTransaction = .ok tx ∧ decoded.spentOutputs = .ok spentOutputs ∧
        (spentOutputs[index]?).map (·.scriptPubKey) = some compiled.scriptPubKey ∧
        final.scriptSig = ByteArray.empty ∧
        ((∃ signature, keyPathValid config tx spentOutputs index
            (compiled.scriptPubKey.extract 2 34) signature = true ∧ final.witness = [signature]) ∨
         ∃ prepared : PreparedDescriptorSatisfaction,
           prepared.verify config.oracle config.flags compiled = .ok () ∧
           final.witness = prepared.witness)

theorem DecodedPsbt.finalInput_verified {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {descriptor : OutputDescriptor} {final : FinalInput}
    (produced : decoded.finalInput config index descriptor = .ok final) :
    FinalInputVerified config decoded index descriptor final := by
  obtain ⟨input, _, _, source⟩ := finalInput_spec produced
  cases descriptor <;> unfold FinalInputVerified
  all_goals first
    | contradiction
    | exact finalizeLegacySingle_verified source
    | exact finalizeLegacyMulti_verified source
    | exact finalizeLegacyFragment_verified source
    | exact finalizeWpkh_verified source
    | (obtain ⟨compiled, spent, tx, _, _, _, hc, hs, ht, _, agrees, _, _, _, _, verified⟩ :=
        finalizeWitnessV0_spec source
       exact ⟨compiled, spent, tx, hc, hs, ht, agrees, verified⟩)
    | (obtain ⟨compiled, tx, spent, hc, ht, hs, agrees, sig, origin⟩ := finalizeTaproot_spec source
       refine ⟨compiled, tx, spent, hc, ht, hs, agrees, sig, ?_⟩
       rcases origin with ⟨signature, _, valid, witness⟩ | ⟨_, _, prepared, _, success, witness⟩
       · exact .inl ⟨signature, valid, witness⟩
       · exact .inr ⟨prepared, (scriptPath_witness_verified success).1, witness⟩)

/-- A map was preserved from the caller or written by a verified finalizer.
The generating PSBT and its decoded transaction context remain explicit. -/
def FinalizedMapSource (config : FinalizerConfig) (original : Psbt)
    (index : Nat) (map : KeyValueMap) : Prop :=
  original.inputs[index]? = some map ∨
    ∃ (stage : Psbt) (decoded : DecodedPsbt) (descriptor : OutputDescriptor)
      (prior : KeyValueMap) (final : FinalInput),
      stage.decode = .ok decoded ∧ stage.inputs[index]? = some prior ∧
      decoded.finalInput config index descriptor = .ok final ∧
      FinalInputVerified config decoded index descriptor final ∧
      map = finalizedInputMap prior final

private theorem finalizeInput_sources {config : FinalizerConfig} {original stage result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor}
    (sources : ∀ i map, stage.inputs[i]? = some map → FinalizedMapSource config original i map)
    (finalized : stage.finalizeInput config index descriptor = .ok result) :
    result.global = stage.global ∧ result.outputs = stage.outputs ∧
      result.inputs.length = stage.inputs.length ∧
      ∀ i map, result.inputs[i]? = some map → FinalizedMapSource config original i map := by
  obtain ⟨decoded, input, read, _, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, rfl⟩ | ⟨final, produced, range, rfl⟩
  · exact ⟨rfl, rfl, rfl, sources⟩
  · refine ⟨rfl, rfl, by simp, ?_⟩
    intro i map found
    by_cases same : index = i
    · subst i
      have selected : stage.inputs[index]? = some stage.inputs[index] :=
        List.getElem?_eq_getElem range
      simp [selected] at found
      exact .inr ⟨stage, decoded, descriptor, stage.inputs[index], final, read, selected,
        produced, DecodedPsbt.finalInput_verified produced, found.symm⟩
    · have prior : stage.inputs[i]? = some map := by
        simpa [List.getElem?_modify, same] using found
      exact sources i map prior

private theorem finalize_fold_sources (config : FinalizerConfig) (original : Psbt)
    (jobs : List (Option OutputDescriptor × Nat)) {stage result : Psbt}
    (sources : ∀ i map, stage.inputs[i]? = some map → FinalizedMapSource config original i map)
    (finalized : jobs.foldlM (fun psbt (job : Option OutputDescriptor × Nat) =>
      match job.1 with
      | none => pure psbt
      | some descriptor => psbt.finalizeInput config job.2 descriptor) stage = .ok result) :
    result.global = stage.global ∧ result.outputs = stage.outputs ∧
      result.inputs.length = stage.inputs.length ∧
      ∀ i map, result.inputs[i]? = some map → FinalizedMapSource config original i map := by
  induction jobs generalizing stage with
  | nil => cases finalized; exact ⟨rfl, rfl, rfl, sources⟩
  | cons job jobs ih =>
    rcases job with ⟨descriptor, index⟩
    cases descriptor with
    | none =>
      simp only [List.foldlM_cons, pure, Except.pure, bind, Except.bind] at finalized
      exact ih sources finalized
    | some descriptor =>
      simp only [List.foldlM_cons, bind, Except.bind] at finalized
      cases step : stage.finalizeInput config index descriptor with
      | error error => simp [step] at finalized
      | ok next =>
        simp only [step] at finalized
        obtain ⟨global, outputs, length, nextSources⟩ := finalizeInput_sources sources step
        obtain ⟨global', outputs', length', finalSources⟩ := ih nextSources finalized
        exact ⟨global'.trans global, outputs'.trans outputs, length'.trans length, finalSources⟩

/-- Whole-PSBT finalization preserves global/output maps and input indices.
Each final input map has a preserved or verified generated source. -/
theorem Psbt.finalize_sources {config : FinalizerConfig} {psbt result : Psbt}
    {descriptors : List (Option OutputDescriptor)}
    (finalized : psbt.finalize config descriptors = .ok result) :
    result.global = psbt.global ∧ result.outputs = psbt.outputs ∧
      result.inputs.length = psbt.inputs.length ∧
      ∀ i map, result.inputs[i]? = some map → FinalizedMapSource config psbt i map :=
  finalize_fold_sources config psbt descriptors.zipIdx (fun _ _ found => .inl found) finalized

end LeanMiniscript.Psbt
