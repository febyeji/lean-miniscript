import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Extraction.DescriptorSatisfactionProofs
import LeanMiniscript.Miniscript.SatisfactionCorrectnessProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Script
open LeanMiniscript.Extraction

/-!
# Finalizer soundness

A finalized witness is exactly what the existing satisfaction machinery
returns for the material read from the PSBT input:

* `wsh`/`sh(wsh)`: `satisfyFinal` on the sane witness-script fragment with
  `witnessV0Env`, followed by the witness script; under the existing
  environment contracts `satisfyFinalCorrectnessCore` then gives Miniscript
  acceptance of the arguments.
* `tr` script path: the witness of a `satisfyDescriptorTransaction` result for
  some descriptor leaf, so `satisfyDescriptorTransaction_ok_iff` gives the
  complete Core verification of that witness, and preparation gives the
  generated-satisfaction equation.
* `tr` key path: the PSBT key signature, after BIP340 verification against the
  output key and the BIP341 key-path digest.

`decodeAll_readWitnessStack` shows the stored witness value decodes to the
finalizer's stack.

TODO(psbt-extract-link): prove that decoding a finalized input map yields
`finalScriptWitness = some final.witness`, so the extractor's witness is the
finalizer's; this needs a lemma about the `inputStep` fold over a filtered map.
TODO(psbt-wsh-core): connect witness-v0 witnesses to Core script-pair
verification; the existing Core theorems cover Taproot descriptors only.
-/

private theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {result : Except ε α} {value : α}
    (mapped : result.mapError f = .ok value) : result = .ok value := by
  cases result <;> simp_all [Except.mapError]

theorem bestCandidate_mem {α : Type} {size : α → Nat} {candidates : List α} {best : α}
    (selected : bestCandidate size candidates = some best) : best ∈ candidates := by
  cases candidates with
  | nil => simp [bestCandidate] at selected
  | cons first rest =>
    simp only [bestCandidate, Option.some.injEq] at selected
    subst selected
    suffices ∀ (start : α), start ∈ first :: rest → ∀ (remaining : List α),
        remaining ⊆ first :: rest →
        remaining.foldl (fun best next => if size next < size best then next else best) start ∈
          first :: rest from this first (by simp) rest (by intro x h; simp [h])
    intro start member remaining
    induction remaining generalizing start with
    | nil => intro _; exact member
    | cons next others ih =>
      intro sub
      simp only [List.foldl_cons]
      apply ih
      · split
        · exact sub (by simp)
        · exact member
      · intro x h; exact sub (by simp [h])

theorem mem_scriptPathCandidates {config : FinalizerConfig} {compiled : CompiledDescriptor}
    {input : InputFields} {tx : Transaction} {spentOutputs : Array TxOutput} {index : Nat}
    {leafIndex : Nat} {prepared : PreparedDescriptorSatisfaction}
    (member : (leafIndex, prepared) ∈
      scriptPathCandidates config compiled input tx spentOutputs index) :
    ∃ leaf, compiled.taprootLeaves[leafIndex]? = some leaf ∧
      satisfyDescriptorTransaction config.oracle config.flags compiled leafIndex
        (input.tapscriptMaterial (tapleafHash leaf.script 0xc0)) tx spentOutputs index =
        .ok prepared := by
  unfold scriptPathCandidates at member
  obtain ⟨candidate, _, produced⟩ := List.mem_filterMap.mp member
  split at produced
  · simp at produced
  · rename_i leaf found
    split at produced
    · rename_i result success
      simp only [Option.some.injEq, Prod.mk.injEq] at produced
      obtain ⟨rfl, rfl⟩ := produced
      exact ⟨leaf, found, success⟩
    · simp at produced

/-- Script-path or key-path origin of a Taproot final witness. -/
def TaprootFinalSource (config : FinalizerConfig) (input : InputFields) (index : Nat)
    (compiled : CompiledDescriptor) (tx : Transaction) (spentOutputs : Array TxOutput)
    (final : FinalInput) : Prop :=
  (∃ signature, input.tapKeySig = some signature ∧
      keyPathValid config tx spentOutputs index (compiled.scriptPubKey.extract 2 34) signature = true ∧
      final.witness = [signature]) ∨
  (∃ leafIndex leaf prepared, compiled.taprootLeaves[leafIndex]? = some leaf ∧
      satisfyDescriptorTransaction config.oracle config.flags compiled leafIndex
        (input.tapscriptMaterial (tapleafHash leaf.script 0xc0)) tx spentOutputs index =
        .ok prepared ∧
      final.witness = prepared.witness)

theorem finalizeTaproot_spec {config : FinalizerConfig} {decoded : DecodedPsbt} {index : Nat}
    {input : InputFields} {descriptor : OutputDescriptor} {final : FinalInput}
    (finalized : finalizeTaproot config decoded index input descriptor = .ok final) :
    ∃ compiled tx spentOutputs,
      compileOutputDescriptor descriptor = .ok compiled ∧
      decoded.unsignedTransaction = .ok tx ∧
      decoded.spentOutputs = .ok spentOutputs ∧
      (spentOutputs[index]?).map (·.scriptPubKey) = some compiled.scriptPubKey ∧
      final.scriptSig = ByteArray.empty ∧
      TaprootFinalSource config input index compiled tx spentOutputs final := by
  unfold finalizeTaproot at finalized
  cases hc : (compileDescriptor descriptor).mapError FinalizeError.role with
  | error error => simp [hc, bind, Except.bind] at finalized
  | ok compiled =>
    have compiledEq : compileOutputDescriptor descriptor = .ok compiled := by
      have := mapError_ok hc
      unfold compileDescriptor at this
      exact mapError_ok this
    simp only [hc, bind, Except.bind] at finalized
    cases ht : (liftPsbt decoded.unsignedTransaction).mapError FinalizeError.role with
    | error error => simp [ht] at finalized
    | ok tx =>
      have txEq : decoded.unsignedTransaction = .ok tx := by
        have := mapError_ok ht
        unfold liftPsbt at this
        exact mapError_ok this
      simp only [ht] at finalized
      cases hs : decoded.spentOutputs.mapError FinalizeError.role with
      | error error => simp [hs] at finalized
      | ok spentOutputs =>
        have spentEq := mapError_ok hs
        simp only [hs] at finalized
        cases hi : spentOutputs[index]? with
        | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at finalized
        | some spent =>
          simp only [hi] at finalized
          split at finalized
          · simp [throw, throwThe, MonadExceptOf.throw] at finalized
          · rename_i agree
            have scriptEq : spent.scriptPubKey = compiled.scriptPubKey := by
              simpa using agree
            refine ⟨compiled, tx, spentOutputs, compiledEq, txEq, spentEq,
              by simp [hi, scriptEq], ?_⟩
            -- Key path, then the script-path candidates.
            cases hk : input.tapKeySig with
            | some signature =>
              simp only [hk] at finalized
              by_cases valid : keyPathValid config tx spentOutputs index
                  (compiled.scriptPubKey.extract 2 34) signature = true
              · simp only [valid, if_true, pure, Except.pure, Except.ok.injEq] at finalized
                subst finalized
                exact ⟨rfl, .inl ⟨signature, hk, valid, rfl⟩⟩
              · simp only [valid, if_false, Bool.false_eq_true] at finalized
                cases selected : bestCandidate (fun candidate => witnessSize candidate.2.witness)
                    (scriptPathCandidates config compiled input tx spentOutputs index) with
                | none => simp [selected, throw, throwThe, MonadExceptOf.throw] at finalized
                | some choice =>
                  obtain ⟨leafIndex, prepared⟩ := choice
                  simp only [selected, pure, Except.pure, Except.ok.injEq] at finalized
                  subst finalized
                  obtain ⟨leaf, found, success⟩ :=
                    mem_scriptPathCandidates (bestCandidate_mem selected)
                  exact ⟨rfl, .inr ⟨leafIndex, leaf, prepared, found, success, rfl⟩⟩
            | none =>
              simp only [hk] at finalized
              cases selected : bestCandidate (fun candidate => witnessSize candidate.2.witness)
                  (scriptPathCandidates config compiled input tx spentOutputs index) with
              | none => simp [selected, throw, throwThe, MonadExceptOf.throw] at finalized
              | some choice =>
                obtain ⟨leafIndex, prepared⟩ := choice
                simp only [selected, pure, Except.pure, Except.ok.injEq] at finalized
                subst finalized
                obtain ⟨leaf, found, success⟩ :=
                  mem_scriptPathCandidates (bestCandidate_mem selected)
                exact ⟨rfl, .inr ⟨leafIndex, leaf, prepared, found, success, rfl⟩⟩

/-- A script-path final witness passed the complete Core verifier for the
descriptor output, and its arguments are the generated satisfaction of the
selected leaf for the filtered PSBT material. -/
theorem scriptPath_witness_verified {config : FinalizerConfig} {compiled : CompiledDescriptor}
    {leafIndex : Nat} {material : DescriptorSatisfactionMaterial} {tx : Transaction}
    {spentOutputs : Array TxOutput} {index : Nat} {prepared : PreparedDescriptorSatisfaction}
    (success : satisfyDescriptorTransaction config.oracle config.flags compiled leafIndex material
      tx spentOutputs index = .ok prepared) :
    prepared.verify config.oracle config.flags compiled = .ok () ∧
    compiled.taprootLeaves[leafIndex]? = some prepared.leaf ∧
    prepared.witness = prepared.arguments ++ [prepared.leaf.script, prepared.leaf.controlBlock] ∧
    satisfyFinal prepared.sane.checked.fragment
      ((material.validated config.oracle config.flags.script prepared.context).toEnv
        prepared.context) = some prepared.arguments := by
  obtain ⟨_, _, preparation, verified⟩ :=
    (satisfyDescriptorTransaction_ok_iff _ _ _ _ _ _ _ _ _).mp success
  obtain ⟨leaf, _, generated, _⟩ := prepareDescriptorSatisfaction_spec preparation
  exact ⟨verified, leaf, rfl, generated⟩

theorem finalizeWitnessV0_spec {config : FinalizerConfig} {decoded : DecodedPsbt} {index : Nat}
    {input : InputFields} {descriptor : OutputDescriptor} {fragment : SurfaceFragment}
    {final : FinalInput}
    (finalized : finalizeWitnessV0 config decoded index input descriptor fragment = .ok final) :
    ∃ compiled spent tx witnessScript sane arguments,
      compileOutputDescriptor descriptor = .ok compiled ∧
      decoded.spentOutput index = .ok spent ∧
      decoded.unsignedTransaction = .ok tx ∧
      compiled.witnessScript = some witnessScript ∧
      spent.scriptPubKey = compiled.scriptPubKey ∧
      checkSaneSurface .p2wsh fragment = .ok sane ∧
      satisfyFinal sane.checked.fragment
        (witnessV0Env config tx index input witnessScript spent.amount) = some arguments ∧
      final.witness = arguments ++ [witnessScript] ∧
      final.scriptSig = (compiled.redeemScript.map pushData).getD ByteArray.empty := by
  unfold finalizeWitnessV0 at finalized
  cases hc : (compileDescriptor descriptor).mapError FinalizeError.role with
  | error error => simp [hc, bind, Except.bind] at finalized
  | ok compiled =>
    have compiledEq : compileOutputDescriptor descriptor = .ok compiled := by
      have := mapError_ok hc
      unfold compileDescriptor at this
      exact mapError_ok this
    simp only [hc, bind, Except.bind] at finalized
    cases hs : (decoded.spentOutput index).mapError FinalizeError.role with
    | error error => simp [hs] at finalized
    | ok spent =>
      have spentEq := mapError_ok hs
      simp only [hs] at finalized
      cases ht : (liftPsbt decoded.unsignedTransaction).mapError FinalizeError.role with
      | error error => simp [ht] at finalized
      | ok tx =>
        have txEq : decoded.unsignedTransaction = .ok tx := by
          have := mapError_ok ht
          unfold liftPsbt at this
          exact mapError_ok this
        simp only [ht] at finalized
        cases hw : compiled.witnessScript with
        | none => simp [hw, throw, throwThe, MonadExceptOf.throw] at finalized
        | some witnessScript =>
          simp only [hw] at finalized
          split at finalized
          · simp [throw, throwThe, MonadExceptOf.throw] at finalized
          · rename_i agree
            have scriptEq : spent.scriptPubKey = compiled.scriptPubKey := by simpa using agree
            split at finalized
            · simp [throw, throwThe, MonadExceptOf.throw] at finalized
            · cases hn : (checkSaneSurface .p2wsh fragment).mapError FinalizeError.notSane with
              | error error => simp [hn] at finalized
              | ok sane =>
                have saneEq := mapError_ok hn
                simp only [hn] at finalized
                split at finalized
                · simp [throw, throwThe, MonadExceptOf.throw] at finalized
                · rename_i arguments generated
                  simp only [pure, Except.pure, Except.ok.injEq] at finalized
                  subst finalized
                  exact ⟨compiled, spent, tx, witnessScript, sane, arguments, compiledEq, spentEq,
                    txEq, hw, scriptEq, saneEq, generated, rfl, rfl⟩

/-- Under the existing satisfaction-environment contracts, the witness-v0
finalizer's arguments are accepted by the witness script's Miniscript under
the modeled P2WSH semantics. -/
theorem finalizeWitnessV0_accepts {config : FinalizerConfig} {tx : Transaction} {index : Nat}
    {input : InputFields} {witnessScript : ByteArray} {amount : UInt64}
    {sane : SaneFragment .p2wsh} {arguments : Witness} {flags : ScriptFlags}
    (generated : satisfyFinal sane.checked.fragment
      (witnessV0Env config tx index input witnessScript amount) = some arguments)
    (sound : (witnessV0Env config tx index input witnessScript amount).Sound)
    (encodings : (witnessV0Env config tx index input witnessScript amount).EncodingSound flags)
    (modeled : ModeledContextFlags .p2wsh flags) :
    Accepts .p2wsh (compile sane.checked.fragment) arguments flags
      (witnessV0Context tx index) :=
  satisfyFinalCorrectnessCore sane.validMiniscript sound encodings rfl modeled generated

/-- The input finalizer for each supported descriptor shape: the PSBT
signature hash types agree, and the result is the witness-v0 or Taproot
finalizer's output. -/
theorem finalInput_spec {config : FinalizerConfig} {decoded : DecodedPsbt} {index : Nat}
    {descriptor : OutputDescriptor} {final : FinalInput}
    (finalized : decoded.finalInput config index descriptor = .ok final) :
    ∃ input, decoded.inputs[index]? = some input ∧ input.sighashTypesMatch = true ∧
      match descriptor with
      | .wsh fragment | .shWsh fragment =>
          finalizeWitnessV0 config decoded index input descriptor fragment = .ok final
      | .tr _ _ => finalizeTaproot config decoded index input descriptor = .ok final := by
  unfold DecodedPsbt.finalInput at finalized
  cases hi : (decoded.input index).mapError FinalizeError.role with
  | error error => simp [hi, bind, Except.bind] at finalized
  | ok input =>
    have inputEq := mapError_ok hi
    have found : decoded.inputs[index]? = some input := by
      unfold DecodedPsbt.input at inputEq
      split at inputEq <;> simp_all
    simp only [hi, bind, Except.bind] at finalized
    split at finalized
    · simp [throw, throwThe, MonadExceptOf.throw] at finalized
    · rename_i agree
      refine ⟨input, found, by simpa using agree, ?_⟩
      cases descriptor <;> exact finalized

/-- The finalizer leaves finalized inputs unchanged and otherwise replaces
exactly the selected input map by `finalizedInputMap` for the finalizer's
output. -/
theorem Psbt.finalizeInput_spec {config : FinalizerConfig} {psbt result : Psbt} {index : Nat}
    {descriptor : OutputDescriptor}
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    ∃ decoded input, psbt.decode = .ok decoded ∧ decoded.inputs[index]? = some input ∧
      ((input.isFinalized = true ∧ result = psbt) ∨
       (∃ final, decoded.finalInput config index descriptor = .ok final ∧
          index < psbt.inputs.length ∧
          result = { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) })) := by
  unfold Psbt.finalizeInput at finalized
  cases hd : (liftPsbt psbt.decode).mapError FinalizeError.role with
  | error error => simp [hd, bind, Except.bind] at finalized
  | ok decoded =>
    have decodeEq : psbt.decode = .ok decoded := by
      have := mapError_ok hd
      unfold liftPsbt at this
      exact mapError_ok this
    simp only [hd, bind, Except.bind] at finalized
    cases hi : (decoded.input index).mapError FinalizeError.role with
    | error error => simp [hi] at finalized
    | ok input =>
      have inputEq := mapError_ok hi
      have found : decoded.inputs[index]? = some input := by
        unfold DecodedPsbt.input at inputEq
        split at inputEq <;> simp_all
      simp only [hi] at finalized
      refine ⟨decoded, input, decodeEq, found, ?_⟩
      split at finalized
      · rename_i done
        simp only [pure, Except.pure, Except.ok.injEq] at finalized
        exact .inl ⟨done, finalized.symm⟩
      · cases hf : decoded.finalInput config index descriptor with
        | error error => simp [hf] at finalized
        | ok final =>
          simp only [hf] at finalized
          by_cases inRange : index < psbt.inputs.length
          · simp only [Psbt.modifyInput, inRange, if_true, Except.mapError] at finalized
            unfold Psbt.checked at finalized
            cases hc : liftPsbt ({ psbt with
                inputs := psbt.inputs.modify index (finalizedInputMap · final) } : Psbt).decode with
            | error error => simp [hc, bind, Except.bind] at finalized
            | ok value =>
              simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at finalized
              exact .inr ⟨final, rfl, inRange, finalized.symm⟩
          · simp [Psbt.modifyInput, inRange, Except.mapError] at finalized

/-- Finalization keeps every UTXO, BIP370 transaction field and record of a
type it does not define, and adds the final fields it produced. -/
theorem mem_finalizedInputMap {map : KeyValueMap} {final : FinalInput} {record : Record}
    (member : record ∈ map) (kept : keepAfterFinalize record = true) :
    record ∈ finalizedInputMap map final := by
  unfold finalizedInputMap
  simp [member, kept]

theorem finalScriptWitness_mem_finalizedInputMap (map : KeyValueMap) {final : FinalInput}
    (nonempty : final.witness ≠ []) :
    ⟨recordKey KeyType.inFinalScriptWitness, serializeWitness final.witness⟩ ∈
      finalizedInputMap map final := by
  unfold finalizedInputMap
  simp [nonempty]

/-! ## Headline finalizer theorems -/

/-- A Taproot input finalized against `tr(key, tree)` either was already
final, or now carries a witness that is a verified key-path signature for the
descriptor's output key, or the witness of a leaf whose generated
satisfaction passed the complete Core verifier for the descriptor output. -/
theorem Psbt.finalizeInput_taproot_sound {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {key : PubKey} {tree : Option DescriptorTree}
    (finalized : psbt.finalizeInput config index (.tr key tree) = .ok result) :
    result = psbt ∨
    ∃ decoded input final compiled tx spentOutputs,
      psbt.decode = .ok decoded ∧ decoded.inputs[index]? = some input ∧
      compileOutputDescriptor (.tr key tree) = .ok compiled ∧
      decoded.unsignedTransaction = .ok tx ∧ decoded.spentOutputs = .ok spentOutputs ∧
      result = { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) } ∧
      final.scriptSig = ByteArray.empty ∧
      ((∃ signature, input.tapKeySig = some signature ∧
          keyPathValid config tx spentOutputs index (compiled.scriptPubKey.extract 2 34) signature ∧
          final.witness = [signature]) ∨
       (∃ (leafIndex : Nat) (prepared : PreparedDescriptorSatisfaction),
          compiled.taprootLeaves[leafIndex]? = some prepared.leaf ∧
          prepared.verify config.oracle config.flags compiled = .ok () ∧
          final.witness = prepared.arguments ++ [prepared.leaf.script, prepared.leaf.controlBlock])) := by
  obtain ⟨decoded, input, decodes, found, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, same⟩ | ⟨final, produced, _, resultEq⟩
  · exact .inl same
  · right
    obtain ⟨input', found', _, taproot⟩ := finalInput_spec produced
    have sameInput : input' = input := Option.some.inj (found'.symm.trans found)
    subst sameInput
    obtain ⟨compiled, tx, spentOutputs, compiledEq, txEq, spentEq, _, scriptSig, source⟩ :=
      finalizeTaproot_spec taproot
    refine ⟨decoded, input', final, compiled, tx, spentOutputs, decodes, found, compiledEq, txEq,
      spentEq, resultEq, scriptSig, ?_⟩
    rcases source with keyPath | ⟨leafIndex, _, prepared, _, success, witness⟩
    · exact .inl keyPath
    · obtain ⟨verified, leaf, shape, _⟩ := scriptPath_witness_verified success
      exact .inr ⟨leafIndex, prepared, leaf, verified, witness.trans shape⟩

/-- A witness-v0 input finalized against `wsh(fragment)` or
`sh(wsh(fragment))` either was already final, or now carries exactly the
`satisfyFinal` result for the sane witness-script fragment and the PSBT
material, followed by the witness script; the scriptSig is the P2SH push of
the witness program for `sh(wsh)` and empty otherwise. -/
theorem Psbt.finalizeInput_witnessV0_sound {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor} {fragment : SurfaceFragment}
    (shape : descriptor = .wsh fragment ∨ descriptor = .shWsh fragment)
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    result = psbt ∨
    ∃ decoded input final compiled spent tx witnessScript sane arguments,
      psbt.decode = .ok decoded ∧ decoded.inputs[index]? = some input ∧
      compileOutputDescriptor descriptor = .ok compiled ∧
      decoded.spentOutput index = .ok spent ∧ decoded.unsignedTransaction = .ok tx ∧
      compiled.witnessScript = some witnessScript ∧
      spent.scriptPubKey = compiled.scriptPubKey ∧
      checkSaneSurface .p2wsh fragment = .ok sane ∧
      satisfyFinal sane.checked.fragment
        (witnessV0Env config tx index input witnessScript spent.amount) = some arguments ∧
      result = { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) } ∧
      final.witness = arguments ++ [witnessScript] ∧
      final.scriptSig = (compiled.redeemScript.map pushData).getD ByteArray.empty := by
  obtain ⟨decoded, input, decodes, found, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, same⟩ | ⟨final, produced, _, resultEq⟩
  · exact .inl same
  · right
    obtain ⟨input', found', _, witnessV0⟩ := finalInput_spec produced
    have sameInput : input' = input := Option.some.inj (found'.symm.trans found)
    subst sameInput
    have finalizedV0 : finalizeWitnessV0 config decoded index input' descriptor fragment =
        .ok final := by
      rcases shape with rfl | rfl <;> exact witnessV0
    obtain ⟨compiled, spent, tx, witnessScript, sane, arguments, compiledEq, spentEq, txEq,
      witnessEq, scriptEq, saneEq, generated, witness, scriptSig⟩ :=
      finalizeWitnessV0_spec finalizedV0
    exact ⟨decoded, input', final, compiled, spent, tx, witnessScript, sane, arguments, decodes,
      found, compiledEq, spentEq, txEq, witnessEq, scriptEq, saneEq, generated, resultEq,
      witness, scriptSig⟩

end LeanMiniscript.Psbt
