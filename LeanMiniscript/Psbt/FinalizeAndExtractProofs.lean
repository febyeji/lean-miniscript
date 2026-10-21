import LeanMiniscript.Psbt.FinalizationTraceProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- The length conditions needed to read back a serialized witness. -/
def FinalInput.WitnessFits (final : FinalInput) : Prop :=
  final.witness.length < 2 ^ 64 ∧ ∀ item ∈ final.witness, item.size < 2 ^ 64

/-- An extracted input either retains the caller's final fields, or is the
exact result of a verified finalizer in its recorded transaction context. -/
def ExtractedInputSource (config : FinalizerConfig) (original : Psbt)
    (version index : Nat) (final : FinalInput) : Prop :=
  (∃ map input, original.inputs[index]? = some map ∧
    decodeInput version map = .ok input ∧ input.isFinalized = true ∧ input.finalInput = final) ∨
  ∃ (stage : Psbt) (decoded : DecodedPsbt) (descriptor : OutputDescriptor), stage.decode = .ok decoded ∧
    decoded.finalInput config index descriptor = .ok final ∧
    FinalInputVerified config decoded index descriptor final

private theorem source_of_map {config : FinalizerConfig} {original : Psbt}
    {version index : Nat} {map : KeyValueMap} {input : InputFields}
    (bounds : ∀ decoded index descriptor final,
      DecodedPsbt.finalInput config decoded index descriptor = .ok final → final.WitnessFits)
    (source : FinalizedMapSource config original index map)
    (read : decodeInput version map = .ok input) (ready : input.isFinalized = true) :
    ExtractedInputSource config original version index input.finalInput := by
  rcases source with preserved | ⟨stage, decoded, descriptor, prior, final,
      decodedEq, _, produced, verified, rfl⟩
  · exact .inl ⟨map, input, preserved, read, ready, rfl⟩
  · obtain ⟨count, items⟩ := bounds decoded index descriptor final produced
    have fields := decodeInput_finalizedInputMap_finals count items read
    rw [fields]
    exact .inr ⟨stage, decoded, descriptor, decodedEq, produced, verified⟩

/-- Whole-PSBT finalization and extraction: every returned input retains its
source, both final fields reach the transaction, and the returned bytes are
its network serialization. The caller supplies uint64 witness length bounds.
Preserved inputs remain explicit because finalization does not reverify them. -/
theorem Psbt.finalizeAndExtract_spec {config : FinalizerConfig} {psbt : Psbt}
    {descriptors : List (Option OutputDescriptor)} {bytes : ByteArray}
    (bounds : ∀ decoded index descriptor final,
      DecodedPsbt.finalInput config decoded index descriptor = .ok final → final.WitnessFits)
    (completed : psbt.finalizeAndExtract config descriptors = .ok bytes) :
    ∃ result decoded tx unsigned,
      psbt.finalize config descriptors = .ok result ∧
      result.decode = .ok decoded ∧ decoded.finalTransaction = .ok tx ∧
      decoded.unsignedTransaction = .ok unsigned ∧
      bytes = serializeWitnessTransaction tx.transaction tx.witnesses ∧
      tx.transaction.version = unsigned.version ∧
      tx.transaction.outputs = unsigned.outputs ∧
      tx.transaction.locktime = unsigned.locktime ∧
      tx.transaction.inputs.size = psbt.inputs.length ∧
      tx.witnesses.length = psbt.inputs.length ∧
      ∀ index, index < psbt.inputs.length → ∃ (input : InputFields) (original : TxInput),
        decoded.inputs[index]? = some input ∧ input.isFinalized = true ∧
        unsigned.inputs[index]? = some original ∧
        tx.transaction.inputs[index]? = some { original with scriptSig := input.finalInput.scriptSig } ∧
        tx.witnesses[index]? = some input.finalInput.witness ∧
        ExtractedInputSource config psbt decoded.global.psbtVersion index input.finalInput := by
  unfold Psbt.finalizeAndExtract at completed
  cases hf : psbt.finalize config descriptors with
  | error error => simp [hf, bind, Except.bind] at completed
  | ok result =>
    simp only [hf, bind, Except.bind] at completed
    have extracted : result.extract = .ok bytes := by
      cases h : result.extract <;> simp_all [Except.mapError]
    obtain ⟨decoded, tx, read, extractedTx, serialized⟩ := Psbt.extract_spec extracted
    obtain ⟨_, _, length, sources⟩ := Psbt.finalize_sources hf
    have inputLength := (Psbt.decode_shape read).2.2
    obtain ⟨unsigned, unsignedEq, version, outputs, locktime, count, witnesses, fields⟩ :=
      DecodedPsbt.finalTransaction_spec (fun _ h => Psbt.unsignedTransaction_inputCount read h) extractedTx
    refine ⟨result, decoded, tx, unsigned, rfl, read, extractedTx, unsignedEq, serialized,
      version, outputs, locktime, count.trans (inputLength.trans length),
      witnesses.trans (inputLength.trans length), ?_⟩
    intro index range
    have decodedRange : index < decoded.inputs.length := by omega
    have mapRange : index < result.inputs.length := by omega
    have found := List.getElem?_eq_getElem decodedRange
    obtain ⟨ready, ⟨original, originalEq, scriptSig⟩, witness⟩ := fields index _ found
    have selected := List.getElem?_eq_getElem mapRange
    obtain ⟨input, typed, inputRead⟩ := Psbt.decode_input read selected
    have same : input = decoded.inputs[index] := Option.some.inj (typed.symm.trans found)
    subst input
    exact ⟨decoded.inputs[index], original, found, ready, originalEq, scriptSig, witness,
      source_of_map bounds (sources index _ selected) inputRead ready⟩

/-- A caller's input property lifts through the whole pipeline when it holds
for retained final fields and follows from each generated input's verifier
evidence. This states the obligation for already-finalized/skipped inputs.
The evidence records each finalization context; identifying those contexts
with an external consensus verifier remains a separate contract. -/
theorem Psbt.finalizeAndExtract_preserves {config : FinalizerConfig} {psbt : Psbt}
    {descriptors : List (Option OutputDescriptor)} {bytes : ByteArray}
    (P : Nat → FinalInput → Prop)
    (bounds : ∀ decoded index descriptor final,
      DecodedPsbt.finalInput config decoded index descriptor = .ok final → final.WitnessFits)
    (existing : ∀ version index map input, psbt.inputs[index]? = some map →
      decodeInput version map = .ok input → input.isFinalized = true → P index input.finalInput)
    (generated : ∀ decoded index descriptor final,
      FinalInputVerified config decoded index descriptor final → P index final)
    (completed : psbt.finalizeAndExtract config descriptors = .ok bytes) :
    ∃ tx : WitnessTransaction,
      bytes = serializeWitnessTransaction tx.transaction tx.witnesses ∧
      tx.transaction.inputs.size = psbt.inputs.length ∧
      tx.witnesses.length = psbt.inputs.length ∧
      ∀ index, index < psbt.inputs.length → ∃ (input : TxInput) (witness : List ByteArray),
        tx.transaction.inputs[index]? = some input ∧ tx.witnesses[index]? = some witness ∧
        P index ⟨input.scriptSig, witness⟩ := by
  obtain ⟨_, decoded, tx, _, _, _, _, _, serialized, _, _, _, count, witnesses, fields⟩ :=
    Psbt.finalizeAndExtract_spec bounds completed
  refine ⟨tx, serialized, count, witnesses, ?_⟩
  intro index range
  obtain ⟨input, original, _, _, _, scriptSig, witness, source⟩ := fields index range
  have valid : P index input.finalInput := by
    rcases source with ⟨map, prior, found, read, ready, same⟩ |
      ⟨_, stage, descriptor, _, produced, verified⟩
    · rw [← same]; exact existing decoded.global.psbtVersion index map prior found read ready
    · exact generated stage index descriptor input.finalInput verified
  exact ⟨{ original with scriptSig := input.finalInput.scriptSig }, input.finalInput.witness,
    scriptSig, witness, valid⟩

end LeanMiniscript.Psbt
