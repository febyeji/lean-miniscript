import LeanMiniscript.Psbt.FinalizerProofs
import LeanMiniscript.Psbt.TransactionExtractionProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- Decoding a finalized input recovers the witness written by the finalizer.
The bounds are the uint64 limits of the witness serialization format. -/
theorem decodeInput_finalizedInputMap {version : Nat} {map : KeyValueMap}
    {final : FinalInput} {input : InputFields}
    (nonempty : final.witness ≠ []) (count : final.witness.length < 2 ^ 64)
    (bounded : ∀ item ∈ final.witness, item.size < 2 ^ 64)
    (decoded : decodeInput version (finalizedInputMap map final) = .ok input) :
    input.finalScriptWitness = some final.witness := by
  by_cases empty : final.scriptSig = ByteArray.empty
  · refine decodeInput_append_finalWitness
      (version := version) (map := map.filter keepAfterFinalize)
      final.witness count bounded ?_
    simpa [finalizedInputMap, empty, nonempty] using decoded
  · refine decodeInput_append_finalWitness
      (version := version) (map := map.filter keepAfterFinalize ++
        [⟨recordKey KeyType.inFinalScriptSig, final.scriptSig⟩])
      final.witness count bounded ?_
    simpa [finalizedInputMap, empty, nonempty, List.append_assoc] using decoded

/-- Finalization validates the resulting PSBT again. -/
theorem Psbt.finalizeInput_decodes {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor}
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    ∃ decoded, result.decode = .ok decoded := by
  unfold Psbt.finalizeInput at finalized
  cases hd : (liftPsbt psbt.decode).mapError FinalizeError.role with
  | error error => simp [hd, bind, Except.bind] at finalized
  | ok decoded =>
      have original : psbt.decode = .ok decoded := by
        cases h : psbt.decode <;> simp_all [liftPsbt, Except.mapError]
      simp only [hd, bind, Except.bind] at finalized
      cases hi : (decoded.input index).mapError FinalizeError.role with
      | error error => simp [hi] at finalized
      | ok input =>
          simp only [hi] at finalized
          split at finalized
          · cases finalized; exact ⟨decoded, original⟩
          · cases hf : decoded.finalInput config index descriptor with
            | error error => simp [hf] at finalized
            | ok final =>
                simp only [hf] at finalized
                cases hu : (psbt.modifyInput index (finalizedInputMap · final)).mapError FinalizeError.role with
                | error error => simp [hu] at finalized
                | ok updated =>
                    simp only [hu] at finalized
                    unfold Psbt.checked at finalized
                    cases hc : updated.decode with
                    | error error => simp [hc, liftPsbt, Except.mapError, bind, Except.bind] at finalized
                    | ok fields =>
                        simp only [hc, liftPsbt, Except.mapError, bind, Except.bind,
                          pure, Except.pure, Except.ok.injEq] at finalized
                        subst result
                        exact ⟨fields, hc⟩

/-- The transaction extractor uses the finalizer's witness on a newly
finalized input, whenever extraction succeeds and its serialized lengths fit. -/
theorem finalizedInputMap_extracted_witness {psbt : Psbt} {index : Nat}
    {final : FinalInput} {decoded : DecodedPsbt} {tx : WitnessTransaction}
    (inRange : index < psbt.inputs.length)
    (nonempty : final.witness ≠ []) (count : final.witness.length < 2 ^ 64)
    (bounded : ∀ item ∈ final.witness, item.size < 2 ^ 64)
    (decodes : ({ psbt with inputs :=
      (psbt.inputs.modify index (fun map => finalizedInputMap map final)) } : Psbt).decode =
      .ok decoded)
    (extracted : decoded.finalTransaction = .ok tx) :
    tx.witnesses[index]? = some final.witness := by
  have found : (psbt.inputs.modify index (finalizedInputMap · final))[index]? =
      some (finalizedInputMap psbt.inputs[index] final) := by
    simp [inRange]
  obtain ⟨input, selected, read⟩ := Psbt.decode_input decodes found
  have witness := decodeInput_finalizedInputMap nonempty count bounded read
  simpa [witness] using DecodedPsbt.finalTransaction_witness extracted selected

/-- Successful finalization either preserves an already finalized PSBT, or
its generated witness reaches the extractor unchanged. -/
theorem Psbt.finalizeInput_extracted_witness {config : FinalizerConfig}
    {psbt result : Psbt} {index : Nat} {descriptor : OutputDescriptor}
    {decodedResult : DecodedPsbt} {tx : WitnessTransaction}
    (finalized : psbt.finalizeInput config index descriptor = .ok result)
    (decodes : result.decode = .ok decodedResult)
    (extracted : decodedResult.finalTransaction = .ok tx) :
    result = psbt ∨ ∃ original final,
      psbt.decode = .ok original ∧
      original.finalInput config index descriptor = .ok final ∧
      (final.witness ≠ [] → final.witness.length < 2 ^ 64 →
        (∀ item ∈ final.witness, item.size < 2 ^ 64) →
        tx.witnesses[index]? = some final.witness) := by
  obtain ⟨original, input, source, found, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, same⟩ | ⟨final, produced, inRange, same⟩
  · exact .inl same
  · refine .inr ⟨original, final, source, produced, ?_⟩
    intro nonempty count bounded
    rw [same] at decodes
    exact finalizedInputMap_extracted_witness inRange nonempty count bounded decodes extracted

end LeanMiniscript.Psbt
