import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Psbt.FieldsProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-- The scriptSig and witness defaults used by the transaction extractor. -/
def InputFields.finalInput (input : InputFields) : FinalInput :=
  ⟨input.finalScriptSig.getD ByteArray.empty, input.finalScriptWitness.getD []⟩

private theorem keepAfterFinalize_not_finals {record : Record}
    (kept : keepAfterFinalize record = true) :
    record.keyType? ≠ some KeyType.inFinalScriptSig ∧
      record.keyType? ≠ some KeyType.inFinalScriptWitness := by
  constructor <;> intro key <;>
    simp [keepAfterFinalize, key, KeyType.inFinalScriptSig, KeyType.inFinalScriptWitness,
      knownInputKeyTypes] at kept

private theorem fold_kept_finals {version : Nat} {map : KeyValueMap}
    {before after : InputFields}
    (kept : ∀ record ∈ map, keepAfterFinalize record = true)
    (read : map.foldlM (inputStep version) before = .ok after) :
    after.finalScriptSig = before.finalScriptSig ∧
      after.finalScriptWitness = before.finalScriptWitness := by
  induction map generalizing before with
  | nil => cases read; exact ⟨rfl, rfl⟩
  | cons record rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at read
    cases first : inputStep version before record with
    | error error => simp [first] at read
    | ok next =>
      simp only [first] at read
      obtain ⟨notSig, notWitness⟩ := keepAfterFinalize_not_finals (kept record (by simp))
      obtain ⟨sig, witness⟩ := inputStep_preserves_finals notSig notWitness first
      obtain ⟨sig', witness'⟩ := ih (by intro r h; exact kept r (by simp [h])) read
      exact ⟨sig'.trans sig, witness'.trans witness⟩

theorem inputStep_finalScriptSig (version : Nat) (fields : InputFields) (script : ByteArray) :
    inputStep version fields ⟨recordKey KeyType.inFinalScriptSig, script⟩ =
      .ok { fields with finalScriptSig := some script } := by
  rfl

/-- Reading a finalized map recovers both final fields, including omitted
empty fields. CompactSize lengths must fit uint64. -/
theorem decodeInput_finalizedInputMap_finals {version : Nat} {map : KeyValueMap}
    {final : FinalInput} {input : InputFields}
    (count : final.witness.length < 2 ^ 64)
    (bounded : ∀ item ∈ final.witness, item.size < 2 ^ 64)
    (decoded : decodeInput version (finalizedInputMap map final) = .ok input) :
    input.finalInput = final := by
  unfold decodeInput finalizedInputMap at decoded
  simp only [List.foldlM_append, bind, Except.bind] at decoded
  cases base : (map.filter keepAfterFinalize).foldlM (inputStep version) {} with
  | error error => simp [base] at decoded
  | ok fields =>
    have kept : ∀ record ∈ map.filter keepAfterFinalize, keepAfterFinalize record = true :=
      fun record h => (List.mem_filter.mp h).2
    obtain ⟨sig, witness⟩ := fold_kept_finals kept base
    simp only [base] at decoded
    by_cases emptySig : final.scriptSig = ByteArray.empty <;>
      by_cases emptyWitness : final.witness = [] <;>
      simp [emptySig, emptyWitness, inputStep_finalScriptSig,
        inputStep_finalWitness version _ final.witness count bounded,
        bind, Except.bind] at decoded
    all_goals
      repeat' (split at decoded <;> try simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure])
      all_goals subst_vars; cases final; simp_all [InputFields.finalInput]

end LeanMiniscript.Psbt
