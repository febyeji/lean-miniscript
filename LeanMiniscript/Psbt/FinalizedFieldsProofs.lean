import LeanMiniscript.Psbt.ExtractionProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-- The scriptSig and witness defaults used by the transaction extractor. -/
def InputFields.finalInput (input : InputFields) : FinalInput :=
  ⟨input.finalScriptSig.getD ByteArray.empty, input.finalScriptWitness.getD []⟩

private theorem inputStep_kept_finals {version : Nat} {before after : InputFields}
    {record : Record} (kept : keepAfterFinalize record = true)
    (read : inputStep version before record = .ok after) :
    after.finalScriptSig = before.finalScriptSig ∧
      after.finalScriptWitness = before.finalScriptWitness := by
  cases hk : splitKey record.key with
  | error error => simp [inputStep, hk, bind, Except.bind] at read
  | ok pair =>
    rcases pair with ⟨keyType, keyData⟩
    by_cases known : keyType ∈ knownInputKeyTypes
    · simp [knownInputKeyTypes] at known
      rcases known with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h
      all_goals subst keyType
      all_goals simp [keepAfterFinalize, Record.keyType?, hk, knownInputKeyTypes] at kept
      all_goals simp only [inputStep, hk, bind, Except.bind, KeyType.inNonWitnessUtxo,
        KeyType.inWitnessUtxo, KeyType.inPartialSig, KeyType.inSighashType, KeyType.inRedeemScript,
        KeyType.inWitnessScript, KeyType.inBip32Derivation, KeyType.inFinalScriptSig,
        KeyType.inFinalScriptWitness, KeyType.inRipemd160, KeyType.inSha256, KeyType.inHash160,
        KeyType.inHash256, KeyType.inPreviousTxid, KeyType.inOutputIndex, KeyType.inSequence,
        KeyType.inRequiredTimeLocktime, KeyType.inRequiredHeightLocktime, KeyType.inTapKeySig,
        KeyType.inTapScriptSig, KeyType.inTapLeafScript, KeyType.inTapBip32Derivation,
        KeyType.inTapInternalKey, KeyType.inTapMerkleRoot, Nat.reduceBEq,
        if_true, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at read
      all_goals
        repeat' (split at read <;> try simp_all)
        all_goals subst after; exact ⟨rfl, rfl⟩
    · simp [knownInputKeyTypes] at known
      simp only [inputStep, hk, bind, Except.bind, KeyType.inNonWitnessUtxo, KeyType.inWitnessUtxo,
        KeyType.inPartialSig, KeyType.inSighashType, KeyType.inRedeemScript,
        KeyType.inWitnessScript, KeyType.inBip32Derivation, KeyType.inFinalScriptSig,
        KeyType.inFinalScriptWitness, KeyType.inRipemd160, KeyType.inSha256, KeyType.inHash160,
        KeyType.inHash256, KeyType.inPreviousTxid, KeyType.inOutputIndex, KeyType.inSequence,
        KeyType.inRequiredTimeLocktime, KeyType.inRequiredHeightLocktime, KeyType.inTapKeySig,
        KeyType.inTapScriptSig, KeyType.inTapLeafScript, KeyType.inTapBip32Derivation,
        KeyType.inTapInternalKey, KeyType.inTapMerkleRoot] at read
      simp only [beq_iff_eq] at read
      simp_all only [if_false]
      repeat' (split at read <;> try simp_all [pure, Except.pure])
      all_goals subst after; exact ⟨rfl, rfl⟩

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
      obtain ⟨sig, witness⟩ := inputStep_kept_finals (kept record (by simp)) first
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
