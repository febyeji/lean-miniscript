import LeanMiniscript.Psbt.Fields
import LeanMiniscript.Bitcoin.DeserializationProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-- Reading a final witness record recovers the serialized witness exactly. -/
theorem inputStep_finalWitness (version : Nat) (fields : InputFields)
    (witness : List ByteArray) (count : witness.length < 2 ^ 64)
    (bounded : ∀ item ∈ witness, item.size < 2 ^ 64) :
    inputStep version fields
      ⟨recordKey KeyType.inFinalScriptWitness, serializeWitness witness⟩ =
      .ok { fields with finalScriptWitness := some witness } := by
  simp only [inputStep, recordKey, splitKey, compactSize, liftDecode,
    Except.mapError, bind, Except.bind,
    pure, Except.pure, ByteArray.data_append, Array.toList_append]
  simp only [ByteArray.empty, noKeyData, checkKeyData, exactValue]
  rw [decodeAll_readWitnessStack witness count bounded]
  rfl

/-- On a successfully decoded map, its last final-witness record determines
that field, regardless of the preceding records. -/
theorem decodeInput_append_finalWitness {version : Nat} {map : KeyValueMap}
    {fields : InputFields} (witness : List ByteArray)
    (count : witness.length < 2 ^ 64)
    (bounded : ∀ item ∈ witness, item.size < 2 ^ 64)
    (decoded : decodeInput version
      (map ++ [⟨recordKey KeyType.inFinalScriptWitness, serializeWitness witness⟩]) =
      .ok fields) :
    fields.finalScriptWitness = some witness := by
  unfold decodeInput at decoded
  rw [List.foldlM_append] at decoded
  cases prior : map.foldlM (inputStep version) {} with
  | error error => simp [prior, bind, Except.bind] at decoded
  | ok previous =>
      simp only [prior, bind, Except.bind, List.foldlM_cons,
        inputStep_finalWitness version previous witness count bounded,
        List.foldlM_nil, pure, Except.pure] at decoded
      split at decoded
      · split at decoded
        · simp [throw, throwThe, MonadExceptOf.throw] at decoded
        · split at decoded
          · simp [throw, throwThe, MonadExceptOf.throw] at decoded
          · cases decoded; rfl
      · cases decoded; rfl

/-- Successful monadic mapping preserves each indexed source/result pair. -/
theorem getElem?_of_mapM_ok {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (mapped : xs.mapM f = .ok ys)
    {index : Nat} {x : α} (found : xs[index]? = some x) :
    ∃ y, ys[index]? = some y ∧ f x = .ok y := by
  induction xs generalizing ys index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.mapM_cons, bind, Except.bind] at mapped
      cases first : f head with
      | error error => simp [first] at mapped
      | ok value =>
          simp only [first] at mapped
          cases rest : tail.mapM f with
          | error error => simp [rest] at mapped
          | ok values =>
              simp only [rest, pure, Except.pure, Except.ok.injEq] at mapped
              subst ys
              cases index with
              | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                        subst x; exact ⟨value, rfl, first⟩
              | succ index => exact ih rest found

/-- Each typed input returned by whole-PSBT decoding is read from the
corresponding input map with the decoded global version. -/
theorem Psbt.decode_input {psbt : Psbt} {decoded : DecodedPsbt}
    (decodes : psbt.decode = .ok decoded) {index : Nat} {map : KeyValueMap}
    (found : psbt.inputs[index]? = some map) :
    ∃ input, decoded.inputs[index]? = some input ∧
      decodeInput decoded.global.psbtVersion map = .ok input := by
  unfold Psbt.decode at decodes
  cases hg : decodeGlobal psbt.global with
  | error error => simp [hg, bind, Except.bind] at decodes
  | ok global =>
      simp only [hg, bind, Except.bind] at decodes
      split at decodes
      · simp [throw, throwThe, MonadExceptOf.throw] at decodes
      · cases hi : psbt.inputs.mapM (decodeInput global.psbtVersion) with
        | error error => simp [hi] at decodes
        | ok inputs =>
            simp only [hi] at decodes
            cases ho : psbt.outputs.mapM (decodeOutput global.psbtVersion) with
            | error error => simp [ho] at decodes
            | ok outputs =>
                simp only [ho, pure, Except.pure, Except.ok.injEq] at decodes
                subst decoded
                exact getElem?_of_mapM_ok hi found

end LeanMiniscript.Psbt
