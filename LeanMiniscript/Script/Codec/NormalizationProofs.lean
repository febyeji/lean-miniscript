import LeanMiniscript.Script.Codec.Proofs
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
Normalization preserves the bytes pushed by each instruction, conditional
structure, and canonical serialization, including serialization errors.
-/

private theorem normalizeSerializedData_cases (data : ByteArray) :
    normalizeSerializedData data = .pushData data ∨
      ∃ value, normalizeSerializedData data = .pushNum value ∧ scriptNum value = data := by
  unfold normalizeSerializedData
  split
  next empty =>
    right
    refine ⟨0, rfl, ?_⟩
    apply ByteArray.ext
    exact (Array.eq_empty_of_size_eq_zero empty).symm
  next nonempty =>
    split
    next oneByte =>
      have singleton : data = ⟨#[data.get! 0]⟩ := by
        apply ByteArray.ext
        apply Array.ext
        · simpa using oneByte
        · intro index leftBound rightBound
          have indexEq : index = 0 := by
            have : index < 1 := by simpa using rightBound
            omega
          subst index
          simp [ByteArray.get!, oneByte]
      dsimp only
      split
      next small =>
        right
        refine ⟨(data.get! 0).toNat, rfl, ?_⟩
        have encoding : ∀ n : Fin 17, 1 ≤ n.val →
            scriptNum (n.val : Int) = ⟨#[UInt8.ofNat n.val]⟩ := by decide
        rw [encoding ⟨(data.get! 0).toNat, by omega⟩ small.1]
        simpa using singleton.symm
      next notSmall =>
        split
        next negativeOne =>
          right
          refine ⟨-1, rfl, ?_⟩
          rw [singleton, negativeOne]
          rfl
        next ordinary => exact Or.inl rfl
    next ordinary => exact Or.inl rfl

/-- Any observation identifying numeric pushes with their actual bytes is
    invariant under data-push normalization. -/
theorem normalizeSerializedData_preserves {α : Type} (observe : ScriptElement → α)
    (push : ∀ value, observe (.pushNum value) = observe (.pushData (scriptNum value)))
    (data : ByteArray) :
    observe (normalizeSerializedData data) = observe (.pushData data) := by
  rcases normalizeSerializedData_cases data with unchanged | ⟨value, normalized, bytes⟩
  · rw [unchanged]
  · rw [normalized, push, bytes]

/-- Numeric annotations and canonical push opcodes denote the same bytes. -/
theorem normalizeSerializedElement_preserves {α : Type} (observe : ScriptElement → α)
    (push : ∀ value, observe (.pushNum value) = observe (.pushData (scriptNum value)))
    (element : ScriptElement) :
    observe (normalizeSerializedElement element) = observe element := by
  cases element with
  | op opcode => rfl
  | pushData data => exact normalizeSerializedData_preserves observe push data
  | pushNum value =>
      simp only [normalizeSerializedElement]
      split
      · rfl
      · rw [normalizeSerializedData_preserves observe push, ← push]

theorem normalizeSerializedElement_control (element : ScriptElement) :
    normalizeSerializedElement element = element ∨
      (NonConditional element ∧ NonConditional (normalizeSerializedElement element)) := by
  cases element with
  | op opcode => exact Or.inl rfl
  | pushData data =>
      right
      refine ⟨trivial, ?_⟩
      rcases normalizeSerializedData_cases data with unchanged | ⟨value, normalized, _⟩
      · simp [normalizeSerializedElement, unchanged, NonConditional]
      · simp [normalizeSerializedElement, normalized, NonConditional]
  | pushNum value =>
      right
      refine ⟨trivial, ?_⟩
      simp only [normalizeSerializedElement]
      split
      · trivial
      · rcases normalizeSerializedData_cases (scriptNum value) with
          unchanged | ⟨number, normalized, _⟩
        · simp [unchanged, NonConditional]
        · simp [normalized, NonConditional]

theorem splitConditional_normalizeSerializedScript (script : Script) :
    splitConditional (normalizeSerializedScript script) =
      (splitConditional script).map (ConditionalFrame.map normalizeSerializedElement) :=
  splitConditional_map _ normalizeSerializedElement_control script

theorem selectUnclosedConditional_normalizeSerializedScript
    (script : Script) (selected : Bool) :
    selectUnclosedConditional (normalizeSerializedScript script) selected =
      normalizeSerializedScript (selectUnclosedConditional script selected) :=
  selectUnclosedConditional_map _ normalizeSerializedElement_control script selected

theorem serializePushNum_eq_serializePushData (value : Int) :
    serializePushNum value = serializePushData (scriptNum value) := by
  unfold serializePushNum
  split
  next zero => subst value; rfl
  next nonzero =>
    split
    next negativeOne => subst value; rfl
    next notNegativeOne =>
      split
      next small =>
        have values : value = 1 ∨ value = 2 ∨ value = 3 ∨ value = 4 ∨
            value = 5 ∨ value = 6 ∨ value = 7 ∨ value = 8 ∨
            value = 9 ∨ value = 10 ∨ value = 11 ∨ value = 12 ∨
            value = 13 ∨ value = 14 ∨ value = 15 ∨ value = 16 := by omega
        rcases values with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          subst value <;> rfl
      next ordinary => rfl

theorem serializeElement_normalizeSerializedElement (element : ScriptElement) :
    serializeElement (normalizeSerializedElement element) = serializeElement element := by
  apply normalizeSerializedElement_preserves
  exact serializePushNum_eq_serializePushData

/-- Normalization preserves canonical bytes and any push-length serialization
    error. Tapscript can therefore bind either AST to the same witness bytes. -/
theorem serializeScript_normalizeSerializedScript (script : Script) :
    serializeScript (normalizeSerializedScript script) = serializeScript script := by
  induction script with
  | nil => rfl
  | cons element rest ih =>
      simp only [normalizeSerializedScript, List.map_cons, serializeScript,
        serializeElement_normalizeSerializedElement] at *
      rw [ih]

end LeanMiniscript.Script
