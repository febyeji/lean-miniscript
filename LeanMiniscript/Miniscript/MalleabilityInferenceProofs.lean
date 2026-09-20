import LeanMiniscript.Miniscript.MalleabilityInference

namespace LeanMiniscript.Miniscript

/-! ## Completeness, uniqueness, and reflection for malleability inference -/

mutual
  /-- Executable inference reproduces every relational malleability derivation. -/
  theorem inferMalleabilityTyped_complete {ctx : ScriptContext}
      {fragment : CoreFragment} {mods : MalleabilityModifiers}
      (typed : HasMalleability ctx fragment mods) :
      inferMalleabilityTyped ctx fragment = some ⟨mods, typed⟩ := by
    cases typed with
    | zero => rfl
    | one => rfl
    | pk_k => rfl
    | pk_h => rfl
    | older => rfl
    | after => rfl
    | sha256 => rfl
    | hash256 => rfl
    | ripemd160 => rfl
    | hash160 => rfl
    | and_v typedX typedY =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedY]
    | and_b typedX typedY =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedY]
    | or_b typedX typedZ =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedZ]
    | or_c typedX typedZ =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedZ]
    | or_d typedX typedZ =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedZ]
    | or_i typedX typedZ =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedZ]
    | andor typedX typedY typedZ =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTyped_complete typedX,
          inferMalleabilityTyped_complete typedY,
          inferMalleabilityTyped_complete typedZ]
    | a typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | s typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | c typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | d typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | v typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | j typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | n typed =>
        simp [inferMalleabilityTyped, inferMalleabilityTyped_complete typed]
    | thresh typed =>
        simp [inferMalleabilityTyped,
          inferMalleabilityTypedList_complete typed]
    | multi k keys allowed =>
        cases ctx with
        | p2wsh => rfl
        | tapscript => simp [ScriptContext.permitsLegacyMulti] at allowed
    | multi_a k keys allowed =>
        cases ctx with
        | p2wsh => simp [ScriptContext.permitsCheckSigAddMulti] at allowed
        | tapscript => rfl

  /-- List inference reproduces every pointwise relational derivation. -/
  theorem inferMalleabilityTypedList_complete {ctx : ScriptContext}
      {fragments : List CoreFragment} {mods : List MalleabilityModifiers}
      (typed : HasMalleabilityList ctx fragments mods) :
      inferMalleabilityTypedList ctx fragments = some ⟨mods, typed⟩ := by
    cases typed with
    | nil => rfl
    | cons typedHead typedRest =>
        simp [inferMalleabilityTypedList,
          inferMalleabilityTyped_complete typedHead,
          inferMalleabilityTypedList_complete typedRest]
end

/-- Relational malleability typing is complete for executable inference. -/
theorem inferMalleability_complete {ctx : ScriptContext}
    {fragment : CoreFragment} {mods : MalleabilityModifiers}
    (unique : fragment.NoDuplicateKeys)
    (typed : HasMalleability ctx fragment mods) :
    inferMalleability ctx fragment = some mods := by
  simp [inferMalleability, unique, inferMalleabilityTyped_complete typed]

/-- Malleability typing is deterministic in a fixed script context. -/
theorem HasMalleability.unique {ctx : ScriptContext} {fragment : CoreFragment}
    {left right : MalleabilityModifiers}
    (leftTyped : HasMalleability ctx fragment left)
    (rightTyped : HasMalleability ctx fragment right) :
    left = right := by
  have leftInferred := inferMalleabilityTyped_complete leftTyped
  have rightInferred := inferMalleabilityTyped_complete rightTyped
  rw [leftInferred] at rightInferred
  exact congrArg Subtype.val (Option.some.inj rightInferred)

/-- Public inference returns exactly the locally admitted modifier sets whose
    fragments also satisfy the global no-duplicate-keys assumption. -/
theorem hasMalleability_iff_inferMalleability_eq {ctx : ScriptContext}
    {fragment : CoreFragment} {mods : MalleabilityModifiers} :
    HasMalleability ctx fragment mods ∧ fragment.NoDuplicateKeys ↔
      inferMalleability ctx fragment = some mods := by
  constructor
  · rintro ⟨typed, unique⟩
    exact inferMalleability_complete unique typed
  · intro inferred
    exact ⟨inferMalleability_sound inferred,
      inferMalleability_noDuplicateKeys inferred⟩

/-- A fragment is analyzable exactly when executable inference succeeds. -/
theorem malleabilityAnalyzable_iff_inferMalleability_isSome
    (ctx : ScriptContext) (fragment : CoreFragment) :
    malleabilityAnalyzable ctx fragment ↔
      (inferMalleability ctx fragment).isSome = true := by
  constructor
  · rintro ⟨unique, mods, typed⟩
    simp [inferMalleability_complete unique typed]
  · intro inferred
    cases modsEq : inferMalleability ctx fragment with
    | none => simp [modsEq] at inferred
    | some mods => exact ⟨inferMalleability_noDuplicateKeys modsEq,
        mods, inferMalleability_sound modsEq⟩

end LeanMiniscript.Miniscript
