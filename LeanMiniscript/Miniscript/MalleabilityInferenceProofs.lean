import LeanMiniscript.Miniscript.MalleabilityInference

namespace LeanMiniscript.Miniscript

/-! ## Completeness, uniqueness, and reflection for malleability inference -/

mutual
  /-- Executable inference reproduces every relational malleability derivation. -/
  theorem inferMalleabilityRulesTyped_complete {ctx : ScriptContext}
      {fragment : CoreFragment} {mods : MalleabilityModifiers}
      (typed : HasMalleability ctx fragment mods) :
      inferMalleabilityRulesTyped ctx fragment = some ⟨mods, typed⟩ := by
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
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedY]
    | and_b typedX typedY =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedY]
    | or_b typedX typedZ =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedZ]
    | or_c typedX typedZ =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedZ]
    | or_d typedX typedZ =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedZ]
    | or_i typedX typedZ =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedZ]
    | andor typedX typedY typedZ =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTyped_complete typedX,
          inferMalleabilityRulesTyped_complete typedY,
          inferMalleabilityRulesTyped_complete typedZ]
    | a typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | s typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | c typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | d typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | v typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | j typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | n typed =>
        simp [inferMalleabilityRulesTyped, inferMalleabilityRulesTyped_complete typed]
    | thresh typed =>
        simp [inferMalleabilityRulesTyped,
          inferMalleabilityRulesTypedList_complete typed]
    | multi k keys allowed =>
        cases ctx with
        | p2wsh => rfl
        | tapscript => simp [ScriptContext.permitsLegacyMulti] at allowed
    | multi_a k keys allowed =>
        cases ctx with
        | p2wsh => simp [ScriptContext.permitsCheckSigAddMulti] at allowed
        | tapscript => rfl

  /-- List inference reproduces every pointwise relational derivation. -/
  theorem inferMalleabilityRulesTypedList_complete {ctx : ScriptContext}
      {fragments : List CoreFragment} {mods : List MalleabilityModifiers}
      (typed : HasMalleabilityList ctx fragments mods) :
      inferMalleabilityRulesTypedList ctx fragments = some ⟨mods, typed⟩ := by
    cases typed with
    | nil => rfl
    | cons typedHead typedRest =>
        simp [inferMalleabilityRulesTypedList,
          inferMalleabilityRulesTyped_complete typedHead,
          inferMalleabilityRulesTypedList_complete typedRest]
end

/-- Checked typed inference is complete when the global key-uniqueness premise
    and the local malleability derivation both hold. -/
theorem inferMalleabilityTyped_complete {ctx : ScriptContext}
    {fragment : CoreFragment} {mods : MalleabilityModifiers}
    (unique : fragment.NoDuplicateKeys)
    (typed : HasMalleability ctx fragment mods) :
    inferMalleabilityTyped ctx fragment = some ⟨mods, typed, unique⟩ := by
  simp [inferMalleabilityTyped, unique,
    inferMalleabilityRulesTyped_complete typed]

/-- Relational malleability typing is complete for executable inference. -/
theorem inferMalleability_complete {ctx : ScriptContext}
    {fragment : CoreFragment} {mods : MalleabilityModifiers}
    (unique : fragment.NoDuplicateKeys)
    (typed : HasMalleability ctx fragment mods) :
    inferMalleability ctx fragment = some mods := by
  simp [inferMalleability, inferMalleabilityTyped_complete unique typed]

/-- Malleability typing is deterministic in a fixed script context. -/
theorem HasMalleability.unique {ctx : ScriptContext} {fragment : CoreFragment}
    {left right : MalleabilityModifiers}
    (leftTyped : HasMalleability ctx fragment left)
    (rightTyped : HasMalleability ctx fragment right) :
    left = right := by
  have leftInferred := inferMalleabilityRulesTyped_complete leftTyped
  have rightInferred := inferMalleabilityRulesTyped_complete rightTyped
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
