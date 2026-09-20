import LeanMiniscript.Miniscript.Malleability

namespace LeanMiniscript.Miniscript

/-! ## Executable BIP 379 malleability inference -/

mutual
  /-- Infer the local malleability rules and retain their derivation. This
      recursive worker does not check global key uniqueness; callers should use
      `inferMalleabilityTyped` or `inferMalleability` for checked analysis. -/
  def inferMalleabilityRulesTyped (ctx : ScriptContext) (fragment : CoreFragment) :
      Option {mods : MalleabilityModifiers // HasMalleability ctx fragment mods} :=
    match fragment with
    | .zero => some ⟨_, .zero⟩
    | .one => some ⟨_, .one⟩
    | .pk_k key => some ⟨_, .pk_k key⟩
    | .pk_h key => some ⟨_, .pk_h key⟩
    | .older n => some ⟨_, .older n⟩
    | .after n => some ⟨_, .after n⟩
    | .sha256 hash => some ⟨_, .sha256 hash⟩
    | .hash256 hash => some ⟨_, .hash256 hash⟩
    | .ripemd160 hash => some ⟨_, .ripemd160 hash⟩
    | .hash160 hash => some ⟨_, .hash160 hash⟩
    | .and_v x y =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx y with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩ =>
            some ⟨_, .and_v typedX typedY⟩
        | _, _ => none
    | .and_b x y =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx y with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩ =>
            some ⟨_, .and_b typedX typedY⟩
        | _, _ => none
    | .or_b x z =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_b typedX typedZ⟩
        | _, _ => none
    | .or_c x z =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_c typedX typedZ⟩
        | _, _ => none
    | .or_d x z =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_d typedX typedZ⟩
        | _, _ => none
    | .or_i x z =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_i typedX typedZ⟩
        | _, _ => none
    | .andor x y z =>
        match inferMalleabilityRulesTyped ctx x, inferMalleabilityRulesTyped ctx y,
            inferMalleabilityRulesTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .andor typedX typedY typedZ⟩
        | _, _, _ => none
    | .a x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .a typed⟩
        | none => none
    | .s x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .s typed⟩
        | none => none
    | .c x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .c typed⟩
        | none => none
    | .d x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .d typed⟩
        | none => none
    | .v x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .v typed⟩
        | none => none
    | .j x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .j typed⟩
        | none => none
    | .n x =>
        match inferMalleabilityRulesTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .n typed⟩
        | none => none
    | .thresh _k fragments =>
        match inferMalleabilityRulesTypedList ctx fragments with
        | some ⟨_mods, typed⟩ => some ⟨_, .thresh typed⟩
        | none => none
    | .multi k keys =>
        match ctx with
        | .p2wsh => some ⟨_, .multi k keys trivial⟩
        | .tapscript => none
    | .multi_a k keys =>
        match ctx with
        | .p2wsh => none
        | .tapscript => some ⟨_, .multi_a k keys trivial⟩

  /-- Infer pointwise malleability modifiers for threshold children. -/
  def inferMalleabilityRulesTypedList (ctx : ScriptContext)
      (fragments : List CoreFragment) :
      Option {mods : List MalleabilityModifiers //
        HasMalleabilityList ctx fragments mods} :=
    match fragments with
    | [] => some ⟨[], .nil⟩
    | fragment :: rest =>
        match inferMalleabilityRulesTyped ctx fragment,
            inferMalleabilityRulesTypedList ctx rest with
        | some ⟨mods, typed⟩, some ⟨restMods, restTyped⟩ =>
            some ⟨mods :: restMods, .cons typed restTyped⟩
        | _, _ => none
end

/-- Infer malleability modifiers together with both the local rule derivation
    and the global BIP 379 no-duplicate-keys evidence. -/
def inferMalleabilityTyped (ctx : ScriptContext) (fragment : CoreFragment) :
    Option {mods : MalleabilityModifiers //
      HasMalleability ctx fragment mods ∧ fragment.NoDuplicateKeys} :=
  if unique : fragment.NoDuplicateKeys then
    match inferMalleabilityRulesTyped ctx fragment with
    | some ⟨mods, typed⟩ => some ⟨mods, typed, unique⟩
    | none => none
  else
    none

/-- Executable malleability inference with derivations erased. A successful
    analysis may return `nonMalleable := false`. Repeated public keys violate
    the BIP 379 analysis assumption and return `none`, as do constructors that
    are unavailable in `ctx`. -/
def inferMalleability (ctx : ScriptContext) (fragment : CoreFragment) :
    Option MalleabilityModifiers :=
  (inferMalleabilityTyped ctx fragment).map Subtype.val

/-- Every modifier set returned by inference has a relational derivation. -/
theorem inferMalleability_sound {ctx : ScriptContext} {fragment : CoreFragment}
    {mods : MalleabilityModifiers}
    (inferred : inferMalleability ctx fragment = some mods) :
    HasMalleability ctx fragment mods := by
  unfold inferMalleability at inferred
  cases typedEq : inferMalleabilityTyped ctx fragment with
  | none => simp [typedEq] at inferred
  | some typed =>
      have valueEq : typed.val = mods := by
        simpa [typedEq] using inferred
      subst mods
      exact typed.property.1

/-- Successful public malleability inference establishes the BIP 379
    no-duplicate-keys assumption. -/
theorem inferMalleability_noDuplicateKeys {ctx : ScriptContext}
    {fragment : CoreFragment} {mods : MalleabilityModifiers}
    (inferred : inferMalleability ctx fragment = some mods) :
    fragment.NoDuplicateKeys := by
  unfold inferMalleability at inferred
  cases typedEq : inferMalleabilityTyped ctx fragment with
  | none => simp [typedEq] at inferred
  | some typed => exact typed.property.2

end LeanMiniscript.Miniscript
