import LeanMiniscript.Miniscript.Malleability

namespace LeanMiniscript.Miniscript

/-! ## Executable BIP 379 malleability inference -/

mutual
  /-- Infer malleability modifiers and retain the relational derivation. -/
  def inferMalleabilityTyped (ctx : ScriptContext) (fragment : CoreFragment) :
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
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx y with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩ =>
            some ⟨_, .and_v typedX typedY⟩
        | _, _ => none
    | .and_b x y =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx y with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩ =>
            some ⟨_, .and_b typedX typedY⟩
        | _, _ => none
    | .or_b x z =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_b typedX typedZ⟩
        | _, _ => none
    | .or_c x z =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_c typedX typedZ⟩
        | _, _ => none
    | .or_d x z =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_d typedX typedZ⟩
        | _, _ => none
    | .or_i x z =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .or_i typedX typedZ⟩
        | _, _ => none
    | .andor x y z =>
        match inferMalleabilityTyped ctx x, inferMalleabilityTyped ctx y,
            inferMalleabilityTyped ctx z with
        | some ⟨_mx, typedX⟩, some ⟨_my, typedY⟩, some ⟨_mz, typedZ⟩ =>
            some ⟨_, .andor typedX typedY typedZ⟩
        | _, _, _ => none
    | .a x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .a typed⟩
        | none => none
    | .s x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .s typed⟩
        | none => none
    | .c x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .c typed⟩
        | none => none
    | .d x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .d typed⟩
        | none => none
    | .v x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .v typed⟩
        | none => none
    | .j x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .j typed⟩
        | none => none
    | .n x =>
        match inferMalleabilityTyped ctx x with
        | some ⟨_mods, typed⟩ => some ⟨_, .n typed⟩
        | none => none
    | .thresh _k fragments =>
        match inferMalleabilityTypedList ctx fragments with
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
  def inferMalleabilityTypedList (ctx : ScriptContext)
      (fragments : List CoreFragment) :
      Option {mods : List MalleabilityModifiers //
        HasMalleabilityList ctx fragments mods} :=
    match fragments with
    | [] => some ⟨[], .nil⟩
    | fragment :: rest =>
        match inferMalleabilityTyped ctx fragment,
            inferMalleabilityTypedList ctx rest with
        | some ⟨mods, typed⟩, some ⟨restMods, restTyped⟩ =>
            some ⟨mods :: restMods, .cons typed restTyped⟩
        | _, _ => none
end

/-- Executable malleability inference with derivations erased. A successful
    analysis may return `nonMalleable := false`; `none` is reserved for a
    context-restricted constructor unavailable in `ctx`. -/
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
      exact typed.property

end LeanMiniscript.Miniscript
