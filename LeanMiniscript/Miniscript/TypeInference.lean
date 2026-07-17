import LeanMiniscript.Miniscript.Types

namespace LeanMiniscript.Miniscript

/-! ## Executable type inference

`inferTyped` constructs a typing derivation together with its inferred type.
Keeping the executable layer separate leaves `Types` focused on the relational
typing judgment.
-/

def branchBaseDecidable : (base : BaseType) → Decidable (branchBase base)
  | .B => isTrue trivial
  | .V => isTrue trivial
  | .K => isTrue trivial
  | .W => isFalse id

instance (base : BaseType) : Decidable (branchBase base) :=
  branchBaseDecidable base

def thresholdRestTypesDecidable :
    (types : List MiniType) → Decidable (thresholdRestTypes types)
  | [] => isTrue trivial
  | ty :: rest =>
      if base : ty.base = .W then
        if dissatisfiable : ty.mods.d = true then
          if unit : ty.mods.u = true then
            match thresholdRestTypesDecidable rest with
            | isTrue restOk => isTrue ⟨base, dissatisfiable, unit, restOk⟩
            | isFalse restBad => isFalse (fun typesOk => restBad typesOk.2.2.2)
          else isFalse (fun typesOk => unit typesOk.2.2.1)
        else isFalse (fun typesOk => dissatisfiable typesOk.2.1)
      else isFalse (fun typesOk => base typesOk.1)

instance (types : List MiniType) : Decidable (thresholdRestTypes types) :=
  thresholdRestTypesDecidable types

mutual
  /-- Infer a Miniscript type and construct the corresponding typing derivation. -/
  def inferTyped (fragment : CoreFragment) :
      Option {ty : MiniType // HasType fragment ty} :=
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
        match inferTyped x, inferTyped y with
        | some ⟨⟨.V, _modsX⟩, typedX⟩, some ⟨tyY, typedY⟩ =>
            if branch : branchBase tyY.base then
              some ⟨_, .and_v typedX typedY branch⟩
            else none
        | _, _ => none
    | .and_b x y =>
        match inferTyped x, inferTyped y with
        | some ⟨⟨.B, _modsX⟩, typedX⟩, some ⟨⟨.W, _modsY⟩, typedY⟩ =>
            some ⟨_, .and_b typedX typedY⟩
        | _, _ => none
    | .or_b x y =>
        match inferTyped x, inferTyped y with
        | some ⟨⟨.B, modsX⟩, typedX⟩, some ⟨⟨.W, modsY⟩, typedY⟩ =>
            if dx : modsX.d = true then
              if dy : modsY.d = true then some ⟨_, .or_b typedX dx typedY dy⟩
              else none
            else none
        | _, _ => none
    | .or_c x y =>
        match inferTyped x, inferTyped y with
        | some ⟨⟨.B, modsX⟩, typedX⟩, some ⟨⟨.V, _modsY⟩, typedY⟩ =>
            if dx : modsX.d = true then
              if ux : modsX.u = true then some ⟨_, .or_c typedX dx ux typedY⟩
              else none
            else none
        | _, _ => none
    | .or_d x y =>
        match inferTyped x, inferTyped y with
        | some ⟨⟨.B, modsX⟩, typedX⟩, some ⟨⟨.B, _modsY⟩, typedY⟩ =>
            if dx : modsX.d = true then
              if ux : modsX.u = true then some ⟨_, .or_d typedX dx ux typedY⟩
              else none
            else none
        | _, _ => none
    | .or_i x y =>
        match inferTyped x, inferTyped y with
        | some ⟨tyX, typedX⟩, some ⟨tyY, typedY⟩ =>
            if branch : branchBase tyX.base then
              if bases : tyX.base = tyY.base then
                some ⟨_, .or_i typedX typedY branch bases⟩
              else none
            else none
        | _, _ => none
    | .andor x y z =>
        match inferTyped x, inferTyped y, inferTyped z with
        | some ⟨⟨.B, modsX⟩, typedX⟩, some ⟨tyY, typedY⟩,
            some ⟨tyZ, typedZ⟩ =>
            if dx : modsX.d = true then
              if ux : modsX.u = true then
                if branch : branchBase tyY.base then
                  if bases : tyY.base = tyZ.base then
                    some ⟨_, .andor typedX dx ux typedY typedZ branch bases⟩
                  else none
                else none
              else none
            else none
        | _, _, _ => none
    | .c x =>
        match inferTyped x with
        | some ⟨⟨.K, _modsX⟩, typedX⟩ => some ⟨_, .c_wrap typedX⟩
        | _ => none
    | .v x =>
        match inferTyped x with
        | some ⟨⟨.B, _modsX⟩, typedX⟩ => some ⟨_, .v_wrap typedX⟩
        | _ => none
    | .a x =>
        match inferTyped x with
        | some ⟨⟨.B, _modsX⟩, typedX⟩ => some ⟨_, .a_wrap typedX⟩
        | _ => none
    | .s x =>
        match inferTyped x with
        | some ⟨⟨.B, modsX⟩, typedX⟩ =>
            if oneArg : modsX.o = true then some ⟨_, .s_wrap typedX oneArg⟩
            else none
        | _ => none
    | .d x =>
        match inferTyped x with
        | some ⟨⟨.V, modsX⟩, typedX⟩ =>
            if zeroArg : modsX.z = true then some ⟨_, .d_wrap typedX zeroArg⟩
            else none
        | _ => none
    | .j x =>
        match inferTyped x with
        | some ⟨⟨.B, modsX⟩, typedX⟩ =>
            if nonzero : modsX.n = true then some ⟨_, .j_wrap typedX nonzero⟩
            else none
        | _ => none
    | .n x =>
        match inferTyped x with
        | some ⟨⟨.B, _modsX⟩, typedX⟩ => some ⟨_, .n_wrap typedX⟩
        | _ => none
    | .thresh k fragments =>
        match fragments with
        | [] => none
        | x :: xs =>
            match inferTyped x, inferTypedList xs with
            | some ⟨⟨.B, modsX⟩, typedX⟩, some ⟨restTypes, typedRest⟩ =>
                if dx : modsX.d = true then
                  if ux : modsX.u = true then
                    if restOk : thresholdRestTypes restTypes then
                      if bounds : 1 ≤ k ∧ k ≤ (x :: xs).length then
                        some ⟨_, .thresh typedX dx ux typedRest restOk bounds.1 bounds.2⟩
                      else none
                    else none
                  else none
                else none
            | _, _ => none
    | .multi k keys =>
        if bounds : 1 ≤ k ∧ k ≤ keys.length then
          some ⟨_, .multi k keys bounds.1 bounds.2⟩
        else none
    | .multi_a k keys =>
        if bounds : 1 ≤ k ∧ k ≤ keys.length then
          some ⟨_, .multi_a k keys bounds.1 bounds.2⟩
        else none

  /-- Infer types for every fragment in a list, preserving order. -/
  def inferTypedList (fragments : List CoreFragment) :
      Option {types : List MiniType // HasTypeList fragments types} :=
    match fragments with
    | [] => some ⟨[], .nil⟩
    | fragment :: rest =>
        match inferTyped fragment, inferTypedList rest with
        | some ⟨ty, typed⟩, some ⟨types, restTyped⟩ =>
            some ⟨ty :: types, .cons typed restTyped⟩
        | _, _ => none
end

/-- Executable type inference with proof terms erased from the result. -/
def inferType (fragment : CoreFragment) : Option MiniType :=
  (inferTyped fragment).map Subtype.val

/-- Any type returned by `inferType` has a corresponding `HasType` derivation. -/
theorem inferType_sound {fragment : CoreFragment} {ty : MiniType}
    (inferred : inferType fragment = some ty) : HasType fragment ty := by
  unfold inferType at inferred
  cases typedEq : inferTyped fragment with
  | none => simp [typedEq] at inferred
  | some typed =>
      have valueEq : typed.val = ty := by
        simpa [typedEq] using inferred
      subst ty
      exact typed.property

end LeanMiniscript.Miniscript
