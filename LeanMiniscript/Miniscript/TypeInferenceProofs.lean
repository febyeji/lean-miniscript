import LeanMiniscript.Miniscript.TypeInference

namespace LeanMiniscript.Miniscript

/-!
# Executable type-inference guarantees

Completeness and determinism proofs are separate from `Types` so callers that
only execute `inferType` do not import this proof module.
-/

mutual
  /-- Every relational typing derivation is reproduced by executable inference. -/
  theorem inferTyped_complete {fragment : CoreFragment} {ty : MiniType}
      (typed : HasType fragment ty) :
      inferTyped fragment = some ⟨ty, typed⟩ := by
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
    | and_v typedX typedY branch =>
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, branch]
    | and_b typedX typedY =>
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY]
    | or_b typedX dx typedY dy =>
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, dx, dy]
    | or_c typedX dx ux typedY =>
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, dx, ux]
    | or_d typedX dx ux typedY =>
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, dx, ux]
    | @or_i X Y tyX tyY typedX typedY branch bases =>
        have branchY : branchBase tyY.base := by simpa [← bases] using branch
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, branchY, bases]
    | @andor X Y Z modsX tyY tyZ typedX dx ux typedY typedZ branch bases =>
        have branchZ : branchBase tyZ.base := by simpa [← bases] using branch
        simp [inferTyped, inferTyped_complete typedX,
          inferTyped_complete typedY, inferTyped_complete typedZ,
          dx, ux, branchZ, bases]
    | c_wrap typedX =>
        simp [inferTyped, inferTyped_complete typedX]
    | v_wrap typedX =>
        simp [inferTyped, inferTyped_complete typedX]
    | a_wrap typedX =>
        simp [inferTyped, inferTyped_complete typedX]
    | s_wrap typedX oneArg =>
        simp [inferTyped, inferTyped_complete typedX, oneArg]
    | d_wrap typedX zeroArg =>
        simp [inferTyped, inferTyped_complete typedX, zeroArg]
    | j_wrap typedX nonzero =>
        simp [inferTyped, inferTyped_complete typedX, nonzero]
    | n_wrap typedX =>
        simp [inferTyped, inferTyped_complete typedX]
    | @thresh k X Xs modsX restTypes typedX dx ux typedRest restOk lower upper =>
        have upper' : k ≤ Xs.length + 1 := by simpa using upper
        simp [inferTyped, inferTyped_complete typedX,
          inferTypedList_complete typedRest, dx, ux, restOk, lower, upper']
    | multi k keys lower upper =>
        simp [inferTyped, lower, upper]
    | multi_a k keys lower upper =>
        simp [inferTyped, lower, upper]

  /-- List typing derivations are reproduced pointwise by executable inference. -/
  theorem inferTypedList_complete {fragments : List CoreFragment}
      {types : List MiniType} (typed : HasTypeList fragments types) :
      inferTypedList fragments = some ⟨types, typed⟩ := by
    cases typed with
    | nil => rfl
    | cons typedHead typedRest =>
        simp [inferTypedList, inferTyped_complete typedHead,
          inferTypedList_complete typedRest]
end

/-- Relational typing and executable inference agree. -/
theorem inferType_complete {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType fragment ty) : inferType fragment = some ty := by
  simp [inferType, inferTyped_complete typed]

/-- Miniscript typing is deterministic. -/
theorem HasType.unique {fragment : CoreFragment} {left right : MiniType}
    (leftTyped : HasType fragment left) (rightTyped : HasType fragment right) :
    left = right := by
  have leftInferred := inferType_complete leftTyped
  have rightInferred := inferType_complete rightTyped
  rw [leftInferred] at rightInferred
  exact Option.some.inj rightInferred

/-- A fragment is well-typed exactly when executable inference succeeds. -/
theorem wellTyped_iff_inferType_isSome (fragment : CoreFragment) :
    wellTyped fragment ↔ (inferType fragment).isSome = true := by
  constructor
  · rintro ⟨ty, typed⟩
    simp [inferType_complete typed]
  · intro inferred
    cases typeEq : inferType fragment with
    | none => simp [typeEq] at inferred
    | some ty => exact ⟨ty, inferType_sound typeEq⟩

end LeanMiniscript.Miniscript
