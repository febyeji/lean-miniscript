import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Properties.ResourceBounds

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-! # Compiler-independent static resource metrics -/

/-- Projection that retains exact opcodes and erases every pushed value. -/
private def opcodeProjection : ScriptElement → Option Opcode
  | .op opcode => some opcode
  | .pushData _ | .pushNum _ => none

private def scriptOpcodeProjection (script : Script) : List (Option Opcode) :=
  script.map opcodeProjection

private def verifyProjectionReplacement? :
    Option Opcode → Option (Option Opcode)
  | some .OP_EQUAL => some (some .OP_EQUALVERIFY)
  | some .OP_CHECKSIG => some (some .OP_CHECKSIGVERIFY)
  | some .OP_CHECKMULTISIG => some (some .OP_CHECKMULTISIGVERIFY)
  | some .OP_NUMEQUAL => some (some .OP_NUMEQUALVERIFY)
  | _ => none

private def compileVerifyProjection
    (projection : List (Option Opcode)) : List (Option Opcode) :=
  match projection.reverse with
  | [] => [some .OP_VERIFY]
  | last :: reversedPrefix =>
      match verifyProjectionReplacement? last with
      | some replacement => (replacement :: reversedPrefix).reverse
      | none => (some .OP_VERIFY :: last :: reversedPrefix).reverse

private theorem compileVerify_opcodeProjection (script : Script) :
    scriptOpcodeProjection (compileVerify script) =
      compileVerifyProjection (scriptOpcodeProjection script) := by
  simp only [scriptOpcodeProjection, compileVerify, compileVerifyProjection]
  generalize reversedEq : script.reverse = reversed
  have mappedReverse :
      (List.map opcodeProjection script).reverse =
        List.map opcodeProjection reversed := by
    rw [← List.map_reverse, reversedEq]
  rw [mappedReverse]
  cases reversed with
  | nil => simp [opcodeProjection]
  | cons last reversedPrefix =>
      cases last with
      | op opcode => cases opcode <;>
          simp [opcodeProjection, verifyReplacement?,
            verifyProjectionReplacement?, List.map_reverse]
      | pushData data =>
          simp [opcodeProjection, verifyReplacement?,
            verifyProjectionReplacement?, List.map_reverse]
      | pushNum value =>
          simp [opcodeProjection, verifyReplacement?,
            verifyProjectionReplacement?, List.map_reverse]

mutual
  private theorem compileWithKeyHash_opcodeProjection_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (fragment : CoreFragment) :
      scriptOpcodeProjection (compileWithKeyHash leftKeyHash fragment) =
        scriptOpcodeProjection (compileWithKeyHash rightKeyHash fragment) := by
    cases fragment with
    | zero | one | pk_k | pk_h | older | after | sha256 | hash256 |
        ripemd160 | hash160 | multi | multi_a => rfl
    | and_v x y | and_b x y | or_b x y | or_c x y | or_d x y | or_i x y =>
        have xEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash x
        have yEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash y
        unfold scriptOpcodeProjection at xEq yEq
        simp only [compileWithKeyHash, scriptOpcodeProjection, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq, yEq]
    | andor x y z =>
        have xEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash x
        have yEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash y
        have zEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash z
        unfold scriptOpcodeProjection at xEq yEq zEq
        simp only [compileWithKeyHash, scriptOpcodeProjection, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq, yEq, zEq]
    | a x | s x | c x | d x | j x | n x =>
        have xEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash x
        unfold scriptOpcodeProjection at xEq
        simp only [compileWithKeyHash, scriptOpcodeProjection, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq]
    | v x =>
        simp only [compileWithKeyHash]
        rw [compileVerify_opcodeProjection, compileVerify_opcodeProjection,
          compileWithKeyHash_opcodeProjection_eq leftKeyHash rightKeyHash x]
    | thresh threshold fragments =>
        have fragmentsEq := compileThreshWithKeyHash_opcodeProjection_eq
          leftKeyHash rightKeyHash fragments
        unfold scriptOpcodeProjection at fragmentsEq
        simp only [compileWithKeyHash, scriptOpcodeProjection, List.map_append,
          List.map_cons, List.map_nil]
        rw [fragmentsEq]

  private theorem compileThreshWithKeyHash_opcodeProjection_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (fragments : List CoreFragment) :
      scriptOpcodeProjection
          (compileThreshWithKeyHash leftKeyHash fragments) =
        scriptOpcodeProjection
          (compileThreshWithKeyHash rightKeyHash fragments) := by
    cases fragments with
    | nil => rfl
    | cons fragment fragments =>
        have fragmentEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash fragment
        have fragmentsEq := compileThreshTailWithKeyHash_opcodeProjection_eq
          leftKeyHash rightKeyHash fragments
        unfold scriptOpcodeProjection at fragmentEq fragmentsEq
        simp only [compileThreshWithKeyHash, scriptOpcodeProjection,
          List.map_append]
        rw [fragmentEq, fragmentsEq]

  private theorem compileThreshTailWithKeyHash_opcodeProjection_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (fragments : List CoreFragment) :
      scriptOpcodeProjection
          (compileThreshTailWithKeyHash leftKeyHash fragments) =
        scriptOpcodeProjection
          (compileThreshTailWithKeyHash rightKeyHash fragments) := by
    cases fragments with
    | nil => rfl
    | cons fragment fragments =>
        have fragmentEq := compileWithKeyHash_opcodeProjection_eq leftKeyHash
          rightKeyHash fragment
        have fragmentsEq := compileThreshTailWithKeyHash_opcodeProjection_eq
          leftKeyHash rightKeyHash fragments
        unfold scriptOpcodeProjection at fragmentEq fragmentsEq
        simp only [compileThreshTailWithKeyHash, scriptOpcodeProjection,
          List.map_append, List.map_cons, List.map_nil]
        rw [fragmentEq, fragmentsEq]
end

private theorem isNonPushElement_eq_projection (element : ScriptElement) :
    isNonPushElement element = (opcodeProjection element).isSome := by
  cases element <;> rfl

private theorem fold_nonPush_projection
    (script : Script) (initial : Nat) :
    script.foldl
        (fun count element =>
          if isNonPushElement element then count + 1 else count)
        initial =
      (scriptOpcodeProjection script).foldl
        (fun count projection => if projection.isSome then count + 1 else count)
        initial := by
  induction script generalizing initial with
  | nil => rfl
  | cons element script ih =>
      simp only [List.foldl_cons, scriptOpcodeProjection, List.map_cons]
      rw [← isNonPushElement_eq_projection element]
      exact ih _

private theorem nonPushOpCount_eq_of_opcodeProjection_eq
    {left right : Script}
    (projectionEq : scriptOpcodeProjection left =
      scriptOpcodeProjection right) :
    nonPushOpCount left = nonPushOpCount right := by
  unfold nonPushOpCount
  rw [fold_nonPush_projection, fold_nonPush_projection, projectionEq]

/-- The non-push opcode count is independent of the key-HASH160 resolver used
    by compilation. No key-hash size or fragment typing premise is needed. -/
theorem nonPushOpCount_compileWithKeyHash_eq
    (leftKeyHash rightKeyHash : PubKey → Hash160)
    (fragment : CoreFragment) :
    nonPushOpCount (compileWithKeyHash leftKeyHash fragment) =
      nonPushOpCount (compileWithKeyHash rightKeyHash fragment) :=
  nonPushOpCount_eq_of_opcodeProjection_eq
    (compileWithKeyHash_opcodeProjection_eq leftKeyHash rightKeyHash fragment)

/-- Static opcode accounting on the formal compiler equals the executable
    resource-analysis compiler's accounting. -/
theorem nonPushOpCount_compileForResourceAnalysis (fragment : CoreFragment) :
    nonPushOpCount (compile fragment) =
      nonPushOpCount (compileForResourceAnalysis fragment) := by
  unfold compile compileForResourceAnalysis
  exact nonPushOpCount_compileWithKeyHash_eq _ _ fragment

/-- Concrete compilation has the same static opcode count as formal
    compilation. -/
theorem nonPushOpCount_compileConcrete (fragment : CoreFragment) :
    nonPushOpCount (compileConcrete fragment) =
      nonPushOpCount (compile fragment) := by
  unfold compileConcrete compile
  exact nonPushOpCount_compileWithKeyHash_eq _ _ fragment

/-- The static opcode field reported by resource analysis is the count on the
    formal compiled script. -/
theorem resourceUsage_staticOps_eq_compile (fragment : CoreFragment) :
    (resourceUsage fragment).staticOps = nonPushOpCount (compile fragment) := by
  change nonPushOpCount (compileForResourceAnalysis fragment) =
    nonPushOpCount (compile fragment)
  exact (nonPushOpCount_compileForResourceAnalysis fragment).symm

/-- Satisfaction opcode summaries can be stated directly using the formal
    compiled script's static opcode count. -/
theorem maxSatisfactionOpCount_eq_compile (fragment : CoreFragment) :
    maxSatisfactionOpCount fragment =
      (opPathBounds fragment).sat.map fun dynamic =>
        nonPushOpCount (compile fragment) + dynamic := by
  unfold maxSatisfactionOpCount
  rw [nonPushOpCount_compileForResourceAnalysis]

end LeanMiniscript.Properties
