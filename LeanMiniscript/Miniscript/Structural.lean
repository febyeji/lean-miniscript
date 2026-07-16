import LeanMiniscript.Miniscript.Conformance
import LeanMiniscript.Script.ControlFlow

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Structural compiler guarantees

These proofs derive opcode closure and balanced conditional control flow for
every core fragment, not just the finite conformance fixture matrix.
-/

private theorem keyPushCompilation_allNonConditional
    {keys : List PubKey} {script : Script}
    (conforms : Bip379KeyPushCompilation keys script) :
    AllNonConditional script := by
  induction conforms with
  | nil => trivial
  | cons tailConforms tailAll => exact ⟨by trivial, tailAll⟩

private theorem checkSigAddTailCompilation_allNonConditional
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddTailCompilation keys script) :
    AllNonConditional script := by
  induction conforms with
  | nil => trivial
  | cons tailConforms tailAll => exact ⟨by trivial, by trivial, tailAll⟩

private theorem checkSigAddCompilation_allNonConditional
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddCompilation keys script) :
    AllNonConditional script := by
  cases conforms with
  | nil => exact ⟨by trivial, trivial⟩
  | cons tailConforms =>
      exact ⟨by trivial, by trivial,
        checkSigAddTailCompilation_allNonConditional tailConforms⟩

mutual

/-- Every script admitted by the relational BIP 379 compiler has correctly
nested conditional delimiters. -/
theorem Bip379Compilation.balancedControlFlow
    {keyHash : PubKey → Hash160} {fragment : CoreFragment} {script : Script}
    (conforms : Bip379Compilation keyHash fragment script) :
    BalancedControlFlow script := by
  cases conforms with
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 |
      hash160 =>
      apply BalancedControlFlow.ofAllNonConditional
      simp_all [AllNonConditional, NonConditional]
  | andV xConforms yConforms =>
      exact BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (Bip379Compilation.balancedControlFlow yConforms)
  | andB xConforms yConforms =>
      have operatorBalanced : BalancedControlFlow [.op .OP_BOOLAND] :=
        .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (BalancedControlFlow.append
          (Bip379Compilation.balancedControlFlow yConforms) operatorBalanced)
  | orB xConforms yConforms =>
      have operatorBalanced : BalancedControlFlow [.op .OP_BOOLOR] :=
        .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (BalancedControlFlow.append
          (Bip379Compilation.balancedControlFlow yConforms) operatorBalanced)
  | orC xConforms yConforms =>
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (BalancedControlFlow.notifThen
          (Bip379Compilation.balancedControlFlow yConforms))
  | orD xConforms yConforms =>
      have ifDupBalanced : BalancedControlFlow [.op .OP_IFDUP] :=
        .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (BalancedControlFlow.append ifDupBalanced
          (BalancedControlFlow.notifThen
            (Bip379Compilation.balancedControlFlow yConforms)))
  | orI xConforms yConforms =>
      exact BalancedControlFlow.ifElse
        (Bip379Compilation.balancedControlFlow xConforms)
        (Bip379Compilation.balancedControlFlow yConforms)
  | andor xConforms yConforms zConforms =>
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow xConforms)
        (BalancedControlFlow.notifElse
          (Bip379Compilation.balancedControlFlow zConforms)
          (Bip379Compilation.balancedControlFlow yConforms))
  | a conforms =>
      have toAltBalanced : BalancedControlFlow [.op .OP_TOALTSTACK] :=
        .atom (by trivial)
      have fromAltBalanced : BalancedControlFlow [.op .OP_FROMALTSTACK] :=
        .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append toAltBalanced
        (BalancedControlFlow.append
          (Bip379Compilation.balancedControlFlow conforms) fromAltBalanced)
  | s conforms =>
      have swapBalanced : BalancedControlFlow [.op .OP_SWAP] := .atom (by trivial)
      exact BalancedControlFlow.append swapBalanced
        (Bip379Compilation.balancedControlFlow conforms)
  | c conforms =>
      have operatorBalanced : BalancedControlFlow [.op .OP_CHECKSIG] :=
        .atom (by trivial)
      exact BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow conforms) operatorBalanced
  | v conforms =>
      have operatorBalanced : BalancedControlFlow [.op .OP_VERIFY] :=
        .atom (by trivial)
      exact BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow conforms) operatorBalanced
  | n conforms =>
      have operatorBalanced : BalancedControlFlow [.op .OP_0NOTEQUAL] :=
        .atom (by trivial)
      exact BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow conforms) operatorBalanced
  | d conforms =>
      have dupBalanced : BalancedControlFlow [.op .OP_DUP] := .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append dupBalanced
        (BalancedControlFlow.ifThen
          (Bip379Compilation.balancedControlFlow conforms))
  | j conforms =>
      have prefixBalanced : BalancedControlFlow
          [.op .OP_SIZE, .op .OP_0NOTEQUAL] := by
        apply BalancedControlFlow.ofAllNonConditional
        simp [AllNonConditional, NonConditional]
      simpa [List.append_assoc] using BalancedControlFlow.append prefixBalanced
        (BalancedControlFlow.ifThen
          (Bip379Compilation.balancedControlFlow conforms))
  | @thresh k fragments script conforms =>
      have suffixBalanced : BalancedControlFlow [.pushNum k, .op .OP_EQUAL] := by
        apply BalancedControlFlow.ofAllNonConditional
        simp [AllNonConditional, NonConditional]
      exact BalancedControlFlow.append
        (Bip379ThreshCompilation.balancedControlFlow conforms) suffixBalanced
  | @multi k keys keyScript keysConform =>
      have countBalanced : BalancedControlFlow [.pushNum k] := .atom (by trivial)
      have keysBalanced : BalancedControlFlow keyScript :=
        .ofAllNonConditional (keyPushCompilation_allNonConditional keysConform)
      have suffixBalanced : BalancedControlFlow
          [.pushNum keys.length, .op .OP_CHECKMULTISIG] := by
        apply BalancedControlFlow.ofAllNonConditional
        simp [AllNonConditional, NonConditional]
      simpa [List.append_assoc] using BalancedControlFlow.append countBalanced
        (BalancedControlFlow.append keysBalanced suffixBalanced)
  | @multiA k keys keyScript keysConform =>
      have keysBalanced : BalancedControlFlow keyScript :=
        .ofAllNonConditional (checkSigAddCompilation_allNonConditional keysConform)
      have suffixBalanced : BalancedControlFlow [.pushNum k, .op .OP_NUMEQUAL] := by
        apply BalancedControlFlow.ofAllNonConditional
        simp [AllNonConditional, NonConditional]
      exact BalancedControlFlow.append keysBalanced suffixBalanced

/-- Threshold compilation preserves balanced control flow. -/
theorem Bip379ThreshCompilation.balancedControlFlow
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshCompilation keyHash fragments script) :
    BalancedControlFlow script := by
  cases conforms with
  | nil => exact .nil
  | cons headConforms tailConforms =>
      exact BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow headConforms)
        (Bip379ThreshTailCompilation.balancedControlFlow tailConforms)

/-- Threshold-tail compilation preserves balanced control flow. -/
theorem Bip379ThreshTailCompilation.balancedControlFlow
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshTailCompilation keyHash fragments script) :
    BalancedControlFlow script := by
  cases conforms with
  | nil => exact .nil
  | cons headConforms tailConforms =>
      have addBalanced : BalancedControlFlow [.op .OP_ADD] := .atom (by trivial)
      simpa [List.append_assoc] using BalancedControlFlow.append
        (Bip379Compilation.balancedControlFlow headConforms)
        (BalancedControlFlow.append addBalanced
          (Bip379ThreshTailCompilation.balancedControlFlow tailConforms))

end

/-- The parameterized executable compiler always emits balanced control flow. -/
theorem compileWithKeyHash_balancedControlFlow
    (keyHash : PubKey → Hash160) (fragment : CoreFragment) :
    BalancedControlFlow (compileWithKeyHash keyHash fragment) :=
  (compileWithKeyHash_conforms keyHash fragment).balancedControlFlow

/-- The model's abstract-HASH160 compiler always emits balanced control flow. -/
theorem compile_balancedControlFlow (fragment : CoreFragment) :
    BalancedControlFlow (compile fragment) :=
  compileWithKeyHash_balancedControlFlow hash160 fragment

/-- Surface compilation emits balanced control flow after desugaring. -/
theorem compileSurfaceWithKeyHash_balancedControlFlow
    (keyHash : PubKey → Hash160) (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurfaceWithKeyHash keyHash fragment) :=
  compileWithKeyHash_balancedControlFlow keyHash (desugar fragment)

/-- The model's surface compiler emits balanced control flow. -/
theorem compileSurface_balancedControlFlow (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurface fragment) :=
  compileSurfaceWithKeyHash_balancedControlFlow hash160 fragment

/-- Compiler output uses only the closed opcode universe represented by
`Opcode`. This is a type-level closure result, independent of fragment shape. -/
theorem compileWithKeyHash_usesOnlyModeledOpcodes
    (keyHash : PubKey → Hash160) (fragment : CoreFragment) :
    UsesOnlyModeledOpcodes (compileWithKeyHash keyHash fragment) :=
  usesOnlyModeledOpcodes _

theorem compile_usesOnlyModeledOpcodes (fragment : CoreFragment) :
    UsesOnlyModeledOpcodes (compile fragment) :=
  usesOnlyModeledOpcodes _

/-- Surface compiler output has the same type-level opcode closure. -/
theorem compileSurface_usesOnlyModeledOpcodes (fragment : SurfaceFragment) :
    UsesOnlyModeledOpcodes (compileSurface fragment) :=
  usesOnlyModeledOpcodes _

end LeanMiniscript.Miniscript
