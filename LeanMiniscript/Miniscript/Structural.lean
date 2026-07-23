import LeanMiniscript.Miniscript.Conformance
import LeanMiniscript.Miniscript.Checked
import LeanMiniscript.Script.ControlFlow

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Structural compiler guarantees

These proofs derive context-safe opcode emission and balanced conditional
control flow for every core fragment, not just the finite conformance fixture
matrix. Context safety is deliberately separate from the closed `Opcode`
universe: it uses `WellFormed` to exclude the wrong multisig encoding for the
selected Script context.
-/

@[simp]
theorem scriptAllowed_append {ctx : ScriptContext} {left right : Script} :
    ScriptAllowed ctx (left ++ right) ↔
      ScriptAllowed ctx left ∧ ScriptAllowed ctx right := by
  induction left with
  | nil => simp [ScriptAllowed]
  | cons element left ih => simp [ScriptAllowed, ih, and_assoc]

private theorem legacyMulti_opcodeAllowed {ctx : ScriptContext}
    (permits : ctx.permitsLegacyMulti) :
    OpcodeAllowed ctx .OP_CHECKMULTISIG := by
  cases ctx <;>
    simp_all [ScriptContext.permitsLegacyMulti, OpcodeAllowed]

private theorem checkSigAdd_opcodeAllowed {ctx : ScriptContext}
    (permits : ctx.permitsCheckSigAddMulti) :
    OpcodeAllowed ctx .OP_CHECKSIGADD := by
  cases ctx <;>
    simp_all [ScriptContext.permitsCheckSigAddMulti, OpcodeAllowed]

private theorem Bip379KeyPushCompilation.scriptAllowed
    {keys : List PubKey} {script : Script}
    (conforms : Bip379KeyPushCompilation keys script) (ctx : ScriptContext) :
    ScriptAllowed ctx script := by
  induction conforms with
  | nil => trivial
  | cons tailConforms tailAllowed => exact ⟨by trivial, tailAllowed⟩

private theorem Bip379CheckSigAddTailCompilation.scriptAllowed
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddTailCompilation keys script)
    {ctx : ScriptContext} (permits : ctx.permitsCheckSigAddMulti) :
    ScriptAllowed ctx script := by
  induction conforms with
  | nil => trivial
  | cons tailConforms tailAllowed =>
      exact ⟨by trivial, checkSigAdd_opcodeAllowed permits, tailAllowed⟩

private theorem Bip379CheckSigAddCompilation.scriptAllowed
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddCompilation keys script)
    {ctx : ScriptContext} (permits : ctx.permitsCheckSigAddMulti) :
    ScriptAllowed ctx script := by
  cases conforms with
  | nil => exact ⟨by trivial, by trivial⟩
  | cons tailConforms =>
      exact ⟨by trivial,
        by simp [ScriptElementAllowed, OpcodeAllowed],
        tailConforms.scriptAllowed permits⟩

mutual

/-- A relationally conforming compilation of a well-formed fragment contains
only opcodes allowed by the selected Script context. -/
theorem Bip379Compilation.scriptAllowed
    {keyHash : PubKey → Hash160} {fragment : CoreFragment} {script : Script}
    (conforms : Bip379Compilation keyHash fragment script)
    {ctx : ScriptContext} (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx script := by
  cases conforms with
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 |
      hash160 =>
      simp [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed]
  | andV xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2.1)
  | andB xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2.1)
  | orB xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2)
  | orC xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2)
  | orD xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2)
  | orI xConforms yConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (Bip379Compilation.scriptAllowed yConforms wellFormed.2)
  | andor xConforms yConforms zConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed xConforms wellFormed.1)
          (And.intro
            (Bip379Compilation.scriptAllowed zConforms wellFormed.2.2.1)
            (Bip379Compilation.scriptAllowed yConforms wellFormed.2.1))
  | a conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | s conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | c conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | d conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | v conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | j conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | n conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379Compilation.scriptAllowed conforms wellFormed
  | thresh conforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        Bip379ThreshCompilation.scriptAllowed conforms wellFormed.2.1
  | multi _ keysConform =>
      have keysAllowed := keysConform.scriptAllowed ctx
      have checkAllowed := legacyMulti_opcodeAllowed wellFormed.1
      simpa [ScriptAllowed, ScriptElementAllowed] using
        And.intro keysAllowed checkAllowed
  | multiA _ keysConform =>
      have keysAllowed := keysConform.scriptAllowed wellFormed.1
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        keysAllowed

/-- Threshold compilation is context-safe when every child is well-formed. -/
theorem Bip379ThreshCompilation.scriptAllowed
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment}
    {script : Script}
    (conforms : Bip379ThreshCompilation keyHash fragments script)
    {ctx : ScriptContext} (allWellFormed : CoreFragment.allWellFormed ctx fragments) :
    ScriptAllowed ctx script := by
  cases conforms with
  | nil => trivial
  | cons headConforms tailConforms =>
      exact scriptAllowed_append.mpr ⟨
        Bip379Compilation.scriptAllowed headConforms allWellFormed.1,
        Bip379ThreshTailCompilation.scriptAllowed tailConforms allWellFormed.2⟩

/-- Threshold-tail compilation is context-safe when every child is
well-formed. -/
theorem Bip379ThreshTailCompilation.scriptAllowed
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment}
    {script : Script}
    (conforms : Bip379ThreshTailCompilation keyHash fragments script)
    {ctx : ScriptContext} (allWellFormed : CoreFragment.allWellFormed ctx fragments) :
    ScriptAllowed ctx script := by
  cases conforms with
  | nil => trivial
  | cons headConforms tailConforms =>
      simpa [ScriptAllowed, ScriptElementAllowed, OpcodeAllowed] using
        And.intro
          (Bip379Compilation.scriptAllowed headConforms allWellFormed.1)
          (Bip379ThreshTailCompilation.scriptAllowed tailConforms allWellFormed.2)

end

/-! ## Context-safe executable compiler corollaries -/

/-- The parameterized compiler emits only opcodes allowed by the fragment's
validated Script context. -/
theorem compileWithKeyHash_scriptAllowed
    (keyHash : PubKey → Hash160) {ctx : ScriptContext}
    {fragment : CoreFragment} (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileWithKeyHash keyHash fragment) :=
  (compileWithKeyHash_conforms keyHash fragment).scriptAllowed wellFormed

/-- The model compiler emits only opcodes allowed by the fragment's validated
Script context. -/
theorem compile_scriptAllowed {ctx : ScriptContext} {fragment : CoreFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compile fragment) :=
  compileWithKeyHash_scriptAllowed modelKeyHash wellFormed

/-- Surface compilation is context-safe through desugaring. -/
theorem compileSurfaceWithKeyHash_scriptAllowed
    (keyHash : PubKey → Hash160) {ctx : ScriptContext}
    {fragment : SurfaceFragment} (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileSurfaceWithKeyHash keyHash fragment) :=
  compileWithKeyHash_scriptAllowed keyHash wellFormed

/-- The model surface compiler is context-safe through desugaring. -/
theorem compileSurface_scriptAllowed
    {ctx : ScriptContext} {fragment : SurfaceFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileSurface fragment) :=
  compileSurfaceWithKeyHash_scriptAllowed modelKeyHash wellFormed

/-- Checked core compilation exposes context safety without another caller
proof obligation. -/
theorem compileCheckedWithKeyHash_scriptAllowed
    (keyHash : PubKey → Hash160) {ctx : ScriptContext}
    (checked : CheckedFragment ctx) :
    ScriptAllowed ctx (compileCheckedWithKeyHash keyHash checked) :=
  compileWithKeyHash_scriptAllowed keyHash checked.wellFormed

/-- Checked core compilation with the model HASH160 boundary is context-safe. -/
theorem compileChecked_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedFragment ctx) :
    ScriptAllowed ctx (compileChecked checked) :=
  compile_scriptAllowed checked.wellFormed

/-- Checked surface compilation exposes context safety without another caller
proof obligation. -/
theorem compileCheckedSurfaceWithKeyHash_scriptAllowed
    (keyHash : PubKey → Hash160) {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) :
    ScriptAllowed ctx (compileCheckedSurfaceWithKeyHash keyHash checked) :=
  compileSurfaceWithKeyHash_scriptAllowed keyHash checked.wellFormed

/-- Checked surface compilation with the model HASH160 boundary is
context-safe. -/
theorem compileCheckedSurface_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) :
    ScriptAllowed ctx (compileCheckedSurface checked) :=
  compileSurface_scriptAllowed checked.wellFormed

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
  compileWithKeyHash_balancedControlFlow modelKeyHash fragment

/-- Surface compilation emits balanced control flow after desugaring. -/
theorem compileSurfaceWithKeyHash_balancedControlFlow
    (keyHash : PubKey → Hash160) (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurfaceWithKeyHash keyHash fragment) :=
  compileWithKeyHash_balancedControlFlow keyHash (desugar fragment)

/-- The model's surface compiler emits balanced control flow. -/
theorem compileSurface_balancedControlFlow (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurface fragment) :=
  compileSurfaceWithKeyHash_balancedControlFlow modelKeyHash fragment

end LeanMiniscript.Miniscript
