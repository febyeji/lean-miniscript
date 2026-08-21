import LeanMiniscript.Script.BigStep
import LeanMiniscript.Miniscript.Context
import LeanMiniscript.Miniscript.Witness

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Execution and final acceptance

`Eval` describes instruction execution and may finish with any successful stack
shape. The predicates below state the additional witness-order, context-flag,
truth-value, and clean-stack conditions used by Miniscript-facing claims.

This is still a model boundary rather than a claim that every Bitcoin Core
consensus or policy flag has been formalized. `ModeledContextFlags` records the
flags that the current `Eval` semantics enforces.
-/

/-- Required settings among the flags currently enforced by `Eval`.

    Both contexts require minimal Script-number operands. P2WSH additionally
    uses the modeled Miniscript-facing MINIMALIF and NULLDUMMY settings;
    Tapscript requires MINIMALIF. Signature encoding is intentionally excluded:
    the current opaque `checkSig` does not receive flags or a signature version.
    Tapscript signature and disabled-opcode rules need separate modeling. -/
def ModeledContextFlags (ctx : ScriptContext) (flags : ScriptFlags) : Prop :=
  match ctx with
  | .p2wsh =>
      flags.minimalIf = true ∧
      flags.minimalData = true ∧
      flags.nullDummy = true
  | .tapscript =>
      flags.minimalIf = true ∧
      flags.minimalData = true

/-- Execute a serialized-order witness against a script. The operational
    semantics receives a top-first main stack and an initially empty alt stack. -/
def Executes (script : Script) (witness : Witness) (flags : ScriptFlags)
    (txCtx : TxContext) (result : ExecResult) : Prop :=
  Eval script witness.toInitialStack [] flags txCtx result

/-- Successful execution with exactly one final main-stack element and the
    requested truth value. The alternate stack is internal execution state and
    is not part of the final clean-stack check. Instruction failure is distinct
    from a successful false top. -/
def CleanStackResult (script : Script) (witness : Witness)
    (flags : ScriptFlags) (txCtx : TxContext) (expected : Bool) : Prop :=
  ∃ top finalAltStack,
    Executes script witness flags txCtx (.success [top] finalAltStack) ∧
    castToBool top = expected

/-- Final acceptance for the currently modeled context checks: execution
    succeeds and leaves exactly one truthy main-stack item. -/
def Accepts (ctx : ScriptContext) (script : Script) (witness : Witness)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop :=
  ModeledContextFlags ctx flags ∧
  CleanStackResult script witness flags txCtx true

/-- A clean dissatisfaction executes without a Script error and leaves exactly
    one false main-stack item. -/
def Dissatisfies (ctx : ScriptContext) (script : Script) (witness : Witness)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop :=
  ModeledContextFlags ctx flags ∧
  CleanStackResult script witness flags txCtx false

private def contractExampleFlags : ScriptFlags := {}

private def contractExampleTxCtx : TxContext where
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

/-- The acceptance contract is inhabited by the canonical true script. -/
example : Accepts .p2wsh [.pushNum 1] []
    contractExampleFlags contractExampleTxCtx := by
  constructor
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨trueElement, [], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_one] using
      (Eval.pushNum 1 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 1] [])
        (Eval.empty [scriptNum 1] [] contractExampleFlags contractExampleTxCtx))

/-- Clean-stack acceptance constrains the final main stack, not the internal
    alternate stack. -/
example : Accepts .p2wsh
    [.pushNum 1, .op .OP_TOALTSTACK, .pushNum 1] []
    contractExampleFlags contractExampleTxCtx := by
  constructor
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨scriptNum 1, [scriptNum 1], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack] using
      (Eval.pushNum 1 [.op .OP_TOALTSTACK, .pushNum 1] [] []
        contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 1] [scriptNum 1])
        (Eval.toAltStackNext (x := scriptNum 1)
          (Eval.pushNum 1 [] [] [scriptNum 1]
            contractExampleFlags contractExampleTxCtx
            (.success [scriptNum 1] [scriptNum 1])
            (Eval.empty [scriptNum 1] [scriptNum 1]
              contractExampleFlags contractExampleTxCtx))))

/-- A successful false result is a dissatisfaction, not an execution error. -/
example : Dissatisfies .p2wsh [.pushNum 0] []
    contractExampleFlags contractExampleTxCtx := by
  constructor
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨falseElement, [], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_zero] using
      (Eval.pushNum 0 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 0] [])
        (Eval.empty [scriptNum 0] [] contractExampleFlags contractExampleTxCtx))

/-- P2WSH acceptance rejects a flag set that disables the modeled MINIMALIF
    requirement before execution is considered. -/
example : ¬ ModeledContextFlags .p2wsh
    ({ minimalIf := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

/-- Both modeled contexts reject non-minimal numeric operands at their checked
    acceptance boundary. -/
example : ¬ ModeledContextFlags .tapscript
    ({ minimalData := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

/-- Strict signature encoding remains outside the modeled flag contract until
    signature-version-aware checks are part of `Eval`. -/
example : ModeledContextFlags .p2wsh
    ({ strictEncoding := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

end LeanMiniscript.Miniscript
