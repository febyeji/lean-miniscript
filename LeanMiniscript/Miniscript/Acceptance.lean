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
flags that the current semantics can state precisely.
-/

/-- Required settings among the flags currently represented by the model.

    P2WSH uses the standard Miniscript-facing MINIMALIF, NULLDUMMY, and strict
    encoding settings. Tapscript requires MINIMALIF; its signature encoding and
    disabled-opcode rules need separate Tapscript-specific modeling. -/
def ModeledContextFlags (ctx : ScriptContext) (flags : ScriptFlags) : Prop :=
  match ctx with
  | .p2wsh =>
      flags.minimalIf = true ∧
      flags.nullDummy = true ∧
      flags.strictEncoding = true
  | .tapscript =>
      flags.minimalIf = true

/-- Execute a serialized-order witness against a script. The operational
    semantics receives a top-first main stack and an initially empty alt stack. -/
def Executes (script : Script) (witness : Witness) (flags : ScriptFlags)
    (txCtx : TxContext) (result : ExecResult) : Prop :=
  Eval script witness.toInitialStack [] flags txCtx result

/-- Successful execution with the final clean-stack shape and the requested
    truth value. Instruction failure is distinct from a successful false top. -/
def CleanStackResult (script : Script) (witness : Witness)
    (flags : ScriptFlags) (txCtx : TxContext) (expected : Bool) : Prop :=
  ∃ top,
    Executes script witness flags txCtx (.success [top] []) ∧
    castToBool top = expected

/-- Final acceptance for the currently modeled context checks: execution
    succeeds, leaves exactly one truthy main-stack item, and empties the alt
    stack. -/
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
  · refine ⟨trueElement, ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_one] using
      (Eval.pushNum 1 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 1] [])
        (Eval.empty [scriptNum 1] [] contractExampleFlags contractExampleTxCtx))

/-- A successful false result is a dissatisfaction, not an execution error. -/
example : Dissatisfies .p2wsh [.pushNum 0] []
    contractExampleFlags contractExampleTxCtx := by
  constructor
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨falseElement, ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_zero] using
      (Eval.pushNum 0 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 0] [])
        (Eval.empty [scriptNum 0] [] contractExampleFlags contractExampleTxCtx))

/-- P2WSH acceptance rejects a flag set that disables the modeled MINIMALIF
    requirement before execution is considered. -/
example : ¬ ModeledContextFlags .p2wsh
    ({ minimalIf := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

end LeanMiniscript.Miniscript
