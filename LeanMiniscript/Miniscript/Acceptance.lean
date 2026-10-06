import LeanMiniscript.Script.ValidationWeight
import LeanMiniscript.Miniscript.Context
import LeanMiniscript.Miniscript.Witness

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Execution and final acceptance

`Eval` describes resource-free instruction execution and may finish with any successful stack
shape. The predicates below state the additional witness-order, context-flag,
truth-value, and clean-stack conditions used by Miniscript-facing claims.

This is still a model boundary rather than a claim that every Bitcoin Core
consensus or policy flag has been formalized. `ModeledContextFlags` records the
flags that the current `Eval` semantics enforces.
-/

/-- Required settings among the flags currently enforced by `Eval`.

    Both contexts require minimal Script-number operands. P2WSH additionally
    uses the modeled Miniscript-facing MINIMALIF and NULLDUMMY settings.
    P2WSH enables NULLFAIL and STRICTENC. Tapscript enforces MINIMALIF through
    its signature version rather than a flag and ignores the ECDSA encoding and
    NULLFAIL flags; its signature failures are controlled by that version. -/
def ModeledContextFlags (ctx : ScriptContext) (flags : ScriptFlags) : Prop :=
  match ctx with
  | .p2wsh =>
      flags.minimalIf = true ∧
      flags.minimalData = true ∧
      flags.nullDummy = true ∧
      flags.nullFail = true ∧
      flags.strictEncoding = true
  | .tapscript =>
      flags.minimalData = true

/-- The execution version must agree with the Miniscript script context. -/
def ModeledContextVersion (ctx : ScriptContext) (txCtx : TxContext) : Prop :=
  txCtx.sigVersion = match ctx with
    | .p2wsh => .witnessV0
    | .tapscript => .tapscript

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
  ModeledContextVersion ctx txCtx ∧
  CleanStackResult script witness flags txCtx true

/-- A clean dissatisfaction executes without a Script error and leaves exactly
    one false main-stack item. -/
def Dissatisfies (ctx : ScriptContext) (script : Script) (witness : Witness)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop :=
  ModeledContextFlags ctx flags ∧
  ModeledContextVersion ctx txCtx ∧
  CleanStackResult script witness flags txCtx false

/-- Resource-aware script-path acceptance. The full-witness boundary checks
    script bytes, annex, initial arguments, runtime stack/push limits and the
    BIP342 signature budget. Control-block commitment remains outside this
    predicate. Unlike `Accepts`, this includes runtime resource accounting. -/
def TapscriptAccepts (script : Script) (witness : TapscriptWitness)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop :=
  ModeledContextFlags .tapscript flags ∧
  ∃ top finalAlt weight,
    evaluateTapscript CryptoOracle.model script witness flags txCtx =
      .success [top] finalAlt weight ∧ castToBool top = true

/-- A budget-checked clean false result, without a terminal Script error. -/
def TapscriptDissatisfies (script : Script) (witness : TapscriptWitness)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop :=
  ModeledContextFlags .tapscript flags ∧
  ∃ top finalAlt weight,
    evaluateTapscript CryptoOracle.model script witness flags txCtx =
      .success [top] finalAlt weight ∧ castToBool top = false

/-- Executable acceptance for the modeled Miniscript Tapscript flag contract.
    Unsupported flags produce a MODEL error; execution failures and Core's
    CLEANSTACK/EVAL_FALSE checks retain their own errors. Success returns the
    unused signature budget. This does not validate the control-block commitment. -/
def checkTapscriptAcceptance (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags) (txCtx : TxContext) :
    Except ScriptError Nat :=
  if flags.minimalData then
    (evaluateTapscript oracle script witness flags txCtx).checkAcceptance
  else .error .tapscriptFlags

end LeanMiniscript.Miniscript
