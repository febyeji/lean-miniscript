import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.CompileVerifyProofs
import LeanMiniscript.Miniscript.ExecutionFrameProofs
import LeanMiniscript.Miniscript.SatisfactionLemmas
import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A selected B-type execution consumes `args` and leaves one exact result. -/
def BExecution (fragment : CoreFragment) (args : Stack) (result : StackElement)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [result] flags ctx

/-- A selected V-type execution consumes `args` and leaves no result. -/
def VExecution (fragment : CoreFragment) (args : Stack)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [] flags ctx

/-- A selected K-type execution consumes `args` and leaves the exact key-like
    element needed by a following `OP_CHECKSIG`. -/
def KExecution (fragment : CoreFragment) (args : Stack) (key : StackElement)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [key] flags ctx

/-- The two exact output orders used by W wrappers. Wrapper `a` restores the
    protected element above its B result; wrapper `s` will leave the B result
    above the protected element. -/
inductive WStackOrder where
  | savedFirst
  | resultFirst
  deriving Repr, DecidableEq, BEq

namespace WStackOrder

/-- Materialize a W output prefix without hiding its order in an existential. -/
def outputs : WStackOrder → StackElement → StackElement → Stack
  | .savedFirst, saved, result => [saved, result]
  | .resultFirst, saved, result => [result, saved]

/-- Exact numeric-decoding premise for a binary opcode following a W fragment.
    `decodeBinaryScriptNums` receives the top element first, so the operand and
    decoded-value order follows the W wrapper's concrete output order. -/
def BinaryDecoded (order : WStackOrder) (flags : ScriptFlags)
    (saved result : StackElement) (savedValue resultValue : Int) : Prop :=
  match order with
  | .savedFirst =>
      decodeBinaryScriptNums flags saved result = .ok (savedValue, resultValue)
  | .resultFirst =>
      decodeBinaryScriptNums flags result saved = .ok (resultValue, savedValue)

end WStackOrder

/-- A selected W-type execution runs below one protected main-stack element
    and returns the protected element and exact B result in the wrapper's
    declared order. -/
def WExecution (fragment : CoreFragment) (args : Stack) (result : StackElement)
    (order : WStackOrder) (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∀ saved : StackElement,
    ExecutesStackFrame (compile fragment) (saved :: args)
      (order.outputs saved result) flags ctx

/-- A W-type execution together with the truth value of its B child result.
    The protected stack element is kept separate from that truth value. -/
def WExecutionOutcome (fragment : CoreFragment) (args : Stack)
    (expected : Bool) (order : WStackOrder) (flags : ScriptFlags)
    (ctx : TxContext) : Prop :=
  ∃ result, WExecution fragment args result order flags ctx ∧
    castToBool result = expected

/-- Execute a W child below an exact saved accumulator and immediately add its
    result. Both W output orders produce the same source-order sum; the
    `BinaryDecoded` premise records the physical top-first operand order seen
    by `OP_ADD`. -/
theorem WExecution.addToSaved
    {fragment : CoreFragment} {args : Stack} {saved result : StackElement}
    {savedValue resultValue : Int} {order : WStackOrder}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : WExecution fragment args result order flags ctx)
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesStackFrame (compile fragment ++ [.op .OP_ADD]) (saved :: args)
      [scriptNum (savedValue + resultValue)] flags ctx := by
  intro rest altStack
  have childRun := executed saved rest altStack
  cases order with
  | savedFirst =>
      have addRun :
          Eval [.op .OP_ADD] (saved :: result :: rest) altStack flags ctx
            (.success (scriptNum (savedValue + resultValue) :: rest)
              altStack) := by
        exact Eval.add saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
      simpa [WExecution, WStackOrder.outputs, ExecutesStackFrame] using
        Eval.append childRun addRun
  | resultFirst =>
      have addRun :
          Eval [.op .OP_ADD] (result :: saved :: rest) altStack flags ctx
            (.success (scriptNum (savedValue + resultValue) :: rest)
              altStack) := by
        simpa [Int.add_comm] using
          (Eval.add result saved resultValue savedValue rest [] altStack flags
            ctx _ decoded Eval.done)
      simpa [WExecution, WStackOrder.outputs, ExecutesStackFrame] using
        Eval.append childRun addRun

/-- A B-type execution together with the truth value required by satisfaction
    or dissatisfaction. -/
def BExecutionOutcome (fragment : CoreFragment) (args : Stack) (expected : Bool)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∃ result, BExecution fragment args result flags ctx ∧
    castToBool result = expected

/-- A selected B-type execution over a serialized witness yields the existing
    clean-stack result when instantiated with empty surrounding stacks. -/
theorem BExecutionOutcome.cleanStackResult
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment witness.toInitialStack expected flags ctx) :
    CleanStackResult (compile fragment) witness flags ctx expected := by
  obtain ⟨result, frame, truth⟩ := executed
  refine ⟨result, [], ?_, truth⟩
  simpa [BExecution, ExecutesStackFrame, Executes, Witness.toInitialStack] using
    frame [] []

/-! ## Base-type composition -/

/-- Wrapper `c` places a signature below the K fragment's own arguments, then
    converts its exact key output into a boolean B result. -/
theorem KExecution.c
    {fragment : CoreFragment} {args : Stack} {key signature : StackElement}
    {valid : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution fragment args key flags ctx)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok valid) :
    BExecution (.c fragment) (args ++ [signature]) (boolToElement valid)
      flags ctx := by
  intro rest altStack
  have keyExec := executed (signature :: rest) altStack
  have checkExec :
      Eval [.op .OP_CHECKSIG] (key :: signature :: rest) altStack flags ctx
        (.success (boolToElement valid :: rest) altStack) := by
    cases valid with
    | false =>
        simpa [boolToElement] using
          (Eval.checksigFalse checked
            (Eval.done (stack := falseElement :: rest) (altStack := altStack)))
    | true =>
        simpa [boolToElement] using
          (Eval.checksigTrue checked
            (Eval.done (stack := trueElement :: rest) (altStack := altStack)))
  simpa [BExecution, KExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append keyExec checkExec

/-- Wrapper `v` consumes a truthy B result and turns successful execution into
    the silent V stack shape. -/
theorem BExecution.v
    {fragment : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args result flags ctx)
    (truthy : castToBool result = true) :
    VExecution (.v fragment) args flags ctx := by
  intro rest altStack
  have fragmentExec := executed rest altStack
  have verifyExec :
      Eval [.op .OP_VERIFY] (result :: rest) altStack flags ctx
        (.success rest altStack) :=
    Eval.verifyTrue truthy
      (Eval.done (stack := rest) (altStack := altStack))
  have unfused := Eval.append fragmentExec verifyExec
  have optimized := Eval.compileVerify_success
    (compile_balancedControlFlow fragment) unfused
  simpa [BExecution, VExecution, ExecutesStackFrame, compile,
    compileWithKeyHash] using optimized

/-- A satisfying B outcome lifts through `v`; there is intentionally no false
    counterpart because a V fragment aborts instead of dissatisfying. -/
theorem BExecutionOutcome.v
    {fragment : CoreFragment} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment args true flags ctx) :
    VExecution (.v fragment) args flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact frame.v truth

/-- Wrapper `a` protects one main-stack item on the alternate stack while its
    B child executes, then restores that item above the child's result. -/
theorem BExecution.a
    {fragment : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args result flags ctx) :
    WExecution (.a fragment) args result .savedFirst flags ctx := by
  intro saved rest altStack
  have fragmentExec := executed rest (saved :: altStack)
  have restoreExec :
      Eval [.op .OP_FROMALTSTACK] (result :: rest) (saved :: altStack) flags ctx
        (.success (saved :: result :: rest) altStack) :=
    Eval.fromAltStackNext
      (Eval.done (stack := saved :: result :: rest) (altStack := altStack))
  have bodyExec := Eval.append fragmentExec restoreExec
  simpa [BExecution, WExecution, WStackOrder.outputs, ExecutesStackFrame,
    compile, compileWithKeyHash] using Eval.toAltStackNext bodyExec

/-- Satisfaction and dissatisfaction truth values pass through `a` while its
    protected element is restored above the result. -/
theorem BExecutionOutcome.a
    {fragment : CoreFragment} {args : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment args expected flags ctx) :
    WExecutionOutcome (.a fragment) args expected .savedFirst flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.a, truth⟩

/-- Wrapper `s` swaps one protected element with its child's single argument.
    The singleton input is the semantic content of the wrapper's `o` typing
    premise; raw candidate propagation alone does not establish this shape. -/
theorem BExecution.s
    {fragment : CoreFragment} {argument result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment [argument] result flags ctx) :
    WExecution (.s fragment) [argument] result .resultFirst flags ctx := by
  intro saved rest altStack
  have childExec := executed (saved :: rest) altStack
  simpa [BExecution, WExecution, WStackOrder.outputs, ExecutesStackFrame,
    compile, compileWithKeyHash] using
    (Eval.swap saved argument rest altStack (compile fragment) flags ctx
      (.success (result :: saved :: rest) altStack) childExec)

/-- A singleton-argument B outcome passes through `s`, with the result above
    the protected element. -/
theorem BExecutionOutcome.s
    {fragment : CoreFragment} {argument : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment [argument] expected flags ctx) :
    WExecutionOutcome (.s fragment) [argument] expected .resultFirst flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.s, truth⟩

/-- Canonical boolean stack elements round-trip through Script truthiness. -/
@[simp] theorem castToBool_boolToElement (value : Bool) :
    castToBool (boolToElement value) = value := by
  cases value <;> decide

/-- Wrapper `n` executes `OP_0NOTEQUAL` on the child's exact result. The
    explicit four-byte decode premise is required because B truthiness alone
    does not imply that Script-number decoding succeeds. -/
theorem BExecution.n
    {fragment : CoreFragment} {args : Stack} {operand : StackElement}
    {value : Int} {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args operand flags ctx)
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .ok value) :
    BExecution (.n fragment) args (boolToElement (value != 0)) flags ctx := by
  intro rest altStack
  have childExec := executed rest altStack
  have normalizeExec :
      Eval [.op .OP_0NOTEQUAL] (operand :: rest) altStack flags ctx
        (.success (boolToElement (value != 0) :: rest) altStack) :=
    Eval.zeroNotEqual operand value rest altStack [] flags ctx
      (.success (boolToElement (value != 0) :: rest) altStack) decoded
      (Eval.done (stack := boolToElement (value != 0) :: rest)
        (altStack := altStack))
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    Eval.append childExec normalizeExec

/-- The normalized `n` result has the requested truth value when the decoded
    integer's zero test agrees with that value. -/
theorem BExecution.nOutcome
    {fragment : CoreFragment} {args : Stack} {operand : StackElement}
    {value : Int} {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args operand flags ctx)
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .ok value)
    (truth : (value != 0) = expected) :
    BExecutionOutcome (.n fragment) args expected flags ctx := by
  refine ⟨boolToElement (value != 0), executed.n decoded, ?_⟩
  exact (castToBool_boolToElement (value != 0)).trans truth

end LeanMiniscript.Miniscript
