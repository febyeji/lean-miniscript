import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Composable execution frames

The satisfaction algorithm stores witnesses in serialized order, while Script
execution consumes a top-first stack.  The contracts below operate on the
top-first argument frame so recursive proofs can compose independently of the
candidate-selection representation.

These are successful execution contracts for selected arguments.  They are
distinct from the type guarantees in `Soundness`, which describe the possible
success-or-error behavior of arbitrary inputs.
-/

/-- Executing `script` replaces an exact top-first input frame with an exact
    output frame while preserving every main-stack suffix and the complete
    alternate stack. -/
def ExecutesStackFrame (script : Script) (inputs outputs : Stack)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∀ (rest altStack : Stack),
    Eval script (inputs ++ rest) altStack flags ctx
      (.success (outputs ++ rest) altStack)

/-- Stack-frame execution composes in Script source order. -/
theorem ExecutesStackFrame.append
    {left right : Script} {inputs middle outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (leftExec : ExecutesStackFrame left inputs middle flags ctx)
    (rightExec : ExecutesStackFrame right middle outputs flags ctx) :
    ExecutesStackFrame (left ++ right) inputs outputs flags ctx := by
  intro rest altStack
  exact Eval.append (leftExec rest altStack) (rightExec rest altStack)

/-- Extend both sides of an exact frame by the same protected main-stack
    suffix. This makes sequential child argument frames explicit. -/
theorem ExecutesStackFrame.withSuffix
    {script : Script} {inputs outputs suffix : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : ExecutesStackFrame script inputs outputs flags ctx) :
    ExecutesStackFrame script (inputs ++ suffix) (outputs ++ suffix) flags ctx := by
  intro rest altStack
  simpa [List.append_assoc] using executed (suffix ++ rest) altStack

/-! ### Exact balanced conditional frames -/

/-- A truthy selector executes the sole balanced `OP_IF` branch. -/
theorem ExecutesStackFrame.ifThen_execute
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (bodyExec : ExecutesStackFrame body inputs outputs flags ctx) :
    ExecutesStackFrame (.op .OP_IF :: body ++ [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.if_execute (frame := { branches := [body], after := [] })
  · simpa using splitConditional_balanced_ifThen balanced (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
      bodyExec rest altStack

/-- A false selector skips the sole balanced `OP_IF` branch. -/
theorem ExecutesStackFrame.ifThen_skip
    {body : Script} {selector : StackElement} {inputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false) :
    ExecutesStackFrame (.op .OP_IF :: body ++ [.op .OP_ENDIF])
      (selector :: inputs) inputs flags ctx := by
  intro rest altStack
  apply Eval.if_execute (frame := { branches := [body], after := [] })
  · simpa using splitConditional_balanced_ifThen balanced (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, falsy] using
      (Eval.done (stack := inputs ++ rest) (altStack := altStack))

/-- A false selector executes the sole balanced `OP_NOTIF` branch. -/
theorem ExecutesStackFrame.notifThen_execute
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (bodyExec : ExecutesStackFrame body inputs outputs flags ctx) :
    ExecutesStackFrame (.op .OP_NOTIF :: body ++ [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.notif_execute (frame := { branches := [body], after := [] })
  · simpa using splitConditional_balanced_ifThen balanced (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, falsy] using
      bodyExec rest altStack

/-- A truthy selector skips the sole balanced `OP_NOTIF` branch. -/
theorem ExecutesStackFrame.notifThen_skip
    {body : Script} {selector : StackElement} {inputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    ExecutesStackFrame (.op .OP_NOTIF :: body ++ [.op .OP_ENDIF])
      (selector :: inputs) inputs flags ctx := by
  intro rest altStack
  apply Eval.notif_execute (frame := { branches := [body], after := [] })
  · simpa using splitConditional_balanced_ifThen balanced (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
      (Eval.done (stack := inputs ++ rest) (altStack := altStack))

/-- A truthy selector executes the first branch of a balanced `OP_IF`/`OP_ELSE`. -/
theorem ExecutesStackFrame.ifElse_first
    {firstBody secondBody : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (firstBalanced : BalancedControlFlow firstBody)
    (secondBalanced : BalancedControlFlow secondBody)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (bodyExec : ExecutesStackFrame firstBody inputs outputs flags ctx) :
    ExecutesStackFrame
      (.op .OP_IF :: firstBody ++ [.op .OP_ELSE] ++ secondBody ++
        [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.if_execute (frame :=
    { branches := [firstBody, secondBody], after := [] })
  · simpa using splitConditional_balanced_ifElse firstBalanced secondBalanced
      (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
      bodyExec rest altStack

/-- A false selector executes the second branch of a balanced `OP_IF`/`OP_ELSE`. -/
theorem ExecutesStackFrame.ifElse_second
    {firstBody secondBody : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (firstBalanced : BalancedControlFlow firstBody)
    (secondBalanced : BalancedControlFlow secondBody)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (bodyExec : ExecutesStackFrame secondBody inputs outputs flags ctx) :
    ExecutesStackFrame
      (.op .OP_IF :: firstBody ++ [.op .OP_ELSE] ++ secondBody ++
        [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.if_execute (frame :=
    { branches := [firstBody, secondBody], after := [] })
  · simpa using splitConditional_balanced_ifElse firstBalanced secondBalanced
      (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, falsy] using
      bodyExec rest altStack

/-- A false selector executes the first branch of balanced
    `OP_NOTIF`/`OP_ELSE`. -/
theorem ExecutesStackFrame.notifElse_first
    {firstBody secondBody : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (firstBalanced : BalancedControlFlow firstBody)
    (secondBalanced : BalancedControlFlow secondBody)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (bodyExec : ExecutesStackFrame firstBody inputs outputs flags ctx) :
    ExecutesStackFrame
      (.op .OP_NOTIF :: firstBody ++ [.op .OP_ELSE] ++ secondBody ++
        [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.notif_execute (frame :=
    { branches := [firstBody, secondBody], after := [] })
  · simpa using splitConditional_balanced_ifElse firstBalanced secondBalanced
      (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, falsy] using
      bodyExec rest altStack

/-- A truthy selector executes the second branch of balanced
    `OP_NOTIF`/`OP_ELSE`. -/
theorem ExecutesStackFrame.notifElse_second
    {firstBody secondBody : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (firstBalanced : BalancedControlFlow firstBody)
    (secondBalanced : BalancedControlFlow secondBody)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (bodyExec : ExecutesStackFrame secondBody inputs outputs flags ctx) :
    ExecutesStackFrame
      (.op .OP_NOTIF :: firstBody ++ [.op .OP_ELSE] ++ secondBody ++
        [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx := by
  intro rest altStack
  apply Eval.notif_execute (frame :=
    { branches := [firstBody, secondBody], after := [] })
  · simpa using splitConditional_balanced_ifElse firstBalanced secondBalanced
      (suffix := [])
  · exact minimal
  · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
      bodyExec rest altStack

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
  simpa [BExecution, VExecution, ExecutesStackFrame, compile,
    compileWithKeyHash] using Eval.append fragmentExec verifyExec

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
  cases value <;> native_decide

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

/-! ## Straight-line connective composition -/

/-- `and_v` runs a V fragment before a B fragment, preserving the latter's
    exact result and every surrounding main/alternate-stack suffix. -/
theorem VExecution.and_v_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.and_v first second) (firstArgs ++ secondArgs) result flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, BExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append firstRun secondRun

/-- The K result of the second `and_v` child remains available to a following
    signature check. -/
theorem VExecution.and_v_k
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : KExecution second secondArgs key flags ctx) :
    KExecution (.and_v first second) (firstArgs ++ secondArgs) key flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, KExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append firstRun secondRun

/-- Two V fragments compose silently through `and_v`. -/
theorem VExecution.and_v_v
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.and_v first second) (firstArgs ++ secondArgs) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun secondRun

/-- A B truth outcome from the second child passes through `and_v`. -/
theorem VExecution.and_v_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.and_v first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := secondExec
  exact ⟨result, firstExec.and_v_b frame, truth⟩

/-- `and_b` executes its B child, then its W child under that exact result, and
    finally decodes both operands for `OP_BOOLAND`. The returned boolean uses
    source-child order independently of the W wrapper's stack order. -/
theorem BExecution.and_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue) :
    BExecution (.and_b first second) (firstArgs ++ secondArgs)
      (boolToElement ((firstValue != 0) && (secondValue != 0))) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  cases order with
  | savedFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLAND] (firstResult :: secondResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) && (secondValue != 0)) :: rest)
              altStack) := by
        apply Eval.booland (a := firstValue) (b := secondValue)
        · exact decoded
        · exact Eval.done
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun
  | resultFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLAND] (secondResult :: firstResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) && (secondValue != 0)) :: rest)
              altStack) := by
        simpa [Bool.and_comm] using
          (Eval.booland secondResult firstResult secondValue firstValue rest []
            altStack flags ctx
            (.success
              (boolToElement ((secondValue != 0) && (firstValue != 0)) :: rest)
              altStack)
            decoded
            (Eval.done (stack :=
              boolToElement ((secondValue != 0) && (firstValue != 0)) :: rest)
              (altStack := altStack)))
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun

/-- `and_b`'s canonical result has the requested truth value once its decoded
    operands' nonzero tests establish that value. -/
theorem BExecution.and_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue)
    (truth : ((firstValue != 0) && (secondValue != 0)) = expected) :
    BExecutionOutcome (.and_b first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  refine ⟨boolToElement ((firstValue != 0) && (secondValue != 0)),
    firstExec.and_b secondExec decoded, ?_⟩
  exact (castToBool_boolToElement _).trans truth

/-- `or_b` has the same exact operand-order boundary as `and_b`, followed by
    `OP_BOOLOR`. -/
theorem BExecution.or_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue) :
    BExecution (.or_b first second) (firstArgs ++ secondArgs)
      (boolToElement ((firstValue != 0) || (secondValue != 0))) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  cases order with
  | savedFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLOR] (firstResult :: secondResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) || (secondValue != 0)) :: rest)
              altStack) := by
        apply Eval.boolor (a := firstValue) (b := secondValue)
        · exact decoded
        · exact Eval.done
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun
  | resultFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLOR] (secondResult :: firstResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) || (secondValue != 0)) :: rest)
              altStack) := by
        simpa [Bool.or_comm] using
          (Eval.boolor secondResult firstResult secondValue firstValue rest []
            altStack flags ctx
            (.success
              (boolToElement ((secondValue != 0) || (firstValue != 0)) :: rest)
              altStack)
            decoded
            (Eval.done (stack :=
              boolToElement ((secondValue != 0) || (firstValue != 0)) :: rest)
              (altStack := altStack)))
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun

/-- `or_b`'s normalized result has the requested truth value. -/
theorem BExecution.or_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue)
    (truth : ((firstValue != 0) || (secondValue != 0)) = expected) :
    BExecutionOutcome (.or_b first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  refine ⟨boolToElement ((firstValue != 0) || (secondValue != 0)),
    firstExec.or_b secondExec decoded, ?_⟩
  exact (castToBool_boolToElement _).trans truth

/-! ## Conditional connective composition -/

/-- A satisfying first child makes `or_c` skip its V child. The child-produced
    selector keeps its explicit MINIMALIF and truthiness premises. -/
theorem BExecution.or_c_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    VExecution (.or_c first second) firstArgs flags ctx := by
  have tail := ExecutesStackFrame.notifThen_skip
    (body := compile second) (inputs := []) (ctx := ctx)
    (compile_balancedControlFlow second) minimal truth
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstExec tail

/-- A dissatisfied first child makes `or_c` execute its V child. -/
theorem BExecution.or_c_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.or_c first second) (firstArgs ++ secondArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifThen_execute
    (compile_balancedControlFlow second) minimal falsy secondExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

/-- On the direct `or_d` path, `OP_IFDUP` preserves the satisfying first-child
    selector as the connector's exact B result. -/
theorem BExecution.or_d_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    BExecution (.or_d first second) firstArgs selector flags ctx := by
  intro rest altStack
  have firstRun := firstExec rest altStack
  have conditionalFrame := ExecutesStackFrame.notifThen_skip
    (body := compile second) (inputs := [selector]) (ctx := ctx)
    (compile_balancedControlFlow second) minimal truth
  have tailRun :
      Eval (.op .OP_IFDUP :: .op .OP_NOTIF ::
          compile second ++ [.op .OP_ENDIF])
        (selector :: rest) altStack flags ctx
        (.success (selector :: rest) altStack) := by
    exact Eval.ifdup_true selector rest altStack _ flags ctx _ truth
      (conditionalFrame rest altStack)
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun tailRun

/-- On the alternate `or_d` path, a false first result is consumed and the
    second child's exact B result becomes the connector result. -/
theorem BExecution.or_d_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.or_d first second) (firstArgs ++ secondArgs) result flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have conditionalFrame := ExecutesStackFrame.notifThen_execute
    (compile_balancedControlFlow second) minimal falsy secondExec
  have tailRun :
      Eval (.op .OP_IFDUP :: .op .OP_NOTIF ::
          compile second ++ [.op .OP_ENDIF])
        (selector :: secondArgs ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    exact Eval.ifdup_false selector (secondArgs ++ rest) altStack _ flags ctx _
      falsy (conditionalFrame rest altStack)
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun tailRun

theorem BExecutionOutcome.or_d_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    BExecutionOutcome (.or_d first second) firstArgs true flags ctx :=
  ⟨selector, firstExec.or_d_left minimal truth, truth⟩

theorem BExecutionOutcome.or_d_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.or_d first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := secondExec
  exact ⟨result, firstExec.or_d_right minimal falsy frame, truth⟩

/-- The canonical true selector chooses the first B branch of `or_i` and
    satisfies MINIMALIF for every flag set. -/
theorem BExecution.or_i_left
    {first second : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution first args result flags ctx) :
    BExecution (.or_i first second) (trueElement :: args) result flags ctx := by
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by native_decide) executed

/-- The canonical false selector chooses the second B branch of `or_i`. -/
theorem BExecution.or_i_right
    {first second : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution second args result flags ctx) :
    BExecution (.or_i first second) (falseElement :: args) result flags ctx := by
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by native_decide) executed

theorem KExecution.or_i_left
    {first second : CoreFragment} {args : Stack} {key : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution first args key flags ctx) :
    KExecution (.or_i first second) (trueElement :: args) key flags ctx := by
  simpa [KExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by native_decide) executed

theorem KExecution.or_i_right
    {first second : CoreFragment} {args : Stack} {key : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution second args key flags ctx) :
    KExecution (.or_i first second) (falseElement :: args) key flags ctx := by
  simpa [KExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by native_decide) executed

theorem VExecution.or_i_left
    {first second : CoreFragment} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution first args flags ctx) :
    VExecution (.or_i first second) (trueElement :: args) flags ctx := by
  simpa [VExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by native_decide) executed

theorem VExecution.or_i_right
    {first second : CoreFragment} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution second args flags ctx) :
    VExecution (.or_i first second) (falseElement :: args) flags ctx := by
  simpa [VExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by native_decide) executed

theorem BExecutionOutcome.or_i_left
    {first second : CoreFragment} {args : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome first args expected flags ctx) :
    BExecutionOutcome (.or_i first second) (trueElement :: args)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.or_i_left, truth⟩

theorem BExecutionOutcome.or_i_right
    {first second : CoreFragment} {args : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome second args expected flags ctx) :
    BExecutionOutcome (.or_i first second) (falseElement :: args)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.or_i_right, truth⟩

/-- A truthy first child selects Y, the second source child of `andor`. -/
theorem BExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.andor first second third) (firstArgs ++ secondArgs)
      result flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.append firstFrame tail

/-- A false first child selects Z, the third source child of `andor`. -/
theorem BExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : BExecution third thirdArgs result flags ctx) :
    BExecution (.andor first second third) (firstArgs ++ thirdArgs)
      result flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.append firstFrame tail

theorem KExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : KExecution second secondArgs key flags ctx) :
    KExecution (.andor first second third) (firstArgs ++ secondArgs)
      key flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, KExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem KExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : KExecution third thirdArgs key flags ctx) :
    KExecution (.andor first second third) (firstArgs ++ thirdArgs)
      key flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, KExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem VExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.andor first second third) (firstArgs ++ secondArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem VExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : VExecution third thirdArgs flags ctx) :
    VExecution (.andor first second third) (firstArgs ++ thirdArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem BExecutionOutcome.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.andor first second third) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, resultTruth⟩ := secondExec
  exact ⟨result, firstExec.andor_true minimal truth frame, resultTruth⟩

theorem BExecutionOutcome.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : BExecutionOutcome third thirdArgs expected flags ctx) :
    BExecutionOutcome (.andor first second third) (firstArgs ++ thirdArgs)
      expected flags ctx := by
  obtain ⟨result, frame, resultTruth⟩ := thirdExec
  exact ⟨result, firstExec.andor_false minimal falsy frame, resultTruth⟩

/-! ## Guarded wrapper composition -/

/-- Wrapper `d` duplicates its canonical true selector, consumes one copy in
    `OP_IF`, and runs a zero-argument V child while retaining the other copy as
    its B result. Balanced child compilation identifies the exact IF body. -/
theorem VExecution.d
    {fragment : CoreFragment} {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution fragment [] flags ctx) :
    BExecution (.d fragment) [trueElement] trueElement flags ctx := by
  intro rest altStack
  have childExec := executed (trueElement :: rest) altStack
  have truth : castToBool trueElement = true := by native_decide
  have split :
      splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some { branches := [compile fragment], after := [] } := by
    simpa using
      (splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := []))
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (trueElement :: trueElement :: rest) altStack flags ctx
        (.success (trueElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
        childExec
  simpa [BExecution, VExecution, ExecutesStackFrame, compile,
    compileWithKeyHash] using
    Eval.dup trueElement rest _ altStack flags ctx _ ifExec

/-- The canonical false selector skips the `d` child and remains as the exact
    false B result on every surrounding stack. -/
theorem d_dissatisfaction_execution
    (fragment : CoreFragment) (flags : ScriptFlags) (ctx : TxContext) :
    BExecution (.d fragment) [falseElement] falseElement flags ctx := by
  intro rest altStack
  have falsehood : castToBool falseElement = false := by native_decide
  have split :
      splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some { branches := [compile fragment], after := [] } := by
    simpa using
      (splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := []))
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (falseElement :: falseElement :: rest) altStack flags ctx
        (.success (falseElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, falsehood] using
        (Eval.done (stack := falseElement :: rest) (altStack := altStack))
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    Eval.dup falseElement rest _ altStack flags ctx _ ifExec

/-- A nonempty first runtime item makes `j` execute its B child. The explicit
    decode premise exposes the four-byte Script-number boundary of the
    `OP_SIZE OP_0NOTEQUAL` guard. -/
theorem BExecution.j
    {fragment : CoreFragment} {top result : StackElement} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment (top :: args) result flags ctx)
    (nonempty : top.size ≠ 0)
    (decoded : decodeScriptNum (scriptNat top.size) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat top.size)) :
    BExecution (.j fragment) (top :: args) result flags ctx := by
  intro rest altStack
  have childExec := executed rest altStack
  have nonzero : (Int.ofNat top.size != 0) = true := by
    simp [nonempty]
  have branchTrue :
      boolToElement (Int.ofNat top.size != 0) = trueElement := by
    rw [nonzero]
    rfl
  have truth : castToBool trueElement = true := by native_decide
  have split :
      splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some { branches := [compile fragment], after := [] } := by
    simpa using
      (splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := []))
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (trueElement :: top :: args ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
        childExec
  have ifExec' :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (boolToElement (Int.ofNat top.size != 0) :: top :: args ++ rest)
        altStack flags ctx (.success (result :: rest) altStack) := by
    simpa only [branchTrue] using ifExec
  have nonzeroExec :
      Eval (.op .OP_0NOTEQUAL :: .op .OP_IF ::
          compile fragment ++ [.op .OP_ENDIF])
        (scriptNat top.size :: top :: args ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    exact Eval.zeroNotEqual (scriptNat top.size) (Int.ofNat top.size)
      (top :: args ++ rest) altStack _ flags ctx _ decoded ifExec'
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using
    Eval.size top (args ++ rest) altStack _ flags ctx _ nonzeroExec

/-- `j` preserves the child's requested truth outcome whenever its first
    runtime item is nonempty and its encoded size satisfies the numeric guard. -/
theorem BExecutionOutcome.j
    {fragment : CoreFragment} {top : StackElement} {args : Stack}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment (top :: args) expected flags ctx)
    (nonempty : top.size ≠ 0)
    (decoded : decodeScriptNum (scriptNat top.size) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat top.size)) :
    BExecutionOutcome (.j fragment) (top :: args) expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.j nonempty decoded, truth⟩

/-- The canonical empty item takes `j`'s skipped branch and remains as the
    exact false B result without requiring any child execution premise. -/
theorem j_dissatisfaction_execution
    (fragment : CoreFragment) (flags : ScriptFlags) (ctx : TxContext) :
    BExecution (.j fragment) [falseElement] falseElement flags ctx := by
  intro rest altStack
  have decoded :
      decodeScriptNum (scriptNat falseElement.size) flags.minimalData
        maxArithmeticScriptNumBytes = .ok (Int.ofNat falseElement.size) := by
    change decodeScriptNum falseElement flags.minimalData
      maxArithmeticScriptNumBytes = .ok 0
    cases h : flags.minimalData <;> rfl
  have zero : (Int.ofNat falseElement.size != 0) = false := by native_decide
  have branchFalse :
      boolToElement (Int.ofNat falseElement.size != 0) = falseElement := by
    rw [zero]
    rfl
  have falsehood : castToBool falseElement = false := by native_decide
  have split :
      splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some { branches := [compile fragment], after := [] } := by
    simpa using
      (splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := []))
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (falseElement :: falseElement :: rest) altStack flags ctx
        (.success (falseElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, falsehood] using
        (Eval.done (stack := falseElement :: rest) (altStack := altStack))
  have ifExec' :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (boolToElement (Int.ofNat falseElement.size != 0) ::
          falseElement :: rest)
        altStack flags ctx (.success (falseElement :: rest) altStack) := by
    simpa only [branchFalse] using ifExec
  have nonzeroExec :
      Eval (.op .OP_0NOTEQUAL ::
          (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF]))
        (scriptNat falseElement.size :: falseElement :: rest)
        altStack flags ctx (.success (falseElement :: rest) altStack) := by
    exact Eval.zeroNotEqual (scriptNat falseElement.size)
      (Int.ofNat falseElement.size) (falseElement :: rest) altStack _ flags ctx _
      decoded ifExec'
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    Eval.size falseElement rest altStack _ flags ctx _ nonzeroExec

/-! ## Threshold composition -/

/-- Execution evidence for the W-type tail of a threshold. The accumulator is
    represented by its canonical Script-number bytes. Each child result is an
    exact Boolean element, while `BinaryDecoded` keeps the four-byte numeric
    premise for its following `OP_ADD` explicit. Argument frames are listed in
    source execution order. -/
inductive ThresholdTailExecution (flags : ScriptFlags) (ctx : TxContext) :
    Nat → List CoreFragment → List Stack → Nat → Prop where
  | nil (count : Nat) : ThresholdTailExecution flags ctx count [] [] count
  | cons {count total : Nat} {fragment : CoreFragment}
      {fragments : List CoreFragment} {args : Stack}
      {argumentFrames : List Stack} {truth : Bool} {order : WStackOrder}
      (executed : WExecution fragment args (boolToElement truth) order flags ctx)
      (decoded : order.BinaryDecoded flags (scriptNat count)
        (boolToElement truth) (Int.ofNat count) (Int.ofNat truth.toNat))
      (tail : ThresholdTailExecution flags ctx (count + truth.toNat)
        fragments argumentFrames total) :
      ThresholdTailExecution flags ctx count (fragment :: fragments)
        (args :: argumentFrames) total

/-- The threshold tail executes every W child followed by `OP_ADD`, preserving
    arbitrary stack suffixes and the alternate stack. -/
theorem ThresholdTailExecution.executes
    {flags : ScriptFlags} {ctx : TxContext} {count total : Nat}
    {fragments : List CoreFragment} {argumentFrames : List Stack}
    (executed : ThresholdTailExecution flags ctx count fragments
      argumentFrames total) :
    ExecutesStackFrame (compileThreshTail fragments)
      (scriptNat count :: argumentFrames.flatten) [scriptNat total] flags ctx := by
  induction executed with
  | nil count =>
      intro rest altStack
      simpa [compileThreshTail, compileThreshTailWithKeyHash,
        ExecutesStackFrame] using
        (Eval.done (stack := scriptNat count :: rest) (altStack := altStack))
  | @cons count total fragment fragments args argumentFrames truth order
      childExec decoded tail ih =>
      have added :
          ExecutesStackFrame (compile fragment ++ [.op .OP_ADD])
            (scriptNat count :: args)
            [scriptNat (count + truth.toNat)] flags ctx := by
        simpa [scriptNat] using childExec.addToSaved decoded
      have prefixFrame := added.withSuffix (suffix := argumentFrames.flatten)
      have combined := ExecutesStackFrame.append prefixFrame ih
      simpa [compile, compileThreshTail, compileThreshTailWithKeyHash,
        List.append_assoc] using combined

/-- A threshold executes its first B child, accumulates every W child result,
    then compares the final canonical accumulator bytes with the literal
    threshold bytes using `OP_EQUAL`. No numeric injectivity assumption is
    needed for the final comparison. -/
theorem BExecution.thresh
    {threshold : Nat} {first : CoreFragment} {fragments : List CoreFragment}
    {firstArgs : Stack} {argumentFrames : List Stack} {firstTruth : Bool}
    {total : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs (boolToElement firstTruth) flags ctx)
    (tailExec : ThresholdTailExecution flags ctx firstTruth.toNat fragments
      argumentFrames total) :
    BExecution (.thresh threshold (first :: fragments))
      (firstArgs ++ argumentFrames.flatten)
      (boolToElement (decide (scriptNat threshold = scriptNat total)))
      flags ctx := by
  have normalizedFirst :
      BExecution first firstArgs (scriptNat firstTruth.toNat) flags ctx := by
    cases firstTruth <;> simpa [boolToElement, scriptNat, scriptNum_zero,
      scriptNum_one] using firstExec
  have firstFrame :=
    normalizedFirst.withSuffix (suffix := argumentFrames.flatten)
  have childrenFrame := ExecutesStackFrame.append firstFrame tailExec.executes
  have compareFrame :
      ExecutesStackFrame [.pushNum threshold, .op .OP_EQUAL]
        [scriptNat total]
        [boolToElement (decide (scriptNat threshold = scriptNat total))]
        flags ctx := by
    intro rest altStack
    by_cases equal : scriptNat threshold = scriptNat total
    · have equal' : scriptNum (Int.ofNat threshold) =
          scriptNum (Int.ofNat total) := by
        simpa [scriptNat] using equal
      simpa [equal, equal', boolToElement] using
        (Eval.pushNum (Int.ofNat threshold) [.op .OP_EQUAL]
          (scriptNat total :: rest) altStack flags ctx _
          (Eval.equal_true (scriptNat threshold) (scriptNat total) rest []
            altStack flags ctx _ equal Eval.done))
    · have equal' : scriptNum (Int.ofNat threshold) ≠
          scriptNum (Int.ofNat total) := by
        simpa [scriptNat] using equal
      simpa [equal, equal', boolToElement] using
        (Eval.pushNum (Int.ofNat threshold) [.op .OP_EQUAL]
          (scriptNat total :: rest) altStack flags ctx _
          (Eval.equal_false (scriptNat threshold) (scriptNat total) rest []
            altStack flags ctx _ equal Eval.done))
  have complete := ExecutesStackFrame.append childrenFrame compareFrame
  simpa [BExecution, compile, compileWithKeyHash, compileThresh,
    compileThreshTail, compileThreshWithKeyHash, List.append_assoc] using complete

/-- Expose the threshold's requested truth outcome while retaining byte-level
    equality as the final `OP_EQUAL` premise. -/
theorem BExecution.threshOutcome
    {threshold : Nat} {first : CoreFragment} {fragments : List CoreFragment}
    {firstArgs : Stack} {argumentFrames : List Stack}
    {firstTruth expected : Bool} {total : Nat}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs (boolToElement firstTruth) flags ctx)
    (tailExec : ThresholdTailExecution flags ctx firstTruth.toNat fragments
      argumentFrames total)
    (comparison : decide (scriptNat threshold = scriptNat total) = expected) :
    BExecutionOutcome (.thresh threshold (first :: fragments))
      (firstArgs ++ argumentFrames.flatten) expected flags ctx := by
  refine ⟨boolToElement (decide (scriptNat threshold = scriptNat total)),
    firstExec.thresh tailExec, ?_⟩
  exact (castToBool_boolToElement _).trans comparison

/-! ## Legacy multisignature execution -/

/-- Legacy multisignature count literals up to the consensus public-key limit
    decode to their corresponding nonnegative integers under either
    minimal-data setting. -/
theorem decodeScriptNum_scriptNat_multi_count
    (count : Nat) (flags : ScriptFlags)
    (bounded : count ≤ maxPubKeysPerMultiSig) :
    decodeScriptNum (scriptNat count) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat count) := by
  have bounded' : count ≤ 20 := by
    simpa [maxPubKeysPerMultiSig] using bounded
  have options : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨
      count = 4 ∨ count = 5 ∨ count = 6 ∨ count = 7 ∨ count = 8 ∨
      count = 9 ∨ count = 10 ∨ count = 11 ∨ count = 12 ∨ count = 13 ∨
      count = 14 ∨ count = 15 ∨ count = 16 ∨ count = 17 ∨
      count = 18 ∨ count = 19 ∨ count = 20 := by
    omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases flags.minimalData <;> rfl

/-- Pushing the source-order key list leaves the decoder's top-first reversed
    public-key frame while preserving every surrounding stack suffix. -/
theorem compileKeyPushes_execution (keys : List PubKey) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesStackFrame (compileKeyPushes keys) []
      ((keys.map (fun key => key.bytes)).reverse) flags ctx := by
  induction keys with
  | nil =>
      intro rest altStack
      exact Eval.done
  | cons key keys ih =>
      intro rest altStack
      apply Eval.pushData
      simpa [List.map_append, List.append_assoc] using
        ih (key.bytes :: rest) altStack

private theorem exceptOkBind {ε α β} (value : α)
    (next : α → Except ε β) :
    (do let result ← Except.ok value; next result) = next value := by
  rfl

/-- Decode the exact canonical stack frame produced by the legacy `multi`
    compiler and its selected top-first signature arguments. -/
theorem decodeCheckMultiSigOperandsFor_multi
    {threshold : Nat} {keys : List PubKey} {signatures rest : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold) :
    decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest) =
      .ok {
        pubkeys := (keys.map (fun key => key.bytes)).reverse
        signatures := signatures
        dummy := some falseElement
        rest := rest } := by
  have decodeKeys := decodeScriptNum_scriptNat_multi_count keys.length flags
    keyBound
  have decodeThreshold := decodeScriptNum_scriptNat_multi_count threshold flags
    (Nat.le_trans thresholdBound keyBound)
  unfold decodeCheckMultiSigOperandsFor
  simp only [if_neg version]
  simp [decodeCheckMultiSigOperands]
  rw [exceptOkBind]
  rw [decodeKeys]
  rw [exceptOkBind]
  simp only [Int.ofNat_eq_natCast] at *
  simp [maxPubKeysPerMultiSig] at keyBound
  have keyNonnegative : ¬ ((keys.length : Int) < 0) := by omega
  have keyWithinLimit : ¬ ((20 : Int) < (keys.length : Int)) := by omega
  have thresholdNonnegative : ¬ ((threshold : Int) < 0) := by omega
  have thresholdWithinKeys : ¬ (keys.length < threshold) := by omega
  have enoughSignatures :
      ¬ ((threshold : Int) + (rest.length + 1) < threshold) := by omega
  simp [decodeThreshold, exceptOkBind, maxPubKeysPerMultiSig, signatureCount,
    keyNonnegative, keyWithinLimit, thresholdNonnegative, thresholdWithinKeys,
    enoughSignatures]

/-- A legacy `multi` consumes the selected signatures followed by the
    canonical historical dummy. Signature and public-key lists are both in
    the top-first order used by the evaluator. Failed checks require NULLFAIL;
    the canonical dummy discharges NULLDUMMY internally. -/
theorem BExecution.multi
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {result : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok result)
    (allowed : result = true ∨ nullFailSatisfied flags signatures) :
    BExecution (.multi threshold keys) (signatures ++ [falseElement])
      (boolToElement result) flags ctx := by
  intro rest altStack
  let operands : CheckMultiSigOperands := {
    pubkeys := (keys.map (fun key => key.bytes)).reverse
    signatures := signatures
    dummy := some falseElement
    rest := rest }
  have decoded : decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest) =
      .ok operands := by
    exact decodeCheckMultiSigOperandsFor_multi version keyBound thresholdBound
      signatureCount
  have dummyOk : checkMultiSigDummy flags (some falseElement) = .ok () := by
    simp [checkMultiSigDummy, nullDummySatisfied, stackElementEq, falseElement]
  have checked' : checkMultiSigFor checkSig flags ctx operands.signatures
      operands.pubkeys = .ok result := checked
  have checkExec : Eval [.op .OP_CHECKMULTISIG]
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest)
      altStack flags ctx
      (.success (boolToElement result :: rest) altStack) := by
    cases result with
    | false =>
        have nullFail : nullFailSatisfied flags signatures := by
          rcases allowed with impossible | satisfied
          · simp at impossible
          · exact satisfied
        simpa [operands, boolToElement] using
          (Eval.checkmultisig_failure
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx
            (.success (falseElement :: rest) altStack)
            decoded checked' nullFail dummyOk Eval.done)
    | true =>
        simpa [operands, boolToElement] using
          (Eval.checkmultisig_success
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx
            (.success (trueElement :: rest) altStack)
            decoded checked' dummyOk Eval.done)
  have keyExec := compileKeyPushes_execution keys flags ctx
    (scriptNat threshold :: signatures ++ falseElement :: rest) altStack
  have tailExec : Eval
      (compileKeyPushes keys ++ [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      (scriptNat threshold :: signatures ++ falseElement :: rest)
      altStack flags ctx
      (.success (boolToElement result :: rest) altStack) := by
    have pushedCount : Eval [.pushNum keys.length, .op .OP_CHECKMULTISIG]
        ((keys.map (fun key => key.bytes)).reverse ++
          (scriptNat threshold :: signatures ++ falseElement :: rest))
        altStack flags ctx
        (.success (boolToElement result :: rest) altStack) := by
      simpa [List.append_assoc] using
        (Eval.pushNum keys.length [.op .OP_CHECKMULTISIG]
          ((keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: signatures ++ falseElement :: rest)
          altStack flags ctx _ checkExec)
    exact Eval.append keyExec pushedCount
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using
    (Eval.pushNum threshold
      (compileKeyPushes keys ++ [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      (signatures ++ falseElement :: rest) altStack flags ctx _ tailExec)

/-- The false branch of legacy `multi` exposes the NULLFAIL premise directly. -/
theorem BExecution.multiFalse
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok false)
    (nullFail : nullFailSatisfied flags signatures) :
    BExecution (.multi threshold keys) (signatures ++ [falseElement])
      falseElement flags ctx := by
  simpa [boolToElement] using BExecution.multi version keyBound thresholdBound
    signatureCount checked (Or.inr nullFail)

/-- The canonical legacy `multi` dissatisfaction uses only empty signatures,
    so its failed check always satisfies NULLFAIL. -/
theorem multi_dissatisfaction_execution
    {threshold : Nat} {keys : List PubKey}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (checked : checkMultiSigFor checkSig flags ctx
      (List.replicate threshold falseElement)
      ((keys.map (fun key => key.bytes)).reverse) = .ok false) :
    BExecution (.multi threshold keys)
      (List.replicate threshold falseElement ++ [falseElement])
      falseElement flags ctx := by
  have nullFail : nullFailSatisfied flags
      (List.replicate threshold falseElement) := by
    right
    intro signature member
    have equal : signature = falseElement := List.eq_of_mem_replicate member
    subst signature
    rfl
  exact BExecution.multiFalse version keyBound thresholdBound
    (by simp) checked nullFail

/-! ## Tapscript multisignature execution -/

/-- Exact execution evidence for the CHECKSIGADD tail of `multi_a`. Keys and
    signatures are both in source execution order. Every step retains the
    Tapscript count decoder and version-aware signature-check result as
    explicit premises, while the accumulator is an `Int`. -/
inductive CheckSigAddTailExecution (flags : ScriptFlags) (ctx : TxContext) :
    Int → List PubKey → Stack → Int → Prop where
  | nil (count : Int) :
      CheckSigAddTailExecution flags ctx count [] [] count
  | cons {count total : Int} {key : PubKey} {keys : List PubKey}
      {signature : StackElement} {signatures : Stack} {truth : Bool}
      (decoded : decodeCheckSigAddCount flags ctx (scriptNum count) = .ok count)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        signature key.bytes = .ok truth)
      (tail : CheckSigAddTailExecution flags ctx
        (count + Int.ofNat truth.toNat) keys signatures total) :
      CheckSigAddTailExecution flags ctx count (key :: keys)
        (signature :: signatures) total

/-- A CHECKSIGADD tail consumes source-order signatures below its accumulator
    and leaves the exact final canonical Script-number while preserving both
    surrounding stacks. -/
theorem CheckSigAddTailExecution.executes
    {flags : ScriptFlags} {ctx : TxContext} {count total : Int}
    {keys : List PubKey} {signatures : Stack}
    (executed : CheckSigAddTailExecution flags ctx count keys signatures total) :
    ExecutesStackFrame (compileCheckSigAddTail keys)
      (scriptNum count :: signatures) [scriptNum total] flags ctx := by
  induction executed with
  | nil count =>
      intro rest altStack
      exact Eval.done
  | @cons count total key keys signature signatures truth decoded checked tail ih =>
      intro rest altStack
      apply Eval.pushData
      cases truth with
      | false =>
          apply Eval.checksigadd_failure (count := count)
          · exact decoded
          · exact checked
          · simpa using ih rest altStack
      | true =>
          apply Eval.checksigadd_success (count := count)
          · exact decoded
          · exact checked
          · simpa using ih rest altStack

/-- The nonempty CHECKSIG/CHECKSIGADD compiler consumes one source-order
    signature per source-order key and exposes the tail's exact accumulator. -/
theorem compileCheckSigAdd_execution
    {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total) :
    ExecutesStackFrame (compileCheckSigAdd (firstKey :: keys))
      (firstSignature :: signatures) [scriptNum total] flags ctx := by
  intro rest altStack
  apply Eval.pushData
  cases firstTruth with
  | false =>
      apply Eval.checksig_failure
      · exact checked
      · simpa [compileCheckSigAddTail, List.append_assoc, scriptNum_zero] using
          tail.executes rest altStack
  | true =>
      apply Eval.checksig_success
      · exact checked
      · simpa [compileCheckSigAddTail, List.append_assoc, scriptNum_one] using
          tail.executes rest altStack

/-- A nonempty `multi_a` executes only under the explicit Tapscript boundary,
    computes the CHECKSIG/CHECKSIGADD accumulator, then compares it numerically
    with the threshold. Both accumulator and final NUMEQUAL decodes remain
    explicit rather than being inferred from well-formedness. -/
theorem BExecution.multiA
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (_version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total)) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures)
      (boolToElement (Int.ofNat threshold == total)) flags ctx := by
  have children := compileCheckSigAdd_execution checked tail
  have comparison : ExecutesStackFrame [.pushNum threshold, .op .OP_NUMEQUAL]
      [scriptNum total] [boolToElement (Int.ofNat threshold == total)]
      flags ctx := by
    intro rest altStack
    exact Eval.pushNum threshold [.op .OP_NUMEQUAL] (scriptNum total :: rest)
      altStack flags ctx _
      (Eval.numequal (scriptNat threshold) (scriptNum total)
        (Int.ofNat threshold) total rest [] altStack flags ctx _ decoded Eval.done)
  have complete := ExecutesStackFrame.append children comparison
  simpa [BExecution, compile, compileWithKeyHash] using complete

/-- Expose the requested Boolean result of the final NUMEQUAL comparison. -/
theorem BExecution.multiAOutcome
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth expected : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = expected) :
    BExecutionOutcome (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) expected flags ctx := by
  refine ⟨boolToElement (Int.ofNat threshold == total),
    BExecution.multiA version checked tail decoded, ?_⟩
  exact (castToBool_boolToElement _).trans comparison

/-- A final equality result gives the exact canonical true B result. -/
theorem BExecution.multiATrue
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = true) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) trueElement flags ctx := by
  have executed := BExecution.multiA version checked tail decoded
  rw [comparison] at executed
  exact executed

/-- A failed final numeric equality gives the exact canonical false B result. -/
theorem BExecution.multiAFalse
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = false) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) falseElement flags ctx := by
  have executed := BExecution.multiA version checked tail decoded
  rw [comparison] at executed
  exact executed

/-- Empty signatures keep a CHECKSIGADD tail accumulator at zero. The exact
    empty-signature encoding result stays explicit for every key. -/
theorem CheckSigAddTailExecution.allFalse
    {flags : ScriptFlags} {ctx : TxContext} (keys : List PubKey)
    (version : ctx.sigVersion = .tapscript)
    (checked : ∀ key ∈ keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        falseElement key.bytes = .ok false) :
    CheckSigAddTailExecution flags ctx 0 keys
      (List.replicate keys.length falseElement) 0 := by
  induction keys with
  | nil => exact .nil 0
  | cons key keys ih =>
      rw [List.length_cons, List.replicate_succ]
      apply CheckSigAddTailExecution.cons (truth := false)
      · simp only [decodeCheckSigAddCount, version, ne_eq,
          not_true_eq_false, ↓reduceIte, scriptNum_zero]
        cases flags.minimalData <;> rfl
      · exact checked key (by simp)
      · simpa using ih (fun child member => checked child (by simp [member]))

/-- The canonical all-empty `multi_a` dissatisfaction stays at accumulator
    zero and returns false for every positive threshold. -/
theorem multiA_dissatisfaction_execution
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (positive : threshold ≠ 0)
    (firstChecked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      falseElement firstKey.bytes = .ok false)
    (tailChecked : ∀ key ∈ keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        falseElement key.bytes = .ok false)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      falseElement = .ok (Int.ofNat threshold, 0)) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (List.replicate (firstKey :: keys).length falseElement)
      falseElement flags ctx := by
  have tail := CheckSigAddTailExecution.allFalse keys version tailChecked
  have executed := BExecution.multiA (threshold := threshold) version
    firstChecked tail decoded
  simpa [List.replicate_succ, boolToElement, positive] using executed

/-! ## Primitive execution contracts -/

/-- `1` needs no arguments and leaves the canonical true element. -/
theorem one_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .one [] trueElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_one] using
    (Eval.pushNum 1 [] rest altStack flags ctx
      (.success (trueElement :: rest) altStack)
      (Eval.done (stack := trueElement :: rest) (altStack := altStack)))

/-- `0` needs no arguments and leaves the canonical false element. -/
theorem zero_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .zero [] falseElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_zero] using
    (Eval.pushNum 0 [] rest altStack flags ctx
      (.success (falseElement :: rest) altStack)
      (Eval.done (stack := falseElement :: rest) (altStack := altStack)))

/-- `pk_k` needs no arguments of its own and leaves its exact public key. -/
theorem pk_k_execution (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    KExecution (.pk_k key) [] key.bytes flags ctx := by
  intro rest altStack
  simpa [KExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushDataNext (data := key.bytes)
      (Eval.done (stack := key.bytes :: rest) (altStack := altStack)))

/-- `pk_h` consumes the revealed key, verifies its model HASH160, and leaves
    that same key for a following signature check. -/
theorem pk_h_execution (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    KExecution (.pk_h key) [key.bytes] key.bytes flags ctx := by
  intro rest altStack
  simp only [compile, compileWithKeyHash, modelKeyHash, Hash160.ofBytes]
  apply Eval.dup
  apply Eval.op_hash160
  apply Eval.pushDataNext
  apply Eval.equalverify_success
  · rfl
  · exact Eval.done

/-- A matching 32-byte preimage executes its hashlock to the canonical true
    element while preserving arbitrary surrounding stacks. -/
theorem hash_satisfaction_execution
    {lock : HashLock} {preimage : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (matching : lock.Matches preimage) :
    BExecution lock.fragment [preimage] trueElement flags ctx := by
  rcases matching with ⟨size, digest⟩
  cases lock with
  | sha256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_sha256
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | hash256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash256
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | ripemd160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_ripemd160
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | hash160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash160
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done

/-- A mismatching 32-byte value executes its hashlock to the canonical false
    element; an arbitrary-length mismatch would instead abort at `EQUALVERIFY`. -/
theorem hash_dissatisfaction_execution
    {lock : HashLock} {nonPreimage : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (mismatches : lock.Mismatches nonPreimage) :
    BExecution lock.fragment [nonPreimage] falseElement flags ctx := by
  rcases mismatches with ⟨size, digest⟩
  cases lock with
  | sha256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_sha256
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | hash256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash256
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | ripemd160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_ripemd160
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | hash160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash160
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done

/-- A satisfied relative timelock preserves arbitrary surrounding stacks and
    leaves its compiler-produced numeric operand. -/
theorem older_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : sequenceSatisfied n ctx) :
    BExecution (.older n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKSEQUENCEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checksequenceverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- A satisfied absolute timelock has the corresponding arbitrary-stack
    execution contract. -/
theorem after_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : locktimeSatisfied n ctx) :
    BExecution (.after n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKLOCKTIMEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checklocktimeverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- The basic fragment cases whose witness algorithms need no numeric
    well-formedness premise. Timelocks have separate theorems below because
    their compiled Script-number must also satisfy the five-byte limit. -/
inductive BasicSatisfactionFragment : CoreFragment → Prop where
  | one : BasicSatisfactionFragment .one
  | cPkK (key : PubKey) : BasicSatisfactionFragment (.c (.pk_k key))
  | cPkH (key : PubKey) : BasicSatisfactionFragment (.c (.pk_h key))
  | sha256 (hash : Hash256) : BasicSatisfactionFragment (.sha256 hash)
  | hash256 (hash : Hash256) : BasicSatisfactionFragment (.hash256 hash)
  | ripemd160 (hash : Hash160) : BasicSatisfactionFragment (.ripemd160 hash)
  | hash160 (hash : Hash160) : BasicSatisfactionFragment (.hash160 hash)

/-- A witness returned for a supported basic fragment has a satisfying
    arbitrary-stack B execution. Cryptographic and byte-encoding assumptions
    are kept at this execution boundary rather than baked into the frame API. -/
theorem satisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (generated : satisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack true flags env.txCtx := by
  cases supported with
  | one =>
      simp [satisfy] at generated
      subst witness
      exact ⟨trueElement, by simpa using one_execution flags env.txCtx,
        by native_decide⟩
  | cPkK key =>
      cases signatureFor : env.signatureFor key with
      | none => simp [satisfy, keyCandidates, signatureFor] at generated
      | some signature =>
          simp [satisfy, keyCandidates, signatureFor] at generated
          subst witness
          have verified := sound.signatureValid signatureFor
          have checked := checkSigWithEncoding_true
            (encodings key signature signatureFor) verified
          refine ⟨trueElement, ?_, by native_decide⟩
          change BExecution (.c (.pk_k key)) [signature]
            trueElement flags env.txCtx
          simpa [boolToElement] using
            (KExecution.c (pk_k_execution key flags env.txCtx) checked)
  | cPkH key =>
      cases signatureFor : env.signatureFor key with
      | none => simp [satisfy, keyCandidates, signatureFor] at generated
      | some signature =>
          simp [satisfy, keyCandidates, signatureFor] at generated
          subst witness
          have verified := sound.signatureValid signatureFor
          have checked := checkSigWithEncoding_true
            (encodings key signature signatureFor) verified
          refine ⟨trueElement, ?_, by native_decide⟩
          change BExecution (.c (.pk_h key)) [key.bytes, signature]
            trueElement flags env.txCtx
          simpa [boolToElement] using
            (KExecution.c (pk_h_execution key flags env.txCtx) checked)
  | sha256 hash =>
      cases preimageFor : env.preimageFor (.sha256 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by native_decide⟩
  | hash256 hash =>
      cases preimageFor : env.preimageFor (.hash256 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by native_decide⟩
  | ripemd160 hash =>
      cases preimageFor : env.preimageFor (.ripemd160 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by native_decide⟩
  | hash160 hash =>
      cases preimageFor : env.preimageFor (.hash160 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by native_decide⟩

/-- Every witness returned for a supported basic fragment is accepted by its
    compiled script under the environment transaction and modeled flags,
    provided the supplied material also passes the selected encoding checks. -/
theorem satisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfy m env = some witness) :
    Accepts ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_basic_execution supported sound encodings generated).cleanStackResult⟩

/-- The witness returned for a satisfied relative timelock has the reusable B
    execution contract before final clean-stack acceptance is imposed. -/
theorem satisfy_older_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    BExecutionOutcome (.older n) witness.toInitialStack true flags env.txCtx := by
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · simp [satisfy, satisfied] at generated
    subst witness
    exact ⟨scriptNum n, by simpa using older_execution decoded satisfied, positive⟩
  · simp [satisfy, satisfied] at generated

/-- A returned `older` witness is accepted whenever its compiler-produced
    numeric operand is valid and truthy. `WellFormed` supplies these numeric
    premises when this lemma is lifted into the general correctness theorem. -/
theorem satisfy_older_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    Accepts ctx (compile (.older n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_older_execution decoded positive generated).cleanStackResult⟩

/-- The witness returned for a satisfied absolute timelock likewise executes
    over arbitrary surrounding stacks. -/
theorem satisfy_after_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    BExecutionOutcome (.after n) witness.toInitialStack true flags env.txCtx := by
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · simp [satisfy, satisfied] at generated
    subst witness
    exact ⟨scriptNum n, by simpa using after_execution decoded satisfied, positive⟩
  · simp [satisfy, satisfied] at generated

/-- Absolute timelocks use the same transaction predicate and numeric boundary
    as relational Script execution. -/
theorem satisfy_after_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    Accepts ctx (compile (.after n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_after_execution decoded positive generated).cleanStackResult⟩

/-- The raw hash dissatisfaction is a canonical DONTUSE candidate, but its
    retained witness still has an exact false execution contract. -/
theorem hash_dsat_candidate_execution
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).dsat =
        .dontUse [env.nonPreimageFor lock] false .canonical ∧
      BExecution lock.fragment [env.nonPreimageFor lock] falseElement
        flags env.txCtx := by
  constructor
  · cases lock <;> rfl
  · exact hash_dissatisfaction_execution
      (sound.nonPreimageMismatches lock)

/-- A returned basic dissatisfaction has a false B execution over every
    surrounding main and alternate stack. -/
theorem dissatisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨
      (∃ key, m = .c (.pk_k key)) ∨
      (∃ key, m = .c (.pk_h key)))
    (sound : env.Sound)
    (keys : ∀ key,
      (m = .c (.pk_k key) ∨ m = .c (.pk_h key)) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (generated : dissatisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack false flags env.txCtx := by
  rcases supported with rfl | ⟨key, rfl⟩ | ⟨key, rfl⟩
  · simp [dissatisfy] at generated
    subst witness
    exact ⟨falseElement, by simpa using zero_execution flags env.txCtx,
      by native_decide⟩
  · simp [dissatisfy, keyCandidates] at generated
    subst witness
    have rejected := sound.emptySignatureInvalid key
    have checked := checkSigWithEncoding_empty (keys key (Or.inl rfl)) rejected
    refine ⟨falseElement, ?_, by native_decide⟩
    change BExecution (.c (.pk_k key)) [falseElement] falseElement flags env.txCtx
    simpa [boolToElement] using
      (KExecution.c (pk_k_execution key flags env.txCtx) checked)
  · simp [dissatisfy, keyCandidates] at generated
    subst witness
    have rejected := sound.emptySignatureInvalid key
    have checked := checkSigWithEncoding_empty (keys key (Or.inr rfl)) rejected
    refine ⟨falseElement, ?_, by native_decide⟩
    change BExecution (.c (.pk_h key)) [key.bytes, falseElement]
      falseElement flags env.txCtx
    simpa [boolToElement] using
      (KExecution.c (pk_h_execution key flags env.txCtx) checked)

/-- Every witness returned for a supported basic dissatisfiable fragment
    executes successfully to a clean false result when the fragment's key
    passes the public-key encoding check, even with an empty signature. -/
theorem dissatisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨
      (∃ key, m = .c (.pk_k key)) ∨
      (∃ key, m = .c (.pk_h key)))
    (sound : env.Sound)
    (keys : ∀ key,
      (m = .c (.pk_k key) ∨ m = .c (.pk_h key)) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : dissatisfy m env = some witness) :
    Dissatisfies ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (dissatisfy_basic_execution supported sound keys generated).cleanStackResult⟩

end LeanMiniscript.Miniscript
