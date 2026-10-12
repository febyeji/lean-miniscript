import LeanMiniscript.Script.BigStepProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Composable execution frames

Exact Script execution frames compose over a protected main-stack suffix and
alternate stack. Conditional frame lemmas expose the selected balanced branch.
Inputs and outputs use top-first runtime order.
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

end LeanMiniscript.Miniscript
