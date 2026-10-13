import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Resource-aware connectors: execution frames

Resource frames for the boolean opcodes, `IFDUP`, branch selection in stack and
opcode path summaries, and the `or_i`/`andor` branch resources.

Some helpers here were `private` in the former single-file
`SatisfactionResourceConnectorProofs` module. They are visible only so that
sibling submodules can use them; treat them as internal proof helpers, not
stable API.
-/

theorem boolAndFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesResourceFrame [.op .OP_BOOLAND] (order.outputs saved result)
      [boolToElement ((savedValue != 0) && (resultValue != 0))]
      flags ctx StackTraceBound.binary 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases order with
    | savedFirst =>
        exact Eval.booland saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
    | resultFirst =>
        simpa [Bool.and_comm, WStackOrder.outputs] using
          (Eval.booland result saved resultValue savedValue rest [] altStack
            flags ctx _ decoded Eval.done)
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · simp [StackTraceBound.binary]
  · simp [executedMultiSigKeyCharge]

theorem boolOrFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesResourceFrame [.op .OP_BOOLOR] (order.outputs saved result)
      [boolToElement ((savedValue != 0) || (resultValue != 0))]
      flags ctx StackTraceBound.binary 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases order with
    | savedFirst =>
        exact Eval.boolor saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
    | resultFirst =>
        simpa [Bool.or_comm, WStackOrder.outputs] using
          (Eval.boolor result saved resultValue savedValue rest [] altStack
            flags ctx _ decoded Eval.done)
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · simp [StackTraceBound.binary]
  · simp [executedMultiSigKeyCharge]

theorem ifdupTrueFrame
    {value : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (truth : castToBool value = true) :
    ExecutesResourceFrame [.op .OP_IFDUP] [value] [value, value]
      flags ctx StackTraceBound.ifdupTrue 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.ifdup_true value rest altStack [] flags ctx _ truth Eval.done
  · simp [StackTraceBound.ifdupTrue]
  · simp [StackTraceBound.ifdupTrue]
  · simp [StackTraceBound.ifdupTrue]
  · simp [executedMultiSigKeyCharge]

theorem ifdupFalseFrame
    {value : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (falsy : castToBool value = false) :
    ExecutesResourceFrame [.op .OP_IFDUP] [value] [value]
      flags ctx StackTraceBound.ifdupFalse 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.ifdup_false value rest altStack [] flags ctx _ falsy Eval.done
  · simp [StackTraceBound.ifdupFalse]
  · simp [StackTraceBound.ifdupFalse]
  · simp [StackTraceBound.ifdupFalse]
  · simp [executedMultiSigKeyCharge]

theorem stackChoiceLeft
    {left right : StackTraceSet} {trace : StackTraceBound}
    (selected : left = some trace) :
    ∃ upper, StackTraceSet.choice left right = some upper ∧
      trace.netDiff ≤ upper.netDiff ∧ trace.exec ≤ upper.exec := by
  subst left
  cases right with
  | none => exact ⟨trace, rfl, Int.le_refl _, Int.le_refl _⟩
  | some other =>
      exact ⟨{ netDiff := max trace.netDiff other.netDiff
               exec := max trace.exec other.exec }, rfl,
        Int.le_max_left _ _, Int.le_max_left _ _⟩

theorem stackChoiceRight
    {left right : StackTraceSet} {trace : StackTraceBound}
    (selected : right = some trace) :
    ∃ upper, StackTraceSet.choice left right = some upper ∧
      trace.netDiff ≤ upper.netDiff ∧ trace.exec ≤ upper.exec := by
  subst right
  cases left with
  | none => exact ⟨trace, rfl, Int.le_refl _, Int.le_refl _⟩
  | some other =>
      exact ⟨{ netDiff := max other.netDiff trace.netDiff
               exec := max other.exec trace.exec }, rfl,
        Int.le_max_right _ _, Int.le_max_right _ _⟩

theorem opChoiceLeft
    {left right : PathMaximum} {value : Nat} (selected : left = some value) :
    ∃ upper, PathMaximum.choice left right = some upper ∧ value ≤ upper := by
  subst left
  cases right with
  | none => exact ⟨value, rfl, Nat.le_refl _⟩
  | some other => exact ⟨max value other, rfl, Nat.le_max_left _ _⟩

theorem opChoiceRight
    {left right : PathMaximum} {value : Nat} (selected : right = some value) :
    ∃ upper, PathMaximum.choice left right = some upper ∧ value ≤ upper := by
  subst right
  cases left with
  | none => exact ⟨value, rfl, Nat.le_refl _⟩
  | some other => exact ⟨max other value, rfl, Nat.le_max_right _ _⟩

/-- Sequential stack-trace composition is associative. -/
theorem StackTraceBound.sequential_assoc (first second third : StackTraceBound) :
    (first.sequential second).sequential third =
      first.sequential (second.sequential third) := by
  simp only [StackTraceBound.sequential, StackTraceBound.mk.injEq]
  omega

/-- A branch opcode followed by an empty trace is just the branch opcode. -/
theorem StackTraceBound.branch_sequential_empty :
    StackTraceBound.branch.sequential StackTraceBound.empty =
      StackTraceBound.branch := by
  decide

/-- Raise the trace of the second component of a sequential frame bound. -/
theorem ExecutesResourceFrame.monoSequentialRight
    {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {left trace upper : StackTraceBound} {dynamic upperDynamic : Nat}
    (executed : ExecutesResourceFrame script inputs outputs flags ctx
      (left.sequential trace) dynamic)
    (netDiff_le : trace.netDiff ≤ upper.netDiff)
    (exec_le : trace.exec ≤ upper.exec)
    (dynamic_le : dynamic ≤ upperDynamic) :
    ExecutesResourceFrame script inputs outputs flags ctx
      (left.sequential upper) upperDynamic :=
  executed.mono
    (by simp only [StackTraceBound.sequential]; omega)
    (by simp only [StackTraceBound.sequential]; omega) dynamic_le

/-- Raise the trace of the first component of a sequential frame bound. -/
theorem ExecutesResourceFrame.monoSequentialLeft
    {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace upper right : StackTraceBound} {dynamic upperDynamic : Nat}
    (executed : ExecutesResourceFrame script inputs outputs flags ctx
      (trace.sequential right) dynamic)
    (netDiff_le : trace.netDiff ≤ upper.netDiff)
    (exec_le : trace.exec ≤ upper.exec)
    (dynamic_le : dynamic ≤ upperDynamic) :
    ExecutesResourceFrame script inputs outputs flags ctx
      (upper.sequential right) upperDynamic :=
  executed.mono
    (by simp only [StackTraceBound.sequential]; omega)
    (by simp only [StackTraceBound.sequential]; omega) dynamic_le

/-- Execute `IF body ENDIF`, entering `body` exactly when the selector is
    true. -/
theorem ifThenFrame
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesResourceFrame
      (if castToBool selector then body else []) inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame (.op .OP_IF :: (body ++ [.op .OP_ENDIF]))
      (selector :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
  let frame : ConditionalFrame := { branches := [body], after := [] }
  have split : splitConditional (body ++ [.op .OP_ENDIF]) = some frame := by
    simpa [frame] using splitConditional_balanced_ifThen balanced (suffix := [])
  apply ExecutesResourceFrame.ifSelected split minimal
  revert selected
  cases castToBool selector <;> intro selected <;>
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected

/-- Execute `NOTIF body ENDIF`, entering `body` exactly when the selector is
    false. -/
theorem notifThenFrame
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesResourceFrame
      (if castToBool selector then [] else body) inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame (.op .OP_NOTIF :: (body ++ [.op .OP_ENDIF]))
      (selector :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
  let frame : ConditionalFrame := { branches := [body], after := [] }
  have split : splitConditional (body ++ [.op .OP_ENDIF]) = some frame := by
    simpa [frame] using splitConditional_balanced_ifThen balanced (suffix := [])
  apply ExecutesResourceFrame.notifSelected split minimal
  revert selected
  cases castToBool selector <;> intro selected <;>
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected

/-- Execute the branch of an `IF ... ELSE ... ENDIF` selected by `selector`. -/
private theorem ifElseFrame
    {firstScript secondScript : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (firstBalanced : BalancedControlFlow firstScript)
    (secondBalanced : BalancedControlFlow secondScript)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesResourceFrame
      (if castToBool selector then firstScript else secondScript)
      inputs outputs flags ctx trace dynamic) :
    ExecutesResourceFrame
      ([.op .OP_IF] ++ firstScript ++ [.op .OP_ELSE] ++ secondScript ++
        [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
  let frame : ConditionalFrame := {
    branches := [firstScript, secondScript]
    after := [] }
  have split : splitConditional
      (firstScript ++ [.op .OP_ELSE] ++ secondScript ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifElse firstBalanced
      secondBalanced
  have selected' : ExecutesResourceFrame
      (frame.select (castToBool selector)) inputs outputs flags ctx
      trace dynamic := by
    revert selected
    cases castToBool selector <;> intro selected <;>
      simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
        selected
  simpa using ExecutesResourceFrame.ifSelected split minimal selected'

/-- Bound an `or_i` branch frame by the public path choice between the two
    children's selected summaries. -/
private theorem orIResources_of_choice
    {first second : CoreFragment} {inputs outputs : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (raw : ExecutesResourceFrame (compile (.or_i first second)) inputs outputs
      flags ctx (StackTraceBound.branch.sequential trace) dynamic)
    (stackChoice : ∃ upper, StackTraceSet.choice
      (selectedStackSummary first expected)
      (selectedStackSummary second expected) = some upper ∧
        trace.netDiff ≤ upper.netDiff ∧ trace.exec ≤ upper.exec)
    (opChoice : ∃ upper, PathMaximum.choice
      (selectedOpSummary first expected)
      (selectedOpSummary second expected) = some upper ∧ dynamic ≤ upper) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.or_i first second)) inputs outputs
        flags ctx upperTrace upperDynamic ∧
      selectedStackSummary (.or_i first second) expected = some upperTrace ∧
      selectedOpSummary (.or_i first second) expected = some upperDynamic := by
  obtain ⟨childUpper, choiceStack, netBound, execBound⟩ := stackChoice
  obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ := opChoice
  refine ⟨StackTraceBound.branch.sequential childUpper, upperDynamic,
    raw.monoSequentialRight netBound execBound dynamicBound, ?_, ?_⟩
  · cases expected <;>
      simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some StackTraceBound.branch) summary) choiceStack
  · cases expected <;>
      simpa [selectedOpSummary, opPathBounds] using choiceOps

theorem orILeftResources
    {first second : CoreFragment} {inputs outputs : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (resources : ExecutesResourceFrame (compile first) inputs outputs flags ctx
      trace dynamic)
    (stackSelected : selectedStackSummary first expected = some trace)
    (opSelected : selectedOpSummary first expected = some dynamic) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.or_i first second))
        (trueElement :: inputs) outputs flags ctx upperTrace upperDynamic ∧
      selectedStackSummary (.or_i first second) expected = some upperTrace ∧
      selectedOpSummary (.or_i first second) expected = some upperDynamic := by
  have raw : ExecutesResourceFrame (compile (.or_i first second))
      (trueElement :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
    simpa [compile, compileWithKeyHash] using ifElseFrame
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg)
      (selected := by simpa using resources)
  exact orIResources_of_choice raw (stackChoiceLeft stackSelected)
    (opChoiceLeft opSelected)

theorem orIRightResources
    {first second : CoreFragment} {inputs outputs : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (resources : ExecutesResourceFrame (compile second) inputs outputs flags ctx
      trace dynamic)
    (stackSelected : selectedStackSummary second expected = some trace)
    (opSelected : selectedOpSummary second expected = some dynamic) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.or_i first second))
        (falseElement :: inputs) outputs flags ctx upperTrace upperDynamic ∧
      selectedStackSummary (.or_i first second) expected = some upperTrace ∧
      selectedOpSummary (.or_i first second) expected = some upperDynamic := by
  have raw : ExecutesResourceFrame (compile (.or_i first second))
      (falseElement :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
    simpa [compile, compileWithKeyHash] using ifElseFrame
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg)
      (selected := by simpa using resources)
  exact orIResources_of_choice raw (stackChoiceRight stackSelected)
    (opChoiceRight opSelected)

/-- Execute the condition of `andor` followed by the branch its result
    selects through `NOTIF ... ELSE ... ENDIF`. -/
private theorem andorFrame
    {first second third : CoreFragment}
    {firstInputs branchInputs outputs : Stack} {selector : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    {firstTrace branchTrace : StackTraceBound}
    {firstDynamic branchDynamic : Nat}
    (firstResources : ExecutesResourceFrame (compile first) firstInputs
      [selector] flags ctx firstTrace firstDynamic)
    (branchResources : ExecutesResourceFrame
      (if castToBool selector then compile second else compile third)
      branchInputs outputs flags ctx branchTrace branchDynamic)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector) :
    ExecutesResourceFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx
      ((firstTrace.sequential StackTraceBound.branch).sequential branchTrace)
      (firstDynamic + branchDynamic) := by
  let frame : ConditionalFrame := {
    branches := [compile third, compile second]
    after := [] }
  have split : splitConditional
      (compile third ++ [.op .OP_ELSE] ++ compile second ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifElse
      (compile_balancedControlFlow third) (compile_balancedControlFlow second)
  have selected : ExecutesResourceFrame
      (frame.select (!castToBool selector)) branchInputs outputs flags ctx
      branchTrace branchDynamic := by
    revert branchResources
    cases castToBool selector <;> intro branchResources <;>
      simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
        branchResources
  have conditional := ExecutesResourceFrame.notifSelected split minimal selected
  have concrete := (firstResources.withSuffix
    (suffix := branchInputs)).append conditional
  simpa [compile, compileWithKeyHash, frame, List.append_assoc,
    StackTraceBound.sequential_assoc] using concrete

private theorem stackChoice_comm (left right : StackTraceSet) :
    StackTraceSet.choice left right = StackTraceSet.choice right left := by
  cases left <;> cases right <;> simp [StackTraceSet.choice, Int.max_comm]

private theorem opChoice_comm (left right : PathMaximum) :
    PathMaximum.choice left right = PathMaximum.choice right left := by
  cases left <;> cases right <;> simp [PathMaximum.choice, Nat.max_comm]

/-- Bound an `andor` frame by the public path choice between the false
    (`third`) and true (`second`) continuations of the condition. -/
private theorem andorResources_of_choice
    {first second third : CoreFragment} {inputs outputs : Stack}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (executed : ExecutesResourceFrame (compile (.andor first second third))
      inputs outputs flags ctx trace dynamic)
    (stackChoice : ∃ upper, StackTraceSet.choice
      (StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (selectedStackSummary third expected))
      (StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.branch)) (selectedStackSummary second expected)) =
        some upper ∧ trace.netDiff ≤ upper.netDiff ∧ trace.exec ≤ upper.exec)
    (opChoice : ∃ upper, PathMaximum.choice
      (PathMaximum.sequential (opPathBounds first).dsat
        (selectedOpSummary third expected))
      (PathMaximum.sequential (opPathBounds first).sat
        (selectedOpSummary second expected)) = some upper ∧ dynamic ≤ upper) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.andor first second third))
        inputs outputs flags ctx upperTrace upperDynamic ∧
      selectedStackSummary (.andor first second third) expected =
        some upperTrace ∧
      selectedOpSummary (.andor first second third) expected =
        some upperDynamic := by
  obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ := stackChoice
  obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ := opChoice
  refine ⟨upperTrace, upperDynamic,
    executed.mono netBound execBound dynamicBound, ?_, ?_⟩
  · cases expected
    · simpa [selectedStackSummary, stackPathBounds] using choiceStack
    · rw [stackChoice_comm] at choiceStack
      simpa [selectedStackSummary, stackPathBounds] using choiceStack
  · cases expected
    · simpa [selectedOpSummary, opPathBounds] using choiceOps
    · rw [opChoice_comm] at choiceOps
      simpa [selectedOpSummary, opPathBounds] using choiceOps

theorem andorTrueResources
    {first second third : CoreFragment}
    {firstInputs branchInputs outputs : Stack} {selector : StackElement}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    {firstTrace branchTrace : StackTraceBound}
    {firstDynamic branchDynamic : Nat}
    (firstResources : ExecutesResourceFrame (compile first) firstInputs
      [selector] flags ctx firstTrace firstDynamic)
    (branchResources : ExecutesResourceFrame (compile second) branchInputs
      outputs flags ctx branchTrace branchDynamic)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (firstStack : selectedStackSummary first true = some firstTrace)
    (branchStack : selectedStackSummary second expected = some branchTrace)
    (firstOps : selectedOpSummary first true = some firstDynamic)
    (branchOps : selectedOpSummary second expected = some branchDynamic) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.andor first second third))
        (firstInputs ++ branchInputs) outputs flags ctx upperTrace
        upperDynamic ∧
      selectedStackSummary (.andor first second third) expected =
        some upperTrace ∧
      selectedOpSummary (.andor first second third) expected =
        some upperDynamic := by
  have currentStack : StackTraceSet.sequential
      (StackTraceSet.sequential (stackPathBounds first).sat
        (some StackTraceBound.branch)) (selectedStackSummary second expected) =
      some ((firstTrace.sequential StackTraceBound.branch).sequential
        branchTrace) := by
    simp [selectedStackSummary] at firstStack
    simp [firstStack, branchStack, StackTraceSet.sequential]
  have currentOps : PathMaximum.sequential (opPathBounds first).sat
      (selectedOpSummary second expected) =
      some (firstDynamic + branchDynamic) := by
    simp [selectedOpSummary] at firstOps
    simp [firstOps, branchOps, PathMaximum.sequential]
  exact andorResources_of_choice
    (andorFrame firstResources (by simpa [truth] using branchResources) minimal)
    (stackChoiceRight currentStack) (opChoiceRight currentOps)

theorem andorFalseResources
    {first second third : CoreFragment}
    {firstInputs branchInputs outputs : Stack} {selector : StackElement}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    {firstTrace branchTrace : StackTraceBound}
    {firstDynamic branchDynamic : Nat}
    (firstResources : ExecutesResourceFrame (compile first) firstInputs
      [selector] flags ctx firstTrace firstDynamic)
    (branchResources : ExecutesResourceFrame (compile third) branchInputs
      outputs flags ctx branchTrace branchDynamic)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (firstStack : selectedStackSummary first false = some firstTrace)
    (branchStack : selectedStackSummary third expected = some branchTrace)
    (firstOps : selectedOpSummary first false = some firstDynamic)
    (branchOps : selectedOpSummary third expected = some branchDynamic) :
    ∃ upperTrace upperDynamic,
      ExecutesResourceFrame (compile (.andor first second third))
        (firstInputs ++ branchInputs) outputs flags ctx upperTrace
        upperDynamic ∧
      selectedStackSummary (.andor first second third) expected =
        some upperTrace ∧
      selectedOpSummary (.andor first second third) expected =
        some upperDynamic := by
  have currentStack : StackTraceSet.sequential
      (StackTraceSet.sequential (stackPathBounds first).dsat
        (some StackTraceBound.branch)) (selectedStackSummary third expected) =
      some ((firstTrace.sequential StackTraceBound.branch).sequential
        branchTrace) := by
    simp [selectedStackSummary] at firstStack
    simp [firstStack, branchStack, StackTraceSet.sequential]
  have currentOps : PathMaximum.sequential (opPathBounds first).dsat
      (selectedOpSummary third expected) =
      some (firstDynamic + branchDynamic) := by
    simp [selectedOpSummary] at firstOps
    simp [firstOps, branchOps, PathMaximum.sequential]
  exact andorResources_of_choice
    (andorFrame firstResources (by simpa [falsy] using branchResources) minimal)
    (stackChoiceLeft currentStack) (opChoiceLeft currentOps)

end LeanMiniscript.Properties
