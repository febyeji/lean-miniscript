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

private theorem ifElseLeftFrame
    {firstScript secondScript : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (firstBalanced : BalancedControlFlow firstScript)
    (secondBalanced : BalancedControlFlow secondScript)
    (selected : ExecutesResourceFrame firstScript inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame
      ([.op .OP_IF] ++ firstScript ++ [.op .OP_ELSE] ++ secondScript ++
        [.op .OP_ENDIF])
      (trueElement :: inputs) outputs flags ctx
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
      (frame.select (castToBool trueElement)) inputs outputs flags ctx
      trace dynamic := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected
  simpa using ExecutesResourceFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) selected'

private theorem ifElseRightFrame
    {firstScript secondScript : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (firstBalanced : BalancedControlFlow firstScript)
    (secondBalanced : BalancedControlFlow secondScript)
    (selected : ExecutesResourceFrame secondScript inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame
      ([.op .OP_IF] ++ firstScript ++ [.op .OP_ELSE] ++ secondScript ++
        [.op .OP_ENDIF])
      (falseElement :: inputs) outputs flags ctx
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
      (frame.select (castToBool falseElement)) inputs outputs flags ctx
      trace dynamic := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected
  simpa using ExecutesResourceFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) selected'

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
    simpa [compile, compileWithKeyHash] using ifElseLeftFrame
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      resources
  cases expected
  · obtain ⟨childUpper, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := (stackPathBounds second).dsat) stackSelected
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := (opPathBounds second).dsat) opSelected
    have bounded := raw.mono
      (upper := StackTraceBound.branch.sequential childUpper)
      (upperDynamic := upperDynamic) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) dynamicBound
    refine ⟨StackTraceBound.branch.sequential childUpper, upperDynamic,
      bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some StackTraceBound.branch) summary) choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps
  · obtain ⟨childUpper, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := (stackPathBounds second).sat) stackSelected
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := (opPathBounds second).sat) opSelected
    have bounded := raw.mono
      (upper := StackTraceBound.branch.sequential childUpper)
      (upperDynamic := upperDynamic) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) dynamicBound
    refine ⟨StackTraceBound.branch.sequential childUpper, upperDynamic,
      bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some StackTraceBound.branch) summary) choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps

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
    simpa [compile, compileWithKeyHash] using ifElseRightFrame
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      resources
  cases expected
  · obtain ⟨childUpper, choiceStack, netBound, execBound⟩ :=
      stackChoiceRight (left := (stackPathBounds first).dsat) stackSelected
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceRight (left := (opPathBounds first).dsat) opSelected
    have bounded := raw.mono
      (upper := StackTraceBound.branch.sequential childUpper)
      (upperDynamic := upperDynamic) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) dynamicBound
    refine ⟨StackTraceBound.branch.sequential childUpper, upperDynamic,
      bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some StackTraceBound.branch) summary) choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps
  · obtain ⟨childUpper, choiceStack, netBound, execBound⟩ :=
      stackChoiceRight (left := (stackPathBounds first).sat) stackSelected
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceRight (left := (opPathBounds first).sat) opSelected
    have bounded := raw.mono
      (upper := StackTraceBound.branch.sequential childUpper)
      (upperDynamic := upperDynamic) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) (by
        simp [StackTraceBound.sequential, StackTraceBound.branch] at *
        omega) dynamicBound
    refine ⟨StackTraceBound.branch.sequential childUpper, upperDynamic,
      bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some StackTraceBound.branch) summary) choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps

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
    simpa [frame, ConditionalFrame.select, selectConditionalBranches, truth]
      using branchResources
  have conditional := ExecutesResourceFrame.notifSelected split minimal selected
  have concrete := (firstResources.withSuffix
    (suffix := branchInputs)).append conditional
  have raw : ExecutesResourceFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx
      (firstTrace.sequential
        (StackTraceBound.branch.sequential branchTrace))
      (firstDynamic + branchDynamic) := by
    simpa [compile, compileWithKeyHash, frame, List.append_assoc] using concrete
  have normalized : ExecutesResourceFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx
      ((firstTrace.sequential StackTraceBound.branch).sequential branchTrace)
      (firstDynamic + branchDynamic) := by
    apply raw.mono
    · simp [StackTraceBound.sequential, StackTraceBound.branch]
      omega
    · simp [StackTraceBound.sequential, StackTraceBound.branch]
      omega
    · exact Nat.le_refl _
  cases expected
  · have currentStack : StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.branch)) (stackPathBounds second).dsat =
        some ((firstTrace.sequential StackTraceBound.branch).sequential
          branchTrace) := by
      simp [selectedStackSummary] at firstStack branchStack
      simp [firstStack, branchStack, StackTraceSet.sequential]
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceRight (left := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds third).dsat)
        currentStack
    have currentOps : PathMaximum.sequential (opPathBounds first).sat
        (opPathBounds second).dsat =
        some (firstDynamic + branchDynamic) := by
      simp [selectedOpSummary] at firstOps branchOps
      simp [firstOps, branchOps, PathMaximum.sequential]
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceRight (left := PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds third).dsat) currentOps
    have bounded := normalized.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    refine ⟨upperTrace, upperDynamic, bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds] using choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps
  · have currentStack : StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.branch)) (stackPathBounds second).sat =
        some ((firstTrace.sequential StackTraceBound.branch).sequential
          branchTrace) := by
      simp [selectedStackSummary] at firstStack branchStack
      simp [firstStack, branchStack, StackTraceSet.sequential]
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds third).sat)
        currentStack
    have currentOps : PathMaximum.sequential (opPathBounds first).sat
        (opPathBounds second).sat =
        some (firstDynamic + branchDynamic) := by
      simp [selectedOpSummary] at firstOps branchOps
      simp [firstOps, branchOps, PathMaximum.sequential]
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds third).sat) currentOps
    have bounded := normalized.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    refine ⟨upperTrace, upperDynamic, bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds] using choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps

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
    simpa [frame, ConditionalFrame.select, selectConditionalBranches, falsy]
      using branchResources
  have conditional := ExecutesResourceFrame.notifSelected split minimal selected
  have concrete := (firstResources.withSuffix
    (suffix := branchInputs)).append conditional
  have raw : ExecutesResourceFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx
      (firstTrace.sequential
        (StackTraceBound.branch.sequential branchTrace))
      (firstDynamic + branchDynamic) := by
    simpa [compile, compileWithKeyHash, frame, List.append_assoc] using concrete
  have normalized : ExecutesResourceFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx
      ((firstTrace.sequential StackTraceBound.branch).sequential branchTrace)
      (firstDynamic + branchDynamic) := by
    apply raw.mono
    · simp [StackTraceBound.sequential, StackTraceBound.branch]
      omega
    · simp [StackTraceBound.sequential, StackTraceBound.branch]
      omega
    · exact Nat.le_refl _
  cases expected
  · have currentStack : StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds third).dsat =
        some ((firstTrace.sequential StackTraceBound.branch).sequential
          branchTrace) := by
      simp [selectedStackSummary] at firstStack branchStack
      simp [firstStack, branchStack, StackTraceSet.sequential]
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.branch)) (stackPathBounds second).dsat)
        currentStack
    have currentOps : PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds third).dsat =
        some (firstDynamic + branchDynamic) := by
      simp [selectedOpSummary] at firstOps branchOps
      simp [firstOps, branchOps, PathMaximum.sequential]
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := PathMaximum.sequential (opPathBounds first).sat
        (opPathBounds second).dsat) currentOps
    have bounded := normalized.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    refine ⟨upperTrace, upperDynamic, bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds] using choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps
  · have currentStack : StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds third).sat =
        some ((firstTrace.sequential StackTraceBound.branch).sequential
          branchTrace) := by
      simp [selectedStackSummary] at firstStack branchStack
      simp [firstStack, branchStack, StackTraceSet.sequential]
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceRight (left := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.branch)) (stackPathBounds second).sat)
        currentStack
    have currentOps : PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds third).sat =
        some (firstDynamic + branchDynamic) := by
      simp [selectedOpSummary] at firstOps branchOps
      simp [firstOps, branchOps, PathMaximum.sequential]
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceRight (left := PathMaximum.sequential (opPathBounds first).sat
        (opPathBounds second).sat) currentOps
    have bounded := normalized.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    refine ⟨upperTrace, upperDynamic, bounded, ?_, ?_⟩
    · simpa [selectedStackSummary, stackPathBounds] using choiceStack
    · simpa [selectedOpSummary, opPathBounds] using choiceOps

end LeanMiniscript.Properties
