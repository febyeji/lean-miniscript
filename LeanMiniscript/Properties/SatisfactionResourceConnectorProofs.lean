import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-! # Resource-aware connector composition -/

private theorem boolAndFrame
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

private theorem boolOrFrame
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

private theorem ifdupTrueFrame
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

private theorem ifdupFalseFrame
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

private theorem stackChoiceLeft
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

private theorem stackChoiceRight
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

private theorem opChoiceLeft
    {left right : PathMaximum} {value : Nat} (selected : left = some value) :
    ∃ upper, PathMaximum.choice left right = some upper ∧ value ≤ upper := by
  subst left
  cases right with
  | none => exact ⟨value, rfl, Nat.le_refl _⟩
  | some other => exact ⟨max value other, rfl, Nat.le_max_left _ _⟩

private theorem opChoiceRight
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

private theorem orILeftResources
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

private theorem orIRightResources
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

private theorem andorTrueResources
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

private theorem andorFalseResources
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
namespace GeneratedResourceContract

/-- Resource-aware `and_b` composition for the all-true or all-false row. -/
theorem andB_same
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness expected flags
      txCtx ⟨.B, firstMods⟩)
    (secondContract : GeneratedResourceContract second secondWitness expected
      flags txCtx ⟨.W, secondMods⟩) :
    GeneratedResourceContract (.and_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true }⟩ := by
  cases firstContract with
  | @b _ firstResult firstValue firstTrace firstDynamic firstInput firstFacts
      firstExecuted firstResources firstStack firstOps =>
    cases secondContract with
    | @w _ secondResult secondValue secondTrace secondDynamic secondInput order
        secondFacts secondExecuted secondResources secondStack secondOps =>
      have decoded := firstFacts.binaryDecoded secondFacts order
      have children := (firstResources.withSuffix
        (suffix := secondWitness.toInitialStack)).append
          (secondResources firstResult)
      have concrete := children.append (boolAndFrame decoded)
      have resources : ExecutesResourceFrame (compile (.and_b first second))
          (Witness.combine firstWitness secondWitness).toInitialStack
          [boolToElement ((firstValue != 0) && (secondValue != 0))]
          flags txCtx
          ((firstTrace.sequential secondTrace).sequential
            StackTraceBound.binary)
          (firstDynamic + secondDynamic) := by
        simpa [compile, compileWithKeyHash, Witness.toInitialStack_combine,
          List.append_assoc] using concrete
      have standard := GeneratedContract.andB
        (firstExpected := expected) (secondExpected := expected)
        (expected := expected)
        (GeneratedContract.b firstInput firstFacts firstExecuted)
        (GeneratedContract.w secondInput order secondFacts secondExecuted)
        (by cases expected <;> decide)
      cases standard with
      | b input facts executed =>
          apply GeneratedResourceContract.b input facts executed
            (resources.alignOutputs executed)
          · cases expected <;>
              simp [selectedStackSummary] at firstStack secondStack ⊢ <;>
              simp [stackPathBounds, firstStack, secondStack,
                StackTraceSet.sequential]
          · cases expected <;>
              simp [selectedOpSummary] at firstOps secondOps ⊢ <;>
              simp [opPathBounds, firstOps, secondOps, PathMaximum.sequential]

/-- Resource-aware usable path for `or_b`. The all-true overcomplete row is
    excluded; each mixed row is lifted to the public coordinate-wise choice. -/
theorem orB_path
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness firstExpected
      flags txCtx ⟨.B, firstMods⟩)
    (secondContract : GeneratedResourceContract second secondWitness
      secondExpected flags txCtx ⟨.W, secondMods⟩)
    (usable : ¬ (firstExpected = true ∧ secondExpected = true)) :
    GeneratedResourceContract (.or_b first second)
      (Witness.combine firstWitness secondWitness)
      (firstExpected || secondExpected) flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        d := true
        u := true }⟩ := by
  cases firstContract with
  | @b _ firstResult firstValue firstTrace firstDynamic firstInput firstFacts
      firstExecuted firstResources firstStack firstOps =>
    cases secondContract with
    | @w _ secondResult secondValue secondTrace secondDynamic secondInput order
        secondFacts secondExecuted secondResources secondStack secondOps =>
      have decoded := firstFacts.binaryDecoded secondFacts order
      have children := (firstResources.withSuffix
        (suffix := secondWitness.toInitialStack)).append
          (secondResources firstResult)
      have concrete := children.append (boolOrFrame decoded)
      have concreteResources : ExecutesResourceFrame
          (compile (.or_b first second))
          (Witness.combine firstWitness secondWitness).toInitialStack
          [boolToElement ((firstValue != 0) || (secondValue != 0))]
          flags txCtx
          ((firstTrace.sequential secondTrace).sequential
            StackTraceBound.binary)
          (firstDynamic + secondDynamic) := by
        simpa [compile, compileWithKeyHash, Witness.toInitialStack_combine,
          List.append_assoc] using concrete
      have standard := GeneratedContract.orB
        (firstExpected := firstExpected) (secondExpected := secondExpected)
        (expected := firstExpected || secondExpected)
        (GeneratedContract.b firstInput firstFacts firstExecuted)
        (GeneratedContract.w secondInput order secondFacts secondExecuted) rfl
      cases firstExpected <;> cases secondExpected
      · cases standard with
        | b input facts executed =>
            apply GeneratedResourceContract.b input facts executed
              (concreteResources.alignOutputs executed)
            · simp [selectedStackSummary] at firstStack secondStack ⊢
              simp [stackPathBounds, firstStack, secondStack,
                StackTraceSet.sequential]
            · simp [selectedOpSummary] at firstOps secondOps ⊢
              simp [opPathBounds, firstOps, secondOps, PathMaximum.sequential]
      · have currentStack : StackTraceSet.sequential
            (stackPathBounds first).dsat (stackPathBounds second).sat =
            some (firstTrace.sequential secondTrace) := by
          simp [selectedStackSummary] at firstStack secondStack
          simp [firstStack, secondStack, StackTraceSet.sequential]
        obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
          stackChoiceRight (left := StackTraceSet.sequential
            (stackPathBounds first).sat (stackPathBounds second).dsat)
            currentStack
        have currentOps : PathMaximum.sequential (opPathBounds first).dsat
            (opPathBounds second).sat = some (firstDynamic + secondDynamic) := by
          simp [selectedOpSummary] at firstOps secondOps
          simp [firstOps, secondOps, PathMaximum.sequential]
        obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
          opChoiceRight (left := PathMaximum.sequential
            (opPathBounds first).sat (opPathBounds second).dsat) currentOps
        have bounded := concreteResources.mono
          (upper := upperTrace.sequential StackTraceBound.binary)
          (upperDynamic := upperDynamic) (by
            simp [StackTraceBound.sequential, StackTraceBound.binary] at *
            omega) (by
            simp [StackTraceBound.sequential, StackTraceBound.binary] at *
            omega) dynamicBound
        cases standard with
        | b input facts executed =>
            apply GeneratedResourceContract.b input facts executed
              (bounded.alignOutputs executed)
            · simpa [selectedStackSummary, stackPathBounds,
                StackTraceSet.sequential] using congrArg
                  (fun summary => StackTraceSet.sequential summary
                    (some StackTraceBound.binary)) choiceStack
            · simpa [selectedOpSummary, opPathBounds] using choiceOps
      · have currentStack : StackTraceSet.sequential
            (stackPathBounds first).sat (stackPathBounds second).dsat =
            some (firstTrace.sequential secondTrace) := by
          simp [selectedStackSummary] at firstStack secondStack
          simp [firstStack, secondStack, StackTraceSet.sequential]
        obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
          stackChoiceLeft (right := StackTraceSet.sequential
            (stackPathBounds first).dsat (stackPathBounds second).sat)
            currentStack
        have currentOps : PathMaximum.sequential (opPathBounds first).sat
            (opPathBounds second).dsat = some (firstDynamic + secondDynamic) := by
          simp [selectedOpSummary] at firstOps secondOps
          simp [firstOps, secondOps, PathMaximum.sequential]
        obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
          opChoiceLeft (right := PathMaximum.sequential
            (opPathBounds first).dsat (opPathBounds second).sat) currentOps
        have bounded := concreteResources.mono
          (upper := upperTrace.sequential StackTraceBound.binary)
          (upperDynamic := upperDynamic) (by
            simp [StackTraceBound.sequential, StackTraceBound.binary] at *
            omega) (by
            simp [StackTraceBound.sequential, StackTraceBound.binary] at *
            omega) dynamicBound
        cases standard with
        | b input facts executed =>
            apply GeneratedResourceContract.b input facts executed
              (bounded.alignOutputs executed)
            · simpa [selectedStackSummary, stackPathBounds,
                StackTraceSet.sequential] using congrArg
                  (fun summary => StackTraceSet.sequential summary
                    (some StackTraceBound.binary)) choiceStack
            · simpa [selectedOpSummary, opPathBounds] using choiceOps
      · exact False.elim (usable ⟨rfl, rfl⟩)

/-- Resource-aware direct path of `or_c`, where a true first result skips the
    V child. -/
theorem orC_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedResourceContract (.or_c first second) witness true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    let frame : ConditionalFrame := { branches := [compile second], after := [] }
    have split : splitConditional (compile second ++ [.op .OP_ENDIF]) =
        some frame := by
      simpa [frame] using splitConditional_balanced_ifThen
        (compile_balancedControlFlow second) (suffix := [])
    have skipped : ExecutesResourceFrame
        (frame.select (!castToBool result)) [] [] flags txCtx
        StackTraceBound.empty 0 := by
      simpa [frame, ConditionalFrame.select, selectConditionalBranches,
        facts.truth] using ExecutesResourceFrame.empty [] flags txCtx
    have branch := ExecutesResourceFrame.notifSelected split
      (facts.minimalIfSatisfied firstUnit) skipped
    have concrete := resources.append branch
    have concreteRaw : ExecutesResourceFrame (compile (.or_c first second))
        witness.toInitialStack [] flags txCtx
        (trace.sequential
          (StackTraceBound.branch.sequential StackTraceBound.empty))
        dynamic := by
      simpa [compile, compileWithKeyHash, frame] using concrete
    have concrete' : ExecutesResourceFrame (compile (.or_c first second))
        witness.toInitialStack [] flags txCtx
        (trace.sequential StackTraceBound.branch) dynamic := by
      apply concreteRaw.mono
      · simp [StackTraceBound.empty, StackTraceBound.branch,
          StackTraceBound.sequential]
      · simp [StackTraceBound.empty, StackTraceBound.branch,
          StackTraceBound.sequential]
        have traceNonnegative := resources.exec_nonneg
        have oneLe : (1 : Int) ≤ 1 + trace.exec := by omega
        rw [Int.max_eq_right oneLe]
        rw [Int.max_eq_right (by omega)]
        exact Int.le_refl _
      · exact Nat.le_refl _
    have currentStack : StackTraceSet.sequential (stackPathBounds first).sat
        (some StackTraceBound.branch) =
        some (trace.sequential StackTraceBound.branch) := by
      simpa [selectedStackSummary, StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential summary
          (some StackTraceBound.branch)) stackSelected
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds second).sat)
        currentStack
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds second).sat) opSelected
    have bounded := concrete'.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    have standard := GeneratedContract.orC_left
      (second := second) (secondMods := secondMods)
      (GeneratedContract.b input facts executed) firstUnit
    cases standard with
    | v targetInput targetTrue targetExecuted =>
        apply GeneratedResourceContract.v targetInput targetTrue targetExecuted
          bounded
        · simpa [selectedStackSummary, stackPathBounds] using choiceStack
        · simpa [selectedOpSummary, opPathBounds] using choiceOps

/-- Resource-aware alternate path of `or_c`, where a false first result enters
    the V child. -/
theorem orC_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedResourceContract second secondWitness true flags
      txCtx ⟨.V, secondMods⟩) :
    GeneratedResourceContract (.or_c first second)
      (Witness.combine firstWitness secondWitness) true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ := by
  cases firstContract with
  | @b _ result value firstTrace firstDynamic firstInput firstFacts firstExecuted
      firstResources firstStack firstOps =>
    cases secondContract with
    | @v _ secondTrace secondDynamic secondInput secondTrue secondExecuted
        secondResources secondStack secondOps =>
      let frame : ConditionalFrame := { branches := [compile second], after := [] }
      have split : splitConditional (compile second ++ [.op .OP_ENDIF]) =
          some frame := by
        simpa [frame] using splitConditional_balanced_ifThen
          (compile_balancedControlFlow second) (suffix := [])
      have selected : ExecutesResourceFrame
          (frame.select (!castToBool result)) secondWitness.toInitialStack []
          flags txCtx secondTrace secondDynamic := by
        simpa [frame, ConditionalFrame.select, selectConditionalBranches,
          firstFacts.truth] using secondResources
      have branch := ExecutesResourceFrame.notifSelected split
        (firstFacts.minimalIfSatisfied firstUnit) selected
      have concrete := (firstResources.withSuffix
        (suffix := secondWitness.toInitialStack)).append branch
      have concreteRaw : ExecutesResourceFrame (compile (.or_c first second))
          (Witness.combine firstWitness secondWitness).toInitialStack []
          flags txCtx
          (firstTrace.sequential
            (StackTraceBound.branch.sequential secondTrace))
          (firstDynamic + secondDynamic) := by
        simpa [compile, compileWithKeyHash, frame,
          Witness.toInitialStack_combine, List.append_assoc] using concrete
      have concrete' : ExecutesResourceFrame (compile (.or_c first second))
          (Witness.combine firstWitness secondWitness).toInitialStack []
          flags txCtx
          ((firstTrace.sequential StackTraceBound.branch).sequential secondTrace)
          (firstDynamic + secondDynamic) := by
        apply concreteRaw.mono
        · simp [StackTraceBound.sequential, StackTraceBound.branch]
          omega
        · simp [StackTraceBound.sequential, StackTraceBound.branch]
          omega
        · exact Nat.le_refl _
      have currentStack : StackTraceSet.sequential
          (StackTraceSet.sequential (stackPathBounds first).dsat
            (some StackTraceBound.branch)) (stackPathBounds second).sat =
          some ((firstTrace.sequential StackTraceBound.branch).sequential
            secondTrace) := by
        simp [selectedStackSummary] at firstStack secondStack
        simp [firstStack, secondStack, StackTraceSet.sequential]
      obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
        stackChoiceRight (left := StackTraceSet.sequential
          (stackPathBounds first).sat (some StackTraceBound.branch)) currentStack
      have currentOps : PathMaximum.sequential (opPathBounds first).dsat
          (opPathBounds second).sat = some (firstDynamic + secondDynamic) := by
        simp [selectedOpSummary] at firstOps secondOps
        simp [firstOps, secondOps, PathMaximum.sequential]
      obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
        opChoiceRight (left := (opPathBounds first).sat) currentOps
      have bounded := concrete'.mono (upper := upperTrace)
        (upperDynamic := upperDynamic) netBound execBound dynamicBound
      have standard := GeneratedContract.orC_right
        (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
        (GeneratedContract.v secondInput secondTrue secondExecuted)
      cases standard with
      | v targetInput targetTrue targetExecuted =>
          apply GeneratedResourceContract.v targetInput targetTrue targetExecuted
            bounded
          · simpa [selectedStackSummary, stackPathBounds] using choiceStack
          · simpa [selectedOpSummary, opPathBounds] using choiceOps

/-- Resource-aware direct path of `or_d`, where a true first result is
    preserved by `OP_IFDUP` while the B child is skipped. -/
theorem orD_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedResourceContract (.or_d first second) witness true flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    let frame : ConditionalFrame := { branches := [compile second], after := [] }
    have split : splitConditional (compile second ++ [.op .OP_ENDIF]) =
        some frame := by
      simpa [frame] using splitConditional_balanced_ifThen
        (compile_balancedControlFlow second) (suffix := [])
    have skipped : ExecutesResourceFrame
        (frame.select (!castToBool result)) [result] [result] flags txCtx
        StackTraceBound.empty 0 := by
      simpa [frame, ConditionalFrame.select, selectConditionalBranches,
        facts.truth] using ExecutesResourceFrame.empty [result] flags txCtx
    have branch := ExecutesResourceFrame.notifSelected split
      (facts.minimalIfSatisfied firstUnit) skipped
    have tail := (ifdupTrueFrame (ctx := txCtx) facts.truth).append branch
    have concrete := resources.append tail
    have concreteRaw : ExecutesResourceFrame (compile (.or_d first second))
        witness.toInitialStack [result] flags txCtx
        (trace.sequential
          (StackTraceBound.ifdupTrue.sequential
            (StackTraceBound.branch.sequential StackTraceBound.empty)))
        dynamic := by
      simpa [compile, compileWithKeyHash, frame] using concrete
    have concrete' : ExecutesResourceFrame (compile (.or_d first second))
        witness.toInitialStack [result] flags txCtx
        ((trace.sequential StackTraceBound.ifdupTrue).sequential
          StackTraceBound.branch) dynamic := by
      apply concreteRaw.mono
      · simp [StackTraceBound.sequential, StackTraceBound.empty,
          StackTraceBound.ifdupTrue, StackTraceBound.branch]
        omega
      · simp [StackTraceBound.sequential, StackTraceBound.empty,
          StackTraceBound.ifdupTrue, StackTraceBound.branch]
        have traceNonnegative := resources.exec_nonneg
        omega
      · exact Nat.le_refl _
    have currentStack : StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.ifdupTrue))
        (some StackTraceBound.branch) =
        some ((trace.sequential StackTraceBound.ifdupTrue).sequential
          StackTraceBound.branch) := by
      simpa [selectedStackSummary, StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (StackTraceSet.sequential summary (some StackTraceBound.ifdupTrue))
          (some StackTraceBound.branch)) stackSelected
    obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
      stackChoiceLeft (right := StackTraceSet.sequential
        (StackTraceSet.sequential
          (StackTraceSet.sequential (stackPathBounds first).dsat
            (some StackTraceBound.ifdupFalse))
          (some StackTraceBound.branch)) (stackPathBounds second).sat)
        currentStack
    obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
      opChoiceLeft (right := PathMaximum.sequential (opPathBounds first).dsat
        (opPathBounds second).sat) opSelected
    have bounded := concrete'.mono (upper := upperTrace)
      (upperDynamic := upperDynamic) netBound execBound dynamicBound
    have standard := GeneratedContract.orD_left
      (second := second) (secondMods := secondMods)
      (GeneratedContract.b input facts executed) firstUnit
    cases standard with
    | b targetInput targetFacts targetExecuted =>
        apply GeneratedResourceContract.b targetInput targetFacts targetExecuted
          (bounded.alignOutputs targetExecuted)
        · simpa [selectedStackSummary, stackPathBounds] using choiceStack
        · simpa [selectedOpSummary, opPathBounds] using choiceOps

/-- Resource-aware alternate path of `or_d`, where a false first result enters
    the selected B child. -/
theorem orD_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedResourceContract second secondWitness expected
      flags txCtx ⟨.B, secondMods⟩) :
    GeneratedResourceContract (.or_d first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ := by
  cases firstContract with
  | @b _ selector firstValue firstTrace firstDynamic firstInput firstFacts
      firstExecuted firstResources firstStack firstOps =>
    cases secondContract with
    | @b _ result secondValue secondTrace secondDynamic secondInput secondFacts
      secondExecuted secondResources secondStack secondOps =>
      let frame : ConditionalFrame := { branches := [compile second], after := [] }
      have split : splitConditional (compile second ++ [.op .OP_ENDIF]) =
          some frame := by
        simpa [frame] using splitConditional_balanced_ifThen
          (compile_balancedControlFlow second) (suffix := [])
      have selected : ExecutesResourceFrame
          (frame.select (!castToBool selector)) secondWitness.toInitialStack
          [result] flags txCtx secondTrace secondDynamic := by
        simpa [frame, ConditionalFrame.select, selectConditionalBranches,
          firstFacts.truth] using secondResources
      have branch := ExecutesResourceFrame.notifSelected split
        (firstFacts.minimalIfSatisfied firstUnit) selected
      have duplicated := (ifdupFalseFrame (flags := flags) (ctx := txCtx)
        firstFacts.truth).withSuffix (suffix := secondWitness.toInitialStack)
      have tail := duplicated.append branch
      have concrete := (firstResources.withSuffix
        (suffix := secondWitness.toInitialStack)).append tail
      have concreteRaw : ExecutesResourceFrame (compile (.or_d first second))
          (Witness.combine firstWitness secondWitness).toInitialStack [result]
          flags txCtx
          (firstTrace.sequential
            (StackTraceBound.ifdupFalse.sequential
              (StackTraceBound.branch.sequential secondTrace)))
          (firstDynamic + secondDynamic) := by
        simpa [compile, compileWithKeyHash, frame,
          Witness.toInitialStack_combine, List.append_assoc] using concrete
      have concrete' : ExecutesResourceFrame (compile (.or_d first second))
          (Witness.combine firstWitness secondWitness).toInitialStack [result]
          flags txCtx
          (((firstTrace.sequential StackTraceBound.ifdupFalse).sequential
            StackTraceBound.branch).sequential secondTrace)
          (firstDynamic + secondDynamic) := by
        apply concreteRaw.mono
        · simp [StackTraceBound.sequential, StackTraceBound.ifdupFalse,
            StackTraceBound.branch]
          omega
        · simp [StackTraceBound.sequential, StackTraceBound.ifdupFalse,
            StackTraceBound.branch]
          omega
        · exact Nat.le_refl _
      have standard := GeneratedContract.orD_right
        (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
        (GeneratedContract.b secondInput secondFacts secondExecuted)
      cases expected
      · have currentStack : StackTraceSet.sequential
            (StackTraceSet.sequential
              (StackTraceSet.sequential (stackPathBounds first).dsat
                (some StackTraceBound.ifdupFalse))
              (some StackTraceBound.branch)) (stackPathBounds second).dsat =
            some (((firstTrace.sequential StackTraceBound.ifdupFalse).sequential
              StackTraceBound.branch).sequential secondTrace) := by
          simp [selectedStackSummary] at firstStack secondStack
          simp [firstStack, secondStack, StackTraceSet.sequential]
        have currentOps : PathMaximum.sequential (opPathBounds first).dsat
            (opPathBounds second).dsat =
            some (firstDynamic + secondDynamic) := by
          simp [selectedOpSummary] at firstOps secondOps
          simp [firstOps, secondOps, PathMaximum.sequential]
        cases standard with
        | b targetInput targetFacts targetExecuted =>
            apply GeneratedResourceContract.b targetInput targetFacts
              targetExecuted (concrete'.alignOutputs targetExecuted)
            · simpa [selectedStackSummary, stackPathBounds] using currentStack
            · simpa [selectedOpSummary, opPathBounds] using currentOps
      · have currentStack : StackTraceSet.sequential
            (StackTraceSet.sequential
              (StackTraceSet.sequential (stackPathBounds first).dsat
                (some StackTraceBound.ifdupFalse))
              (some StackTraceBound.branch)) (stackPathBounds second).sat =
            some (((firstTrace.sequential StackTraceBound.ifdupFalse).sequential
              StackTraceBound.branch).sequential secondTrace) := by
          simp [selectedStackSummary] at firstStack secondStack
          simp [firstStack, secondStack, StackTraceSet.sequential]
        obtain ⟨upperTrace, choiceStack, netBound, execBound⟩ :=
          stackChoiceRight (left := StackTraceSet.sequential
            (StackTraceSet.sequential (stackPathBounds first).sat
              (some StackTraceBound.ifdupTrue))
            (some StackTraceBound.branch)) currentStack
        have currentOps : PathMaximum.sequential (opPathBounds first).dsat
            (opPathBounds second).sat =
            some (firstDynamic + secondDynamic) := by
          simp [selectedOpSummary] at firstOps secondOps
          simp [firstOps, secondOps, PathMaximum.sequential]
        obtain ⟨upperDynamic, choiceOps, dynamicBound⟩ :=
          opChoiceRight (left := (opPathBounds first).sat) currentOps
        have bounded := concrete'.mono (upper := upperTrace)
          (upperDynamic := upperDynamic) netBound execBound dynamicBound
        cases standard with
        | b targetInput targetFacts targetExecuted =>
            apply GeneratedResourceContract.b targetInput targetFacts
              targetExecuted (bounded.alignOutputs targetExecuted)
            · simpa [selectedStackSummary, stackPathBounds] using choiceStack
            · simpa [selectedOpSummary, opPathBounds] using choiceOps

/-- Resource-aware left branch of `or_i`, selected by the canonical true
    witness item for every admissible branch base. -/
theorem orI_left
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract first witness expected flags txCtx
      ⟨base, firstMods⟩) (branch : branchBase base) :
    GeneratedResourceContract (.or_i first second)
      (witness.withSelector trueElement) expected flags txCtx
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ := by
  cases base with
  | B =>
      cases contract with
      | @b _ result value trace dynamic input facts executed resources
          stackSelected opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orILeftResources (second := second) resources stackSelected opSelected
        have standard := GeneratedContract.orILeft_b
          (second := second) (secondMods := secondMods)
          (GeneratedContract.b input facts executed)
        cases standard with
        | @b _ targetResult targetValue targetInput targetFacts
            targetExecuted =>
            have target' : ExecutesStackFrame (compile (.or_i first second))
                (trueElement :: witness.toInitialStack) [targetResult]
                flags txCtx := by
              simpa only [Witness.toInitialStack_withSelector, BExecution] using
                targetExecuted
            apply GeneratedResourceContract.b targetInput targetFacts
              targetExecuted
            · simpa only [Witness.toInitialStack_withSelector] using
                bounded.alignOutputs target'
            · exact targetStack
            · exact targetOps
  | K =>
      cases contract with
      | @k _ trace dynamic input ownArgs key signature stackShape executed
          checked resources stackSelected opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orILeftResources (second := second) resources stackSelected opSelected
        have standard := GeneratedContract.orILeft_k
          (second := second) (secondMods := secondMods)
          (GeneratedContract.k input ownArgs key signature stackShape executed
            checked)
        cases standard with
        | k targetInput targetOwnArgs targetKey targetSignature targetShape
            targetExecuted targetChecked =>
            have target : ExecutesStackFrame (compile (.or_i first second))
                (witness.withSelector trueElement).toInitialStack
                [targetKey, targetSignature] flags txCtx := by
              rw [targetShape]
              simpa using targetExecuted.withSuffix
                (suffix := [targetSignature])
            have target' : ExecutesStackFrame (compile (.or_i first second))
                (trueElement :: witness.toInitialStack)
                [targetKey, targetSignature] flags txCtx := by
              simpa only [Witness.toInitialStack_withSelector] using target
            exact GeneratedResourceContract.k targetInput targetOwnArgs
              targetKey targetSignature targetShape targetExecuted targetChecked
              (by simpa only [Witness.toInitialStack_withSelector] using
                bounded.alignOutputs target')
              targetStack targetOps
  | V =>
      cases contract with
      | @v _ trace dynamic input expectedTrue executed resources stackSelected
          opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orILeftResources (second := second) resources stackSelected opSelected
        have standard := GeneratedContract.orILeft_v
          (second := second) (secondMods := secondMods)
          (GeneratedContract.v input expectedTrue executed)
        cases standard with
        | v targetInput targetTrue targetExecuted =>
            exact GeneratedResourceContract.v targetInput targetTrue
              targetExecuted (by
                simpa only [Witness.toInitialStack_withSelector] using bounded)
              targetStack targetOps
  | W => simp [branchBase] at branch

/-- Resource-aware right branch of `or_i`, selected by the canonical false
    witness item for every admissible branch base. -/
theorem orI_right
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract second witness expected flags txCtx
      ⟨base, secondMods⟩) (branch : branchBase base) :
    GeneratedResourceContract (.or_i first second)
      (witness.withSelector falseElement) expected flags txCtx
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ := by
  cases base with
  | B =>
      cases contract with
      | @b _ result value trace dynamic input facts executed resources
          stackSelected opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orIRightResources (first := first) resources stackSelected opSelected
        have standard := GeneratedContract.orIRight_b
          (first := first) (firstMods := firstMods)
          (GeneratedContract.b input facts executed)
        cases standard with
        | @b _ targetResult targetValue targetInput targetFacts
            targetExecuted =>
            have target' : ExecutesStackFrame (compile (.or_i first second))
                (falseElement :: witness.toInitialStack) [targetResult]
                flags txCtx := by
              simpa only [Witness.toInitialStack_withSelector, BExecution] using
                targetExecuted
            apply GeneratedResourceContract.b targetInput targetFacts
              targetExecuted
            · simpa only [Witness.toInitialStack_withSelector] using
                bounded.alignOutputs target'
            · exact targetStack
            · exact targetOps
  | K =>
      cases contract with
      | @k _ trace dynamic input ownArgs key signature stackShape executed
          checked resources stackSelected opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orIRightResources (first := first) resources stackSelected opSelected
        have standard := GeneratedContract.orIRight_k
          (first := first) (firstMods := firstMods)
          (GeneratedContract.k input ownArgs key signature stackShape executed
            checked)
        cases standard with
        | k targetInput targetOwnArgs targetKey targetSignature targetShape
            targetExecuted targetChecked =>
            have target : ExecutesStackFrame (compile (.or_i first second))
                (witness.withSelector falseElement).toInitialStack
                [targetKey, targetSignature] flags txCtx := by
              rw [targetShape]
              simpa using targetExecuted.withSuffix
                (suffix := [targetSignature])
            have target' : ExecutesStackFrame (compile (.or_i first second))
                (falseElement :: witness.toInitialStack)
                [targetKey, targetSignature] flags txCtx := by
              simpa only [Witness.toInitialStack_withSelector] using target
            exact GeneratedResourceContract.k targetInput targetOwnArgs
              targetKey targetSignature targetShape targetExecuted targetChecked
              (by simpa only [Witness.toInitialStack_withSelector] using
                bounded.alignOutputs target')
              targetStack targetOps
  | V =>
      cases contract with
      | @v _ trace dynamic input expectedTrue executed resources stackSelected
          opSelected =>
        obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
          orIRightResources (first := first) resources stackSelected opSelected
        have standard := GeneratedContract.orIRight_v
          (first := first) (firstMods := firstMods)
          (GeneratedContract.v input expectedTrue executed)
        cases standard with
        | v targetInput targetTrue targetExecuted =>
            exact GeneratedResourceContract.v targetInput targetTrue
              targetExecuted (by
                simpa only [Witness.toInitialStack_withSelector] using bounded)
              targetStack targetOps
  | W => simp [branchBase] at branch

/-- Resource-aware true-selector path of `andor` for every admissible branch
    base. -/
theorem andorTrue
    {first second third : CoreFragment}
    {firstWitness secondWitness : Witness} {expected : Bool}
    {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness true flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedResourceContract second secondWitness expected
      flags txCtx ⟨base, secondMods⟩) (branch : branchBase base) :
    GeneratedResourceContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ := by
  cases firstContract with
  | @b _ selector firstValue firstTrace firstDynamic firstInput firstFacts
      firstExecuted firstResources firstStack firstOps =>
    cases base with
    | B =>
        cases secondContract with
        | @b _ result value branchTrace branchDynamic branchInput branchFacts
            branchExecuted branchResources branchStack branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorTrueResources (third := third) firstResources branchResources
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
              firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorTrue_b
            (third := third) (thirdMods := thirdMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.b branchInput branchFacts branchExecuted)
          cases standard with
          | @b _ targetResult targetValue targetInput targetFacts
              targetExecuted =>
              have target' : ExecutesStackFrame
                  (compile (.andor first second third))
                  (firstWitness.toInitialStack ++ secondWitness.toInitialStack)
                  [targetResult] flags txCtx := by
                simpa only [Witness.toInitialStack_combine, BExecution] using
                  targetExecuted
              exact GeneratedResourceContract.b targetInput targetFacts
                targetExecuted
                (by simpa only [Witness.toInitialStack_combine] using
                  bounded.alignOutputs target') targetStack targetOps
    | K =>
        cases secondContract with
        | @k _ branchTrace branchDynamic branchInput ownArgs key signature
            stackShape branchExecuted checked branchResources branchStack
            branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorTrueResources (third := third) firstResources branchResources
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
              firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorTrue_k
            (third := third) (thirdMods := thirdMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.k branchInput ownArgs key signature stackShape
              branchExecuted checked)
          cases standard with
          | k targetInput targetOwnArgs targetKey targetSignature targetShape
              targetExecuted targetChecked =>
              have target : ExecutesStackFrame
                  (compile (.andor first second third))
                  (Witness.combine firstWitness secondWitness).toInitialStack
                  [targetKey, targetSignature] flags txCtx := by
                rw [targetShape]
                simpa using targetExecuted.withSuffix
                  (suffix := [targetSignature])
              have target' : ExecutesStackFrame
                  (compile (.andor first second third))
                  (firstWitness.toInitialStack ++ secondWitness.toInitialStack)
                  [targetKey, targetSignature] flags txCtx := by
                simpa only [Witness.toInitialStack_combine] using target
              exact GeneratedResourceContract.k targetInput targetOwnArgs
                targetKey targetSignature targetShape targetExecuted
                targetChecked
                (by simpa only [Witness.toInitialStack_combine] using
                  bounded.alignOutputs target') targetStack targetOps
    | V =>
        cases secondContract with
        | @v _ branchTrace branchDynamic branchInput expectedTrue
            branchExecuted branchResources branchStack branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorTrueResources (third := third) firstResources branchResources
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
              firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorTrue_v
            (third := third) (thirdMods := thirdMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.v branchInput expectedTrue branchExecuted)
          cases standard with
          | v targetInput targetTrue targetExecuted =>
              exact GeneratedResourceContract.v targetInput targetTrue
                targetExecuted
                (by simpa only [Witness.toInitialStack_combine] using bounded)
                targetStack targetOps
    | W => simp [branchBase] at branch

/-- Resource-aware false-selector path of `andor` for every admissible branch
    base. -/
theorem andorFalse
    {first second third : CoreFragment}
    {firstWitness thirdWitness : Witness} {expected : Bool}
    {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedResourceContract third thirdWitness expected
      flags txCtx ⟨base, thirdMods⟩) (branch : branchBase base) :
    GeneratedResourceContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ := by
  cases firstContract with
  | @b _ selector firstValue firstTrace firstDynamic firstInput firstFacts
      firstExecuted firstResources firstStack firstOps =>
    cases base with
    | B =>
        cases thirdContract with
        | @b _ result value branchTrace branchDynamic branchInput branchFacts
            branchExecuted branchResources branchStack branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorFalseResources (second := second) firstResources
              branchResources (firstFacts.minimalIfSatisfied firstUnit)
              firstFacts.truth firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorFalse_b
            (second := second) (secondMods := secondMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.b branchInput branchFacts branchExecuted)
          cases standard with
          | @b _ targetResult targetValue targetInput targetFacts
              targetExecuted =>
              have target' : ExecutesStackFrame
                  (compile (.andor first second third))
                  (firstWitness.toInitialStack ++ thirdWitness.toInitialStack)
                  [targetResult] flags txCtx := by
                simpa only [Witness.toInitialStack_combine, BExecution] using
                  targetExecuted
              exact GeneratedResourceContract.b targetInput targetFacts
                targetExecuted
                (by simpa only [Witness.toInitialStack_combine] using
                  bounded.alignOutputs target') targetStack targetOps
    | K =>
        cases thirdContract with
        | @k _ branchTrace branchDynamic branchInput ownArgs key signature
            stackShape branchExecuted checked branchResources branchStack
            branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorFalseResources (second := second) firstResources
              branchResources (firstFacts.minimalIfSatisfied firstUnit)
              firstFacts.truth firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorFalse_k
            (second := second) (secondMods := secondMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.k branchInput ownArgs key signature stackShape
              branchExecuted checked)
          cases standard with
          | k targetInput targetOwnArgs targetKey targetSignature targetShape
              targetExecuted targetChecked =>
              have target : ExecutesStackFrame
                  (compile (.andor first second third))
                  (Witness.combine firstWitness thirdWitness).toInitialStack
                  [targetKey, targetSignature] flags txCtx := by
                rw [targetShape]
                simpa using targetExecuted.withSuffix
                  (suffix := [targetSignature])
              have target' : ExecutesStackFrame
                  (compile (.andor first second third))
                  (firstWitness.toInitialStack ++ thirdWitness.toInitialStack)
                  [targetKey, targetSignature] flags txCtx := by
                simpa only [Witness.toInitialStack_combine] using target
              exact GeneratedResourceContract.k targetInput targetOwnArgs
                targetKey targetSignature targetShape targetExecuted
                targetChecked
                (by simpa only [Witness.toInitialStack_combine] using
                  bounded.alignOutputs target') targetStack targetOps
    | V =>
        cases thirdContract with
        | @v _ branchTrace branchDynamic branchInput expectedTrue
            branchExecuted branchResources branchStack branchOps =>
          obtain ⟨upperTrace, upperDynamic, bounded, targetStack, targetOps⟩ :=
            andorFalseResources (second := second) firstResources
              branchResources (firstFacts.minimalIfSatisfied firstUnit)
              firstFacts.truth firstStack branchStack firstOps branchOps
          have standard := GeneratedContract.andorFalse_v
            (second := second) (secondMods := secondMods)
            (GeneratedContract.b firstInput firstFacts firstExecuted) firstUnit
            (GeneratedContract.v branchInput expectedTrue branchExecuted)
          cases standard with
          | v targetInput targetTrue targetExecuted =>
              exact GeneratedResourceContract.v targetInput targetTrue
                targetExecuted
                (by simpa only [Witness.toInitialStack_combine] using bounded)
                targetStack targetOps
    | W => simp [branchBase] at branch

/-- Resource-aware satisfying path of the `d` wrapper. -/
theorem d
    {fragment : CoreFragment} {witness : Witness} (scriptCtx : ScriptContext)
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness true flags txCtx
      ⟨.V, mods⟩) (zeroArg : mods.z = true) :
    GeneratedResourceContract (.d fragment)
      (witness.withSelector trueElement) true flags txCtx
      ⟨.B, {
        o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩ := by
  cases contract with
  | @v _ trace dynamic input expectedTrue executed resources stackSelected
      opSelected =>
    have childShape := input.zeroArgs zeroArg
    have childResources : ExecutesResourceFrame (compile fragment) [] []
        flags txCtx trace dynamic := by
      simpa [childShape] using resources
    let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
    have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some frame := by
      simpa [frame] using splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := [])
    have selected : ExecutesResourceFrame
        (frame.select (castToBool trueElement)) [trueElement] [trueElement]
        flags txCtx trace dynamic := by
      simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
        childResources.withSuffix (suffix := [trueElement])
    have conditional := ExecutesResourceFrame.ifSelected split
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) selected
    have concrete :=
      (ExecutesResourceFrame.dup trueElement flags txCtx).append conditional
    have raw : ExecutesResourceFrame (compile (.d fragment)) [trueElement]
        [trueElement] flags txCtx
        (StackTraceBound.dup.sequential
          (StackTraceBound.branch.sequential trace)) dynamic := by
      simpa [compile, compileWithKeyHash, frame] using concrete
    have bounded : ExecutesResourceFrame (compile (.d fragment)) [trueElement]
        [trueElement] flags txCtx
        ((StackTraceBound.dup.sequential StackTraceBound.branch).sequential
          trace) dynamic := by
      apply raw.mono
      · simp [StackTraceBound.sequential, StackTraceBound.dup,
          StackTraceBound.branch]
        omega
      · simp [StackTraceBound.sequential, StackTraceBound.dup,
          StackTraceBound.branch]
        omega
      · exact Nat.le_refl _
    have childExec := executed
    rw [childShape] at childExec
    have targetInput : GeneratedInput (witness.withSelector trueElement) true
        { o := true, n := true, d := true,
          u := scriptCtx.dWrapperUnit } := by
      refine ⟨input.bounded.withSelector trueElement_size_le, ?_, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨trueElement, by simp [childShape]⟩
      · intro _ _
        exact ⟨trueElement, [], by simp [childShape], by decide⟩
    have targetExecuted : BExecution (.d fragment) [trueElement]
        trueElement flags txCtx := by
      simpa [childShape, boolToElement] using childExec.d
    apply GeneratedResourceContract.b targetInput
      (BooleanResultFacts.canonical true _ flags) (by
        simpa [Witness.toInitialStack_withSelector, childShape,
          boolToElement] using
          targetExecuted)
    · simpa [Witness.toInitialStack_withSelector, childShape,
        boolToElement] using bounded
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential
          (some (StackTraceBound.dup.sequential StackTraceBound.branch))
          summary) stackSelected
    · simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware canonical dissatisfaction of the `d` wrapper. -/
theorem d_false
    (fragment : CoreFragment) (scriptCtx : ScriptContext)
    (flags : ScriptFlags) (txCtx : TxContext) :
    GeneratedResourceContract (.d fragment) [falseElement] false flags txCtx
      ⟨.B, { o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩ := by
  let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
  have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifThen
      (compile_balancedControlFlow fragment) (suffix := [])
  have skipped : ExecutesResourceFrame
      (frame.select (castToBool falseElement)) [falseElement] [falseElement]
      flags txCtx StackTraceBound.empty 0 := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      ExecutesResourceFrame.empty [falseElement] flags txCtx
  have conditional := ExecutesResourceFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) skipped
  have concrete :=
    (ExecutesResourceFrame.dup falseElement flags txCtx).append conditional
  have raw : ExecutesResourceFrame (compile (.d fragment)) [falseElement]
      [falseElement] flags txCtx
      (StackTraceBound.dup.sequential
        (StackTraceBound.branch.sequential StackTraceBound.empty)) 0 := by
    simpa [compile, compileWithKeyHash, frame] using concrete
  have resources : ExecutesResourceFrame (compile (.d fragment)) [falseElement]
      [falseElement] flags txCtx
      (StackTraceBound.dup.sequential StackTraceBound.branch) 0 := by
    apply raw.mono
    · simp [StackTraceBound.sequential, StackTraceBound.dup,
        StackTraceBound.branch, StackTraceBound.empty]
    · simp [StackTraceBound.sequential, StackTraceBound.dup,
        StackTraceBound.branch, StackTraceBound.empty]
      omega
    · exact Nat.le_refl _
  apply GeneratedResourceContract.b
  · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
      ?_, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨falseElement, rfl⟩
    · simp
  · exact BooleanResultFacts.canonical false _ flags
  · simpa [boolToElement, Witness.toInitialStack] using
      d_dissatisfaction_execution fragment flags txCtx
  · simpa [Witness.toInitialStack, boolToElement] using resources
  · simp [selectedStackSummary, stackPathBounds]
  · simp [selectedOpSummary, opPathBounds]

end GeneratedResourceContract

namespace CandidatePair.SupportsGeneratedResources

private theorem orILeftSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedResourceContract first witness expected flags txCtx
        ⟨base, firstMods⟩)
    (branch : branchBase base) :
    (result.withSelector trueElement).Supports fun witness =>
      GeneratedResourceContract (.or_i first second) witness expected flags
        txCtx ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector trueElement) witness selected
  exact contract.orI_left branch

private theorem orIRightSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedResourceContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (branch : branchBase base) :
    (result.withSelector falseElement).Supports fun witness =>
      GeneratedResourceContract (.or_i first second) witness expected flags
        txCtx ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector falseElement) witness selected
  exact contract.orI_right branch

private theorem andorTrueSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedResourceContract first witness true flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedResourceContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedResourceContract (.andor first second third) witness expected
        flags txCtx ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  exact firstContract.andorTrue firstUnit branchContract branch

private theorem andorFalseSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedResourceContract first witness false flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedResourceContract third witness expected flags txCtx
        ⟨base, thirdMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedResourceContract (.andor first second third) witness expected
        flags txCtx ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  exact firstContract.andorFalse firstUnit branchContract branch

/-- Resource-aware generated support for `and_b`. -/
theorem and_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.combine secondPair.sat
         dsat := ((firstPair.dsat.combine secondPair.dsat).select
           ((firstPair.dsat.combine secondPair.sat).markOvercomplete)).select
           ((firstPair.sat.combine secondPair.dsat).markOvercomplete) } :
        CandidatePair) scriptCtx (.and_b first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true }⟩ flags txCtx := by
  refine ⟨.and_b firstSupported.typed secondSupported.typed, ?_, ?_⟩
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    exact firstContract.andB_same secondContract
  · have canonical : (firstPair.dsat.combine secondPair.dsat).Supports
        (fun witness => GeneratedResourceContract (.and_b first second)
          witness false flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            n := firstMods.n || (firstMods.z && secondMods.n)
            d := firstMods.d && secondMods.d
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.dsat) witness selected
      exact firstContract.andB_same secondContract
    exact (canonical.select
      (CandidateResult.supports_markOvercomplete _ _)).select
      (CandidateResult.supports_markOvercomplete _ _)

/-- Resource-aware generated support for `or_b`. -/
theorem or_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx)
    (secondD : secondMods.d = true) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := ((firstPair.sat.combine secondPair.dsat).select
           (firstPair.dsat.combine secondPair.sat)).select
           ((firstPair.sat.combine secondPair.sat).markOvercomplete)
         dsat := firstPair.dsat.combine secondPair.dsat } : CandidatePair)
      scriptCtx (.or_b first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        d := true
        u := true }⟩ flags txCtx := by
  refine ⟨.or_b firstSupported.typed firstD secondSupported.typed secondD,
    ?_, ?_⟩
  · have left : (firstPair.sat.combine secondPair.dsat).Supports
        (fun witness => GeneratedResourceContract (.or_b first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.sat.combine secondSupported.dsat) witness selected
      simpa using firstContract.orB_path secondContract (by simp)
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedResourceContract (.or_b first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      simpa using firstContract.orB_path secondContract (by simp)
    exact (left.select right).select
      (CandidateResult.supports_markOvercomplete _ _)
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    simpa using firstContract.orB_path secondContract (by simp)

/-- Resource-aware generated support for both satisfaction paths of `or_c`. -/
theorem or_c
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.V, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat) } : CandidatePair)
      scriptCtx (.or_c first second)
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ flags txCtx := by
  refine ⟨.or_c firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, CandidateResult.supports_impossible _⟩
  change (firstPair.sat.select
    (firstPair.dsat.combine secondPair.sat)).Supports _
  have left : firstPair.sat.Supports
      (fun witness => GeneratedResourceContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) :=
    firstSupported.sat.mono fun _ contract => contract.orC_left firstUnit
  have right : (firstPair.dsat.combine secondPair.sat).Supports
      (fun witness => GeneratedResourceContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) := by
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.sat) witness selected
    exact firstContract.orC_right firstUnit secondContract
  exact left.select right

/-- Resource-aware generated support for every usable path of `or_d`. -/
theorem or_d
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.B, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat)
         dsat := firstPair.dsat.combine secondPair.dsat } : CandidatePair)
      scriptCtx (.or_d first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ flags txCtx := by
  refine ⟨.or_d firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, ?_⟩
  · change (firstPair.sat.select
      (firstPair.dsat.combine secondPair.sat)).Supports _
    have left : firstPair.sat.Supports
        (fun witness => GeneratedResourceContract (.or_d first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) :=
      firstSupported.sat.mono fun _ contract => contract.orD_left firstUnit
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedResourceContract (.or_d first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      exact firstContract.orD_right firstUnit secondContract
    exact left.select right
  · change (firstPair.dsat.combine secondPair.dsat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    exact firstContract.orD_right firstUnit secondContract

/-- Resource-aware generated support for both tagged branches of `or_i`. -/
theorem or_i
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨base, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := (firstPair.sat.withSelector trueElement).select
           (secondPair.sat.withSelector falseElement)
         dsat := (firstPair.dsat.withSelector trueElement).select
           (secondPair.dsat.withSelector falseElement) } : CandidatePair)
      scriptCtx (.or_i first second)
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ flags txCtx := by
  refine ⟨.or_i firstSupported.typed secondSupported.typed branch rfl, ?_, ?_⟩
  · change ((firstPair.sat.withSelector trueElement).select
      (secondPair.sat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.sat branch).select
      (orIRightSupport secondSupported.sat branch)
  · change ((firstPair.dsat.withSelector trueElement).select
      (secondPair.dsat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.dsat branch).select
      (orIRightSupport secondSupported.dsat branch)

/-- Resource-aware generated support for every usable `andor` path. -/
theorem andor
    {firstPair secondPair thirdPair : CandidatePair}
    {scriptCtx : ScriptContext} {first second third : CoreFragment}
    {base : BaseType} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (thirdSupported : CandidatePair.SupportsGeneratedResources thirdPair
      scriptCtx third ⟨base, thirdMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := (firstPair.sat.combine secondPair.sat).select
           (firstPair.dsat.combine thirdPair.sat)
         dsat := (firstPair.dsat.combine thirdPair.dsat).select
           ((firstPair.sat.combine secondPair.dsat).markNonCanonical) } :
        CandidatePair)
      scriptCtx (.andor first second third)
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ flags txCtx := by
  refine ⟨.andor firstSupported.typed firstD firstUnit secondSupported.typed
    thirdSupported.typed branch rfl, ?_, ?_⟩
  · change ((firstPair.sat.combine secondPair.sat).select
      (firstPair.dsat.combine thirdPair.sat)).Supports _
    exact (andorTrueSupport firstSupported.sat secondSupported.sat
      firstUnit branch).select
      (andorFalseSupport firstSupported.dsat thirdSupported.sat
        firstUnit branch)
  · change ((firstPair.dsat.combine thirdPair.dsat).select
      ((firstPair.sat.combine secondPair.dsat).markNonCanonical)).Supports _
    have canonical := andorFalseSupport (second := second)
      (secondMods := secondMods) firstSupported.dsat thirdSupported.dsat
      firstUnit branch
    have noncanonical := CandidateResult.Supports.markNonCanonical
      (andorTrueSupport (third := third) (thirdMods := thirdMods)
        firstSupported.sat secondSupported.dsat firstUnit branch)
    exact canonical.select noncanonical

/-- Resource-aware generated support for the `d` wrapper. -/
theorem d
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.V, mods⟩ flags txCtx) (zeroArg : mods.z = true) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := pair.sat.withSelector trueElement
         dsat := .usable [falseElement] false } : CandidatePair)
      scriptCtx (.d fragment)
      ⟨.B, { o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩
      flags txCtx := by
  refine ⟨.d_wrap supported.typed zeroArg, ?_, ?_⟩
  · intro witness selected
    rw [CandidateResult.withSelector_usableWitness_iff] at selected
    obtain ⟨inner, innerSelected, rfl⟩ := selected
    exact (supported.sat inner innerSelected).d scriptCtx zeroArg
  · apply CandidateResult.supports_usable
    exact GeneratedResourceContract.d_false fragment scriptCtx flags txCtx

end CandidatePair.SupportsGeneratedResources

end LeanMiniscript.Properties
