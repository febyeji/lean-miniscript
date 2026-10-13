import LeanMiniscript.Properties.SatisfactionResourceProofs
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs.Frames

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

namespace GeneratedResourceContract

/-!
# Resource-aware connectors: `and_b`, `or_b`, `or_c`, `or_d`

Resource-aware `GeneratedResourceContract` composition for the boolean and
short-circuit connectives.
-/

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

end GeneratedResourceContract

end LeanMiniscript.Properties
