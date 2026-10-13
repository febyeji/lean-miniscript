import LeanMiniscript.Properties.SatisfactionResourceProofs
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs.Frames

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

namespace GeneratedResourceContract

/-!
# Resource-aware connectors: `or_i`, `andor`, and `d:`

Resource-aware `GeneratedResourceContract` composition for the combinators that
select a branch with `IF`.
-/

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

end LeanMiniscript.Properties
