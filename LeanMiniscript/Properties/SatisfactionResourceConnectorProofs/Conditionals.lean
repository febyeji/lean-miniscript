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

/-- The resource frame and selected summaries carried by a contract whose base
    type can sit inside a branch (`B`, `K`, or `V`). -/
private theorem resourceFrame
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx
      ⟨base, mods⟩) (branch : branchBase base) :
    ∃ outputs trace dynamic,
      ExecutesResourceFrame (compile fragment) witness.toInitialStack outputs
        flags txCtx trace dynamic ∧
      selectedStackSummary fragment expected = some trace ∧
      selectedOpSummary fragment expected = some dynamic := by
  cases contract with
  | b _ _ _ resources stackSelected opSelected =>
      exact ⟨_, _, _, resources, stackSelected, opSelected⟩
  | v _ _ _ resources stackSelected opSelected =>
      exact ⟨_, _, _, resources, stackSelected, opSelected⟩
  | k _ _ _ _ _ _ _ resources stackSelected opSelected =>
      exact ⟨_, _, _, resources, stackSelected, opSelected⟩
  | w => simp [branchBase] at branch

/-- Attach resource evidence to a standard `B`, `K`, or `V` generated
    contract: any resource frame from the witness stack aligns with the exact
    outputs of the standard execution. -/
private theorem ofGeneratedContract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    {outputs : Stack} {trace : StackTraceBound} {dynamic : Nat}
    (standard : GeneratedContract fragment witness expected flags txCtx
      ⟨base, mods⟩) (branch : branchBase base)
    (resources : ExecutesResourceFrame (compile fragment) witness.toInitialStack
      outputs flags txCtx trace dynamic)
    (stackSelected : selectedStackSummary fragment expected = some trace)
    (opSelected : selectedOpSummary fragment expected = some dynamic) :
    GeneratedResourceContract fragment witness expected flags txCtx
      ⟨base, mods⟩ := by
  cases standard with
  | b input facts executed =>
      exact .b input facts executed (resources.alignOutputs executed)
        stackSelected opSelected
  | v input expectedTrue executed =>
      exact .v input expectedTrue executed (resources.alignOutputs executed)
        stackSelected opSelected
  | k input ownArgs key signature stackShape executed checked =>
      have target : ExecutesStackFrame (compile fragment)
          witness.toInitialStack [key, signature] flags txCtx := by
        rw [stackShape]
        simpa using executed.withSuffix (suffix := [signature])
      exact .k input ownArgs key signature stackShape executed checked
        (resources.alignOutputs target) stackSelected opSelected
  | w => simp [branchBase] at branch

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
  obtain ⟨_, _, _, resources, stackSelected, opSelected⟩ :=
    contract.resourceFrame branch
  obtain ⟨_, _, bounded, targetStack, targetOps⟩ :=
    orILeftResources (second := second) resources stackSelected opSelected
  refine ofGeneratedContract ?_ branch
    (by simpa only [Witness.toInitialStack_withSelector] using bounded)
    targetStack targetOps
  have standard := contract.toGeneratedContract
  cases base with
  | B => exact GeneratedContract.orILeft_b standard
  | K => exact GeneratedContract.orILeft_k standard
  | V => exact GeneratedContract.orILeft_v standard
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
  obtain ⟨_, _, _, resources, stackSelected, opSelected⟩ :=
    contract.resourceFrame branch
  obtain ⟨_, _, bounded, targetStack, targetOps⟩ :=
    orIRightResources (first := first) resources stackSelected opSelected
  refine ofGeneratedContract ?_ branch
    (by simpa only [Witness.toInitialStack_withSelector] using bounded)
    targetStack targetOps
  have standard := contract.toGeneratedContract
  cases base with
  | B => exact GeneratedContract.orIRight_b standard
  | K => exact GeneratedContract.orIRight_k standard
  | V => exact GeneratedContract.orIRight_v standard
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
    obtain ⟨_, _, _, branchResources, branchStack, branchOps⟩ :=
      secondContract.resourceFrame branch
    obtain ⟨_, _, bounded, targetStack, targetOps⟩ :=
      andorTrueResources (third := third) firstResources branchResources
        (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        firstStack branchStack firstOps branchOps
    refine ofGeneratedContract ?_ branch
      (by simpa only [Witness.toInitialStack_combine] using bounded)
      targetStack targetOps
    have firstStandard := GeneratedContract.b firstInput firstFacts
      firstExecuted
    have standard := secondContract.toGeneratedContract
    cases base with
    | B => exact GeneratedContract.andorTrue_b firstStandard firstUnit standard
    | K => exact GeneratedContract.andorTrue_k firstStandard firstUnit standard
    | V => exact GeneratedContract.andorTrue_v firstStandard firstUnit standard
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
    obtain ⟨_, _, _, branchResources, branchStack, branchOps⟩ :=
      thirdContract.resourceFrame branch
    obtain ⟨_, _, bounded, targetStack, targetOps⟩ :=
      andorFalseResources (second := second) firstResources branchResources
        (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        firstStack branchStack firstOps branchOps
    refine ofGeneratedContract ?_ branch
      (by simpa only [Witness.toInitialStack_combine] using bounded)
      targetStack targetOps
    have firstStandard := GeneratedContract.b firstInput firstFacts
      firstExecuted
    have standard := thirdContract.toGeneratedContract
    cases base with
    | B => exact GeneratedContract.andorFalse_b firstStandard firstUnit standard
    | K => exact GeneratedContract.andorFalse_k firstStandard firstUnit standard
    | V => exact GeneratedContract.andorFalse_v firstStandard firstUnit standard
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
    have conditional := ifThenFrame (compile_balancedControlFlow fragment)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg)
      (selected := by
        simpa using childResources.withSuffix (suffix := [trueElement]))
    have concrete :=
      (ExecutesResourceFrame.dup trueElement flags txCtx).append conditional
    have bounded : ExecutesResourceFrame (compile (.d fragment)) [trueElement]
        [trueElement] flags txCtx
        ((StackTraceBound.dup.sequential StackTraceBound.branch).sequential
          trace) dynamic := by
      simpa [compile, compileWithKeyHash,
        StackTraceBound.sequential_assoc] using concrete
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
  have conditional := ifThenFrame (compile_balancedControlFlow fragment)
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg)
    (inputs := [falseElement]) (outputs := [falseElement])
    (selected := by
      simpa using ExecutesResourceFrame.empty [falseElement] flags txCtx)
  have concrete :=
    (ExecutesResourceFrame.dup falseElement flags txCtx).append conditional
  have resources : ExecutesResourceFrame (compile (.d fragment)) [falseElement]
      [falseElement] flags txCtx
      (StackTraceBound.dup.sequential StackTraceBound.branch) 0 := by
    simpa [compile, compileWithKeyHash,
      StackTraceBound.branch_sequential_empty] using concrete
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
