import LeanMiniscript.Properties.SatisfactionBudgetConnectorProofs
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs
import LeanMiniscript.Properties.SatisfactionResourceGuardProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

namespace ExecutesBudgetFrame

theorem dup (value : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.op .OP_DUP] [value] [value, value] flags ctx 0 :=
  of_resource_zero (ExecutesResourceFrame.dup value flags ctx) rfl

theorem size (value : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.op .OP_SIZE] [value] [scriptNat value.size, value] flags ctx 0 :=
  of_resource_zero (ExecutesResourceFrame.size value flags ctx) rfl

theorem zeroNotEqual (operand : StackElement) (value : Int) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes = .ok value) :
    ExecutesBudgetFrame [.op .OP_0NOTEQUAL] [operand] [boolToElement (value != 0)] flags ctx 0 :=
  of_resource_zero (ExecutesResourceFrame.zeroNotEqual operand value flags ctx decoded) rfl

end ExecutesBudgetFrame

namespace GeneratedBudgetContract

theorem d
    {fragment : CoreFragment} {witness : Witness} (scriptCtx : ScriptContext)
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness true flags txCtx
      ⟨.V, mods⟩) (zeroArg : mods.z = true) :
    GeneratedBudgetContract (.d fragment)
      (witness.withSelector trueElement) true flags txCtx
      ⟨.B, {
        o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩ := by
  cases contract with
  | @v _ budget input expectedTrue executed frame funded =>
      have shape := input.zeroArgs zeroArg
      have child : ExecutesBudgetFrame (compile fragment) [] [] flags txCtx budget := by
        simpa [shape] using frame
      have selected := child.withSuffix (suffix := [trueElement])
      have conditional := ifThenBudget (compile_balancedControlFlow fragment)
        (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg)
        (selector := trueElement) (by simpa using selected)
      have concrete := (ExecutesBudgetFrame.dup trueElement flags txCtx).append conditional
      have childExec := executed
      rw [shape] at childExec
      apply GeneratedBudgetContract.b
      · refine ⟨input.bounded.withSelector trueElement_size_le, ?_, ?_, ?_⟩
        · simp
        · intro _
          exact ⟨trueElement, by simp [shape]⟩
        · intro _ _
          exact ⟨trueElement, [], by simp [shape], by decide⟩
      · exact BooleanResultFacts.canonical true _ flags
      · simpa [shape, boolToElement] using childExec.d
      · simpa [compile, compileWithKeyHash, shape, boolToElement] using concrete
      · simp only [witnessPayload_selector]
        omega

theorem d_false
    (fragment : CoreFragment) (scriptCtx : ScriptContext)
    (flags : ScriptFlags) (txCtx : TxContext) :
    GeneratedBudgetContract (.d fragment) [falseElement] false flags txCtx
      ⟨.B, { o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩ := by
  have skipped := ExecutesBudgetFrame.empty [falseElement] flags txCtx
  have conditional := ifThenBudget (compile_balancedControlFlow fragment)
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg)
    (selector := falseElement) (by simpa using skipped)
  have concrete := (ExecutesBudgetFrame.dup falseElement flags txCtx).append conditional
  apply generatedBudgetB_of_contract
    (GeneratedResourceContract.d_false fragment scriptCtx flags txCtx).toGeneratedContract
  · simpa [compile, compileWithKeyHash, Witness.toInitialStack] using concrete
  · exact Nat.zero_le _

theorem j
    {fragment : CoreFragment} {witness : Witness}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness true flags txCtx
      ⟨.B, mods⟩) (nonzero : mods.n = true) :
    GeneratedBudgetContract (.j fragment) witness true flags txCtx
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed resources funded =>
    obtain ⟨top, rest, shape, topNonempty⟩ := input.nonzeroTop nonzero rfl
    have topBound := input.bounded.runtimeTop shape
    have decoded := decodeScriptNum_scriptNat_of_le_maxScriptElementSize
      topBound flags.minimalData
    have childResources : ExecutesBudgetFrame (compile fragment)
        (top :: rest) [result] flags txCtx budget := by
      simpa [shape] using resources
    have sized := (ExecutesBudgetFrame.size top flags txCtx).withSuffix
      (suffix := rest)
    have normalized := (ExecutesBudgetFrame.zeroNotEqual (scriptNat top.size)
      (Int.ofNat top.size) flags txCtx decoded).withSuffix
        (suffix := top :: rest)
    have prefixFrame := sized.append normalized
    let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
    have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some frame := by
      simpa [frame] using splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := [])
    have sizeNonzero : Int.ofNat top.size ≠ 0 :=
      Int.ofNat_ne_zero.mpr topNonempty
    have nonzeroBool : (Int.ofNat top.size != 0) = true :=
      bne_iff_ne.mpr sizeNonzero
    have selectorEq : boolToElement (Int.ofNat top.size != 0) = trueElement := by
      rw [nonzeroBool]
      rfl
    have selected : ExecutesBudgetFrame
        (frame.select (castToBool
          (boolToElement (Int.ofNat top.size != 0))))
        (top :: rest) [result] flags txCtx budget := by
      rw [selectorEq]
      simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
        childResources
    have selectorMinimal : minimalIfSatisfied flags txCtx.sigVersion
        (boolToElement (Int.ofNat top.size != 0)) := by
      rw [selectorEq]
      exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    have conditional := ExecutesBudgetFrame.ifSelected split
      selectorMinimal selected
    have concrete := prefixFrame.append conditional
    have childExec := executed
    rw [shape] at childExec
    apply GeneratedBudgetContract.b
    · refine ⟨input.bounded, ?_, ?_, ?_⟩
      · simp
      · intro enabled
        exact input.oneArg enabled
      · intro _ _
        exact ⟨top, rest, shape, topNonempty⟩
    · exact facts.monoUnit (by simp)
    · simpa [shape] using childExec.j topNonempty decoded
    · simpa [compile, compileWithKeyHash, List.append_assoc, shape] using concrete
    · exact funded

theorem j_false
    {mods : CorrectnessModifiers} (fragment : CoreFragment)
    (flags : ScriptFlags) (txCtx : TxContext) :
    GeneratedBudgetContract (.j fragment) [falseElement] false flags txCtx
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ := by
  have decoded : decodeScriptNum (scriptNat falseElement.size)
      flags.minimalData maxArithmeticScriptNumBytes = .ok 0 := by
    have sizeZero : falseElement.size = 0 := by rfl
    simpa [sizeZero, scriptNat, scriptNum_zero] using
      (decodeScriptNum_scriptNat_of_lt
        (n := 0) (by change 0 < 2147483648; omega) flags.minimalData)
  have sized := ExecutesBudgetFrame.size falseElement flags txCtx
  have normalized := (ExecutesBudgetFrame.zeroNotEqual
    (scriptNat falseElement.size) 0 flags txCtx decoded).withSuffix
      (suffix := [falseElement])
  have prefixFrame := sized.append normalized
  let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
  have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifThen
      (compile_balancedControlFlow fragment) (suffix := [])
  have skipped : ExecutesBudgetFrame
      (frame.select (castToBool falseElement)) [falseElement] [falseElement]
      flags txCtx 0 := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      ExecutesBudgetFrame.empty [falseElement] flags txCtx
  have conditional := ExecutesBudgetFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) skipped
  have concrete := prefixFrame.append conditional
  apply generatedBudgetB_of_contract
    (GeneratedResourceContract.j_false (mods := mods) fragment flags txCtx).toGeneratedContract
  · simpa [compile, compileWithKeyHash, Witness.toInitialStack, List.append_assoc, boolToElement] using concrete
  · exact Nat.zero_le _

end GeneratedBudgetContract

namespace CandidatePair.SupportsGeneratedBudgets

private theorem orILeftSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedBudgetContract first witness expected flags txCtx
        ⟨base, firstMods⟩)
    (branch : branchBase base) :
    (result.withSelector trueElement).Supports fun witness =>
      GeneratedBudgetContract (.or_i first second) witness expected flags
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
      GeneratedBudgetContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (branch : branchBase base) :
    (result.withSelector falseElement).Supports fun witness =>
      GeneratedBudgetContract (.or_i first second) witness expected flags
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
      GeneratedBudgetContract first witness true flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedBudgetContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedBudgetContract (.andor first second third) witness expected
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
      GeneratedBudgetContract first witness false flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedBudgetContract third witness expected flags txCtx
        ⟨base, thirdMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedBudgetContract (.andor first second third) witness expected
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

/-- Budget-aware generated support for `and_b`. -/
theorem and_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets
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
        (fun witness => GeneratedBudgetContract (.and_b first second)
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

/-- Budget-aware generated support for `or_b`. -/
theorem or_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx)
    (secondD : secondMods.d = true) :
    CandidatePair.SupportsGeneratedBudgets
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
        (fun witness => GeneratedBudgetContract (.or_b first second)
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
        (fun witness => GeneratedBudgetContract (.or_b first second)
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

/-- Budget-aware generated support for both satisfaction paths of `or_c`. -/
theorem or_c
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨.V, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets
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
      (fun witness => GeneratedBudgetContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) :=
    firstSupported.sat.mono fun _ contract => contract.orC_left firstUnit
  have right : (firstPair.dsat.combine secondPair.sat).Supports
      (fun witness => GeneratedBudgetContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) := by
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.sat) witness selected
    exact firstContract.orC_right firstUnit secondContract
  exact left.select right

/-- Budget-aware generated support for every usable path of `or_d`. -/
theorem or_d
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨.B, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets
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
        (fun witness => GeneratedBudgetContract (.or_d first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) :=
      firstSupported.sat.mono fun _ contract => contract.orD_left firstUnit
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedBudgetContract (.or_d first second)
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

/-- Budget-aware generated support for both tagged branches of `or_i`. -/
theorem or_i
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨base, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedBudgets
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

/-- Budget-aware generated support for every usable `andor` path. -/
theorem andor
    {firstPair secondPair thirdPair : CandidatePair}
    {scriptCtx : ScriptContext} {first second third : CoreFragment}
    {base : BaseType} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (thirdSupported : CandidatePair.SupportsGeneratedBudgets thirdPair
      scriptCtx third ⟨base, thirdMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedBudgets
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

/-- Budget-aware generated support for the `d` wrapper. -/
theorem d
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.V, mods⟩ flags txCtx) (zeroArg : mods.z = true) :
    CandidatePair.SupportsGeneratedBudgets
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
    exact GeneratedBudgetContract.d_false fragment scriptCtx flags txCtx

end CandidatePair.SupportsGeneratedBudgets

namespace CandidatePair.SupportsGeneratedBudgets

/-- Candidate-wide budget support for the `j` nonempty guard. -/
theorem j
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) (nonzero : mods.n = true) :
    CandidatePair.SupportsGeneratedBudgets
      ({ sat := pair.sat
         dsat := (CandidateResult.usable [falseElement] false).select
           (pair.dsat.requireNonemptyRuntimeTop.markNonCanonical) } : CandidatePair)
      scriptCtx (.j fragment)
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ flags txCtx := by
  refine ⟨.j_wrap supported.typed nonzero, ?_, ?_⟩
  · intro witness selected
    exact (supported.sat witness selected).j nonzero
  · intro witness selected
    have witnessShape := CandidateResult.usable_false_select_witness selected
    subst witness
    exact GeneratedBudgetContract.j_false (mods := mods) fragment flags txCtx

end CandidatePair.SupportsGeneratedBudgets

end LeanMiniscript.Properties
