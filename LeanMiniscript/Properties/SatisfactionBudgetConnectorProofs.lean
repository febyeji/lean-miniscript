import LeanMiniscript.Properties.SatisfactionBudgetAtomicProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

private theorem boolAndFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesBudgetFrame [.op .OP_BOOLAND] (order.outputs saved result)
      [boolToElement ((savedValue != 0) && (resultValue != 0))]
      flags ctx 0 := by
  apply ExecutesBudgetFrame.of_zero
  · intro rest altStack
    cases order with
    | savedFirst =>
        exact Eval.booland saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
    | resultFirst =>
        simpa [Bool.and_comm, WStackOrder.outputs] using
          (Eval.booland result saved resultValue savedValue rest [] altStack
            flags ctx _ decoded Eval.done)
  · rfl

private theorem boolOrFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesBudgetFrame [.op .OP_BOOLOR] (order.outputs saved result)
      [boolToElement ((savedValue != 0) || (resultValue != 0))]
      flags ctx 0 := by
  apply ExecutesBudgetFrame.of_zero
  · intro rest altStack
    cases order with
    | savedFirst =>
        exact Eval.boolor saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
    | resultFirst =>
        simpa [Bool.or_comm, WStackOrder.outputs] using
          (Eval.boolor result saved resultValue savedValue rest [] altStack
            flags ctx _ decoded Eval.done)
  · rfl

private theorem ifdupTrueFrame
    {value : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (truth : castToBool value = true) :
    ExecutesBudgetFrame [.op .OP_IFDUP] [value] [value, value]
      flags ctx 0 := by
  apply ExecutesBudgetFrame.of_zero
  · intro rest altStack
    exact Eval.ifdup_true value rest altStack [] flags ctx _ truth Eval.done
  · rfl

private theorem ifdupFalseFrame
    {value : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (falsy : castToBool value = false) :
    ExecutesBudgetFrame [.op .OP_IFDUP] [value] [value]
      flags ctx 0 := by
  apply ExecutesBudgetFrame.of_zero
  · intro rest altStack
    exact Eval.ifdup_false value rest altStack [] flags ctx _ falsy Eval.done
  · rfl

private theorem ifElseLeftFrame
    {firstScript secondScript : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {budget : Nat}
    (firstBalanced : BalancedControlFlow firstScript)
    (secondBalanced : BalancedControlFlow secondScript)
    (selected : ExecutesBudgetFrame firstScript inputs outputs flags ctx
      budget) :
    ExecutesBudgetFrame
      ([.op .OP_IF] ++ firstScript ++ [.op .OP_ELSE] ++ secondScript ++
        [.op .OP_ENDIF])
      (trueElement :: inputs) outputs flags ctx
      budget := by
  let frame : ConditionalFrame := {
    branches := [firstScript, secondScript]
    after := [] }
  have split : splitConditional
      (firstScript ++ [.op .OP_ELSE] ++ secondScript ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifElse firstBalanced
      secondBalanced
  have selected' : ExecutesBudgetFrame
      (frame.select (castToBool trueElement)) inputs outputs flags ctx
      budget := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected
  simpa using ExecutesBudgetFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) selected'

private theorem ifElseRightFrame
    {firstScript secondScript : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {budget : Nat}
    (firstBalanced : BalancedControlFlow firstScript)
    (secondBalanced : BalancedControlFlow secondScript)
    (selected : ExecutesBudgetFrame secondScript inputs outputs flags ctx
      budget) :
    ExecutesBudgetFrame
      ([.op .OP_IF] ++ firstScript ++ [.op .OP_ELSE] ++ secondScript ++
        [.op .OP_ENDIF])
      (falseElement :: inputs) outputs flags ctx
      budget := by
  let frame : ConditionalFrame := {
    branches := [firstScript, secondScript]
    after := [] }
  have split : splitConditional
      (firstScript ++ [.op .OP_ELSE] ++ secondScript ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifElse firstBalanced
      secondBalanced
  have selected' : ExecutesBudgetFrame
      (frame.select (castToBool falseElement)) inputs outputs flags ctx
      budget := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      selected
  simpa using ExecutesBudgetFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) selected'

theorem ifThenBudget
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesBudgetFrame (if castToBool selector then body else []) inputs outputs flags ctx budget) :
    ExecutesBudgetFrame ([.op .OP_IF] ++ body ++ [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx budget := by
  let frame : ConditionalFrame := { branches := [body], after := [] }
  have split : splitConditional (body ++ [.op .OP_ENDIF]) = some frame := by
    simpa [frame] using splitConditional_balanced_ifThen balanced (suffix := [])
  apply ExecutesBudgetFrame.ifSelected split minimal
  cases truth : castToBool selector <;>
    simpa [frame, ConditionalFrame.select, selectConditionalBranches, truth] using selected

theorem notifThenBudget
    {body : Script} {selector : StackElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (balanced : BalancedControlFlow body)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesBudgetFrame (if castToBool selector then [] else body) inputs outputs flags ctx budget) :
    ExecutesBudgetFrame ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF])
      (selector :: inputs) outputs flags ctx budget := by
  let frame : ConditionalFrame := { branches := [body], after := [] }
  have split : splitConditional (body ++ [.op .OP_ENDIF]) = some frame := by
    simpa [frame] using splitConditional_balanced_ifThen balanced (suffix := [])
  apply ExecutesBudgetFrame.notifSelected split minimal
  cases truth : castToBool selector <;>
    simpa [frame, ConditionalFrame.select, selectConditionalBranches, truth] using selected

private theorem andorBudget
    {first second third : CoreFragment} {choice : Bool} {selector : StackElement}
    {firstInputs branchInputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {firstBudget branchBudget : Nat}
    (firstFrame : ExecutesBudgetFrame (compile first) firstInputs [selector] flags ctx firstBudget)
    (branchFrame : ExecutesBudgetFrame (compile (if choice then second else third)) branchInputs outputs flags ctx branchBudget)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = choice) :
    ExecutesBudgetFrame (compile (.andor first second third))
      (firstInputs ++ branchInputs) outputs flags ctx (firstBudget + branchBudget) := by
  let frame : ConditionalFrame := { branches := [compile third, compile second], after := [] }
  have split : splitConditional
      (compile third ++ [.op .OP_ELSE] ++ compile second ++ [.op .OP_ENDIF]) = some frame := by
    simpa [frame] using splitConditional_balanced_ifElse
      (compile_balancedControlFlow third) (compile_balancedControlFlow second)
  have selected : ExecutesBudgetFrame (frame.select (!castToBool selector)) branchInputs outputs flags ctx branchBudget := by
    cases choice <;> simpa [frame, ConditionalFrame.select, selectConditionalBranches, truth] using branchFrame
  have conditional := ExecutesBudgetFrame.notifSelected split minimal selected
  simpa [compile, compileWithKeyHash, List.append_assoc] using
    (firstFrame.withSuffix (suffix := branchInputs)).append conditional

namespace GeneratedBudgetContract

theorem andB_same
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness expected flags
      txCtx ⟨.B, firstMods⟩)
    (secondContract : GeneratedBudgetContract second secondWitness expected
      flags txCtx ⟨.W, secondMods⟩) :
    GeneratedBudgetContract (.and_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true }⟩ := by
  cases firstContract with
  | @b _ firstResult firstValue firstBudget firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases secondContract with
    | @w _ secondResult secondValue secondBudget secondInput order secondFacts secondExecuted secondFrame secondFunded =>
      have children := (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append
        (secondFrame firstResult)
      have full := children.append (boolAndFrame (firstFacts.binaryDecoded secondFacts order))
      apply generatedBudgetB_of_contract
        (GeneratedContract.andB (.b firstInput firstFacts firstExecuted)
          (.w secondInput order secondFacts secondExecuted) (by cases expected <;> decide))
      · simpa [compile, compileWithKeyHash, List.append_assoc] using full
      · simp only [witnessPayload_combine]
        omega

theorem orB_path
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness firstExpected
      flags txCtx ⟨.B, firstMods⟩)
    (secondContract : GeneratedBudgetContract second secondWitness
      secondExpected flags txCtx ⟨.W, secondMods⟩)
    (_usable : ¬ (firstExpected = true ∧ secondExpected = true)) :
    GeneratedBudgetContract (.or_b first second)
      (Witness.combine firstWitness secondWitness)
      (firstExpected || secondExpected) flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        d := true
        u := true }⟩ := by
  cases firstContract with
  | @b _ firstResult firstValue firstBudget firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases secondContract with
    | @w _ secondResult secondValue secondBudget secondInput order secondFacts secondExecuted secondFrame secondFunded =>
      have children := (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append
        (secondFrame firstResult)
      have full := children.append (boolOrFrame (firstFacts.binaryDecoded secondFacts order))
      apply generatedBudgetB_of_contract
        (GeneratedContract.orB (.b firstInput firstFacts firstExecuted)
          (.w secondInput order secondFacts secondExecuted) rfl)
      · simpa [compile, compileWithKeyHash, List.append_assoc] using full
      · simp only [witnessPayload_combine]
        omega

theorem orI_left
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract first witness expected flags txCtx
      ⟨base, firstMods⟩) (branch : branchBase base) :
    GeneratedBudgetContract (.or_i first second)
      (witness.withSelector trueElement) expected flags txCtx
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ := by
  cases contract with
  | b input facts executed frame funded =>
      apply generatedBudgetB_of_contract
        (GeneratedContract.orILeft_b (second := second) (secondMods := secondMods)
          (.b input facts executed))
      · simpa [compile, compileWithKeyHash] using
          ifElseLeftFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | v input truth executed frame funded =>
      apply generatedBudgetV_of_contract
        (GeneratedContract.orILeft_v (second := second) (secondMods := secondMods)
          (.v input truth executed))
      · simpa [compile, compileWithKeyHash] using
          ifElseLeftFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | k input ownArgs key signature shape executed checked frame funded =>
      apply generatedBudgetK_of_contract
        (GeneratedContract.orILeft_k (second := second) (secondMods := secondMods)
          (.k input ownArgs key signature shape executed checked))
      · simpa [compile, compileWithKeyHash] using
          ifElseLeftFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | w => simp [branchBase] at branch

theorem orI_right
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract second witness expected flags txCtx
      ⟨base, secondMods⟩) (branch : branchBase base) :
    GeneratedBudgetContract (.or_i first second)
      (witness.withSelector falseElement) expected flags txCtx
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ := by
  cases contract with
  | b input facts executed frame funded =>
      apply generatedBudgetB_of_contract
        (GeneratedContract.orIRight_b (first := first) (firstMods := firstMods)
          (.b input facts executed))
      · simpa [compile, compileWithKeyHash] using
          ifElseRightFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | v input truth executed frame funded =>
      apply generatedBudgetV_of_contract
        (GeneratedContract.orIRight_v (first := first) (firstMods := firstMods)
          (.v input truth executed))
      · simpa [compile, compileWithKeyHash] using
          ifElseRightFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | k input ownArgs key signature shape executed checked frame funded =>
      apply generatedBudgetK_of_contract
        (GeneratedContract.orIRight_k (first := first) (firstMods := firstMods)
          (.k input ownArgs key signature shape executed checked))
      · simpa [compile, compileWithKeyHash] using
          ifElseRightFrame (compile_balancedControlFlow first)
            (compile_balancedControlFlow second) frame
      · simp only [witnessPayload_selector]
        omega
  | w => simp [branchBase] at branch

theorem andorTrue
    {first second third : CoreFragment}
    {firstWitness secondWitness : Witness} {expected : Bool}
    {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness true flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedBudgetContract second secondWitness expected
      flags txCtx ⟨base, secondMods⟩) (branch : branchBase base) :
    GeneratedBudgetContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases secondContract with
    | b input facts executed frame funded =>
        apply generatedBudgetB_of_contract
          (GeneratedContract.andorTrue_b (third := third) (thirdMods := thirdMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.b input facts executed))
        · simpa using andorBudget (choice := true) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | v input truth executed frame funded =>
        apply generatedBudgetV_of_contract
          (GeneratedContract.andorTrue_v (third := third) (thirdMods := thirdMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.v input truth executed))
        · simpa using andorBudget (choice := true) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | k input ownArgs key signature shape executed checked frame funded =>
        apply generatedBudgetK_of_contract
          (GeneratedContract.andorTrue_k (third := third) (thirdMods := thirdMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.k input ownArgs key signature shape executed checked))
        · simpa using andorBudget (choice := true) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | w => simp [branchBase] at branch

theorem andorFalse
    {first second third : CoreFragment}
    {firstWitness thirdWitness : Witness} {expected : Bool}
    {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedBudgetContract third thirdWitness expected
      flags txCtx ⟨base, thirdMods⟩) (branch : branchBase base) :
    GeneratedBudgetContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases thirdContract with
    | b input facts executed frame funded =>
        apply generatedBudgetB_of_contract
          (GeneratedContract.andorFalse_b (second := second) (secondMods := secondMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.b input facts executed))
        · simpa using andorBudget (choice := false) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | v input truth executed frame funded =>
        apply generatedBudgetV_of_contract
          (GeneratedContract.andorFalse_v (second := second) (secondMods := secondMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.v input truth executed))
        · simpa using andorBudget (choice := false) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | k input ownArgs key signature shape executed checked frame funded =>
        apply generatedBudgetK_of_contract
          (GeneratedContract.andorFalse_k (second := second) (secondMods := secondMods)
            (.b firstInput firstFacts firstExecuted) firstUnit (.k input ownArgs key signature shape executed checked))
        · simpa using andorBudget (choice := false) firstFrame frame
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
        · simp only [witnessPayload_combine]
          omega
    | w => simp [branchBase] at branch

theorem orC_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedBudgetContract (.or_c first second) witness true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      have skipped : ExecutesBudgetFrame (if castToBool result then [] else compile second)
          [] [] flags txCtx 0 := by
        simpa [facts.truth] using ExecutesBudgetFrame.empty [] flags txCtx
      have conditional := notifThenBudget (compile_balancedControlFlow second)
        (facts.minimalIfSatisfied firstUnit) skipped
      apply generatedBudgetV_of_contract
        (GeneratedContract.orC_left (second := second) (secondMods := secondMods)
          (.b input facts executed) firstUnit)
      · simpa [compile, compileWithKeyHash] using frame.append conditional
      · exact funded

theorem orC_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedBudgetContract second secondWitness true flags
      txCtx ⟨.V, secondMods⟩) :
    GeneratedBudgetContract (.or_c first second)
      (Witness.combine firstWitness secondWitness) true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ := by
  cases firstContract with
  | @b _ result value firstBudget firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases secondContract with
    | @v _ secondBudget secondInput secondTrue secondExecuted secondFrame secondFunded =>
      have selected : ExecutesBudgetFrame (if castToBool result then [] else compile second)
          secondWitness.toInitialStack [] flags txCtx secondBudget := by
        simpa [firstFacts.truth] using secondFrame
      have conditional := notifThenBudget (compile_balancedControlFlow second)
        (firstFacts.minimalIfSatisfied firstUnit) selected
      apply generatedBudgetV_of_contract
        (GeneratedContract.orC_right (.b firstInput firstFacts firstExecuted) firstUnit
          (.v secondInput secondTrue secondExecuted))
      · simpa [compile, compileWithKeyHash, List.append_assoc] using
          (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append conditional
      · simp only [witnessPayload_combine]
        omega

theorem orD_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedBudgetContract (.or_d first second) witness true flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      have skipped : ExecutesBudgetFrame (if castToBool result then [] else compile second)
          [result] [result] flags txCtx 0 := by
        simpa [facts.truth] using ExecutesBudgetFrame.empty [result] flags txCtx
      have conditional := notifThenBudget (compile_balancedControlFlow second)
        (facts.minimalIfSatisfied firstUnit) skipped
      have tail := (ifdupTrueFrame (ctx := txCtx) facts.truth).append conditional
      apply generatedBudgetB_of_contract
        (GeneratedContract.orD_left (second := second) (secondMods := secondMods)
          (.b input facts executed) firstUnit)
      · simpa [compile, compileWithKeyHash] using frame.append tail
      · exact funded

theorem orD_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness false flags
      txCtx ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedBudgetContract second secondWitness expected
      flags txCtx ⟨.B, secondMods⟩) :
    GeneratedBudgetContract (.or_d first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ := by
  cases firstContract with
  | @b _ result value firstBudget firstInput firstFacts firstExecuted firstFrame firstFunded =>
    cases secondContract with
    | @b _ secondResult secondValue secondBudget secondInput secondFacts secondExecuted secondFrame secondFunded =>
      have selected : ExecutesBudgetFrame (if castToBool result then [] else compile second)
          secondWitness.toInitialStack [secondResult] flags txCtx secondBudget := by
        simpa [firstFacts.truth] using secondFrame
      have conditional := notifThenBudget (compile_balancedControlFlow second)
        (firstFacts.minimalIfSatisfied firstUnit) selected
      have tail := ((ifdupFalseFrame (ctx := txCtx) firstFacts.truth).withSuffix
        (suffix := secondWitness.toInitialStack)).append conditional
      apply generatedBudgetB_of_contract
        (GeneratedContract.orD_right (.b firstInput firstFacts firstExecuted) firstUnit
          (.b secondInput secondFacts secondExecuted))
      · simpa [compile, compileWithKeyHash, List.append_assoc] using
          (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append tail
      · simp only [witnessPayload_combine]
        omega

end GeneratedBudgetContract

end LeanMiniscript.Properties
