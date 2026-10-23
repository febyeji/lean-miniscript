import LeanMiniscript.Properties.SatisfactionBudgetMultiProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

inductive GeneratedBudgetChoiceFrames (flags : ScriptFlags)
    (txCtx : TxContext) : List CoreFragment → List MiniType → List Bool →
    List Witness → Prop where
  | nil : GeneratedBudgetChoiceFrames flags txCtx [] [] [] []
  | cons {fragment : CoreFragment} {ty : MiniType} {truth : Bool}
      {frame : Witness} {fragments : List CoreFragment} {types : List MiniType}
      {truths : List Bool} {frames : List Witness}
      (head : GeneratedBudgetContract fragment frame truth flags txCtx ty)
      (tail : GeneratedBudgetChoiceFrames flags txCtx fragments types truths
        frames) :
      GeneratedBudgetChoiceFrames flags txCtx (fragment :: fragments)
        (ty :: types) (truth :: truths) (frame :: frames)

namespace GeneratedBudgetChoiceFrames

/-- Append one selected budget contract while retaining source order. -/
theorem snoc
    {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    {fragment : CoreFragment} {ty : MiniType} {truth : Bool} {frame : Witness}
    (prior : GeneratedBudgetChoiceFrames flags txCtx fragments types truths
      frames)
    (child : GeneratedBudgetContract fragment frame truth flags txCtx ty) :
    GeneratedBudgetChoiceFrames flags txCtx (fragments ++ [fragment])
      (types ++ [ty]) (truths ++ [truth]) (frames ++ [frame]) := by
  induction prior with
  | nil => exact .cons child .nil
  | cons head tail ih => exact .cons head ih

/-- Erasing budget evidence recovers the established threshold child row. -/
theorem toGeneratedChoiceFrames
    {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedBudgetChoiceFrames flags txCtx fragments types
      truths frames) :
    GeneratedChoiceFrames flags txCtx fragments types truths frames := by
  induction generated with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.toGeneratedContract ih

end GeneratedBudgetChoiceFrames

/-- Source choice provenance selects budget contracts for every child. -/
theorem CandidatePair.ChoiceFrames.generatedBudgets
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames pairs truths frames)
    (supported : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      pairs fragments types) :
    GeneratedBudgetChoiceFrames flags txCtx fragments types truths frames := by
  induction choices generalizing fragments types with
  | nil =>
      obtain ⟨rfl, rfl⟩ := SupportsGeneratedBudgetsList.nil_inv supported
      exact .nil
  | snocSat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedBudgetsList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.sat _ selected)
  | snocDsat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedBudgetsList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.dsat _ selected)

private theorem thresholdAddFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesBudgetFrame [.op .OP_ADD] (order.outputs saved result)
      [scriptNum (savedValue + resultValue)] flags ctx
      0 :=
  .of_zero (WStackOrder.addStackFrame decoded)

private theorem thresholdPushFrame (value : Nat) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesBudgetFrame [.pushNum value] [] [scriptNat value] flags ctx
      0 := by
  simpa [scriptNat] using
    ExecutesBudgetFrame.pushNum (Int.ofNat value) flags ctx

private theorem thresholdEqualFrame
    (first second : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.op .OP_EQUAL] [first, second]
      [boolToElement (decide (first = second))] flags ctx
      0 :=
  .of_zero (equalStackFrame first second flags ctx)

private theorem thresholdComparisonFrame
    (threshold total : Nat) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.pushNum threshold, .op .OP_EQUAL]
      [scriptNat total]
      [boolToElement (decide (scriptNat threshold = scriptNat total))]
      flags ctx 0 := by
  have pushed := (thresholdPushFrame threshold flags ctx).withSuffix
    (suffix := [scriptNat total])
  exact pushed.append
    (thresholdEqualFrame (scriptNat threshold) (scriptNat total) flags ctx)

private theorem compileThreshTail_append_child
    (fragments : List CoreFragment) (fragment : CoreFragment) :
    compileThreshTail (fragments ++ [fragment]) =
      compileThreshTail fragments ++ compile fragment ++ [.op .OP_ADD] := by
  induction fragments with
  | nil => simp [compileThreshTail, compileThreshTailWithKeyHash, compile]
  | cons head tail ih =>
      change compileThreshTailWithKeyHash modelKeyHash (tail ++ [fragment]) =
        compileThreshTailWithKeyHash modelKeyHash tail ++
          compile fragment ++ [.op .OP_ADD] at ih
      simp only [List.cons_append, compileThreshTail,
        compileThreshTailWithKeyHash]
      rw [ih]
      simp [List.append_assoc]

private theorem compileThresh_append_child
    (priorFragments : List CoreFragment) (fragment : CoreFragment)
    (nonempty : priorFragments ≠ []) :
    compileThresh (priorFragments ++ [fragment]) =
      compileThresh priorFragments ++ compile fragment ++ [.op .OP_ADD] := by
  cases priorFragments with
  | nil => simp at nonempty
  | cons head tail =>
      have tailAppend := compileThreshTail_append_child tail fragment
      change compileThreshTailWithKeyHash modelKeyHash (tail ++ [fragment]) =
        compileThreshTailWithKeyHash modelKeyHash tail ++
          compile fragment ++ [.op .OP_ADD] at tailAppend
      simpa [compileThresh, compileThreshWithKeyHash,
        List.append_assoc] using congrArg
          (fun script => compile head ++ script) tailAppend

private theorem GeneratedBudgetChoiceFrames.extendThresholdBudget
    {flags : ScriptFlags} {txCtx : TxContext}
    {priorFragments fragments : List CoreFragment}
    {priorFrames frames : List Witness} {types : List MiniType}
    {truths : List Bool} {count total : Nat}
    (priorNonempty : priorFragments ≠ [])
    (priorFrame : ExecutesBudgetFrame (compileThresh priorFragments)
      (priorFrames.map Witness.toInitialStack).flatten [scriptNat count]
      flags txCtx (priorFrames.map witnessPayload).sum)
    (generated : GeneratedBudgetChoiceFrames flags txCtx fragments types truths frames)
    (restTyped : thresholdRestTypes types)
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    ExecutesBudgetFrame (compileThresh (priorFragments ++ fragments))
      ((priorFrames ++ frames).map Witness.toInitialStack).flatten [scriptNat total]
      flags txCtx ((priorFrames ++ frames).map witnessPayload).sum := by
  induction generated generalizing priorFragments priorFrames count total with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at totalEq
      subst total
      simpa using priorFrame
  | @cons fragment ty truth frame fragments types truths frames head tail ih =>
      cases ty with
      | mk base mods =>
          simp only [thresholdRestTypes] at restTyped
          obtain ⟨baseEq, childD, childUnit, restTyped⟩ := restTyped
          subst base
          cases head with
          | @w _ result value budget input order facts executed resources funded =>
              have resultEq := facts.eq_boolToElement_of_unit childUnit
              have childFrame : ExecutesBudgetFrame (compile fragment)
                  (scriptNat count :: frame.toInitialStack)
                  (order.outputs (scriptNat count) (boolToElement truth))
                  flags txCtx (witnessPayload frame) := by
                simpa [resultEq] using (resources (scriptNat count)).mono funded
              have decoded := order.binaryDecoded_scriptNat_boolToElement
                (threshold_accumulator_safe safe totalEq) truth flags
              have childAdded : ExecutesBudgetFrame (compile fragment ++ [.op .OP_ADD])
                  (scriptNat count :: frame.toInitialStack) [scriptNat (count + truth.toNat)]
                  flags txCtx (witnessPayload frame) := by
                simpa [scriptNat] using childFrame.append (thresholdAddFrame decoded)
              have combined := (priorFrame.withSuffix (suffix := frame.toInitialStack)).append childAdded
              have nextFrame : ExecutesBudgetFrame (compileThresh (priorFragments ++ [fragment]))
                  (((priorFrames ++ [frame]).map Witness.toInitialStack).flatten)
                  [scriptNat (count + truth.toNat)] flags txCtx
                  ((priorFrames ++ [frame]).map witnessPayload).sum := by
                rw [compileThresh_append_child priorFragments fragment priorNonempty]
                simpa [List.map_append, List.flatten_append, List.append_assoc] using combined
              simpa [List.append_assoc] using
                ih (priorFragments := priorFragments ++ [fragment])
                  (priorFrames := priorFrames ++ [frame]) (count := count + truth.toNat)
                  (total := total) (by simp) nextFrame restTyped safe
                  (threshold_accumulator_step totalEq)

private theorem GeneratedBudgetChoiceFrames.thresholdChildrenBudget
    {flags : ScriptFlags} {txCtx : TxContext} {total : Nat}
    {first : CoreFragment} {fragments : List CoreFragment}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedBudgetChoiceFrames flags txCtx
      (first :: fragments) (⟨.B, firstMods⟩ :: restTypes) truths frames)
    (firstUnit : firstMods.u = true) (restTyped : thresholdRestTypes restTypes)
    (safe : ArithmeticScriptNatSafe total) (sumEq : (truths.map Bool.toNat).sum = total) :
    ExecutesBudgetFrame (compileThresh (first :: fragments))
      (frames.map Witness.toInitialStack).flatten [scriptNat total]
      flags txCtx (frames.map witnessPayload).sum := by
  cases generated with
  | @cons _ _ firstTruth firstFrame _ _ tailTruths tailFrames firstContract tail =>
      cases firstContract with
      | b input facts executed resources funded =>
          have resultEq := facts.eq_boolToElement_of_unit firstUnit
          have firstResources : ExecutesBudgetFrame (compile first) firstFrame.toInitialStack
              [scriptNat firstTruth.toNat] flags txCtx (witnessPayload firstFrame) := by
            cases firstTruth <;>
              simpa [resultEq, boolToElement, scriptNat, scriptNum_zero, scriptNum_one]
                using resources.mono funded
          have firstBounded : ExecutesBudgetFrame (compileThresh [first])
              (([firstFrame].map Witness.toInitialStack).flatten) [scriptNat firstTruth.toNat]
              flags txCtx ([firstFrame].map witnessPayload).sum := by
            simpa [compile, compileThresh, compileThreshWithKeyHash,
              compileThreshTail, compileThreshTailWithKeyHash] using firstResources
          have totalEq : firstTruth.toNat + (tailTruths.map Bool.toNat).sum = total := by
            simpa using sumEq
          simpa using tail.extendThresholdBudget (priorFragments := [first])
            (priorFrames := [firstFrame]) (count := firstTruth.toNat) (total := total)
            (by simp) firstBounded restTyped safe totalEq

namespace CandidatePair.SupportsGeneratedBudgets

theorem thresh
    {firstPair : CandidatePair} {restPairs : List CandidatePair}
    {scriptCtx : ScriptContext} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      restPairs fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    CandidatePair.SupportsGeneratedBudgets
      ({ sat := CandidatePair.selectExactly threshold (firstPair :: restPairs)
         dsat := CandidatePair.thresholdDissatisfaction threshold
           (CandidatePair.countCandidates (firstPair :: restPairs)) } :
        CandidatePair)
      scriptCtx (.thresh threshold (first :: fragments))
      ⟨.B, {
        z := CorrectnessModifiers.allZ
          (firstMods :: MiniType.modifiers restTypes)
        o := CorrectnessModifiers.oneOWithRestZ
          (firstMods :: MiniType.modifiers restTypes)
        d := true
        u := true }⟩ flags txCtx := by
  have allSupported := restSupported.cons firstSupported
  have valid : candidateThresholdValid threshold (first :: fragments).length :=
    ⟨by omega, atMost, safe⟩
  refine ⟨.thresh firstSupported.typed firstD firstUnit restSupported.typed
    restTyped positive atMost, ?_, ?_⟩
  · change (CandidatePair.selectExactly threshold
      (firstPair :: restPairs)).Supports _
    intro witness selected
    obtain ⟨frames, trace⟩ := CandidatePair.selectExactly_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    have generated :=
      LeanMiniscript.Properties.CandidatePair.ChoiceFrames.generatedBudgets
        choices allSupported
    have semantic := generated.toGeneratedChoiceFrames
    have childrenResources := generated.thresholdChildrenBudget firstUnit restTyped safe sumEq
    have comparison := thresholdComparisonFrame threshold threshold flags txCtx
    have combined := childrenResources.append comparison
    have normalized : ExecutesBudgetFrame
        (compile (.thresh threshold (first :: fragments)))
        witness.toInitialStack [trueElement] flags txCtx
        (frames.map witnessPayload).sum := by
      rw [trace.toInitialStack]
      simpa [compile, compileWithKeyHash, compileThresh,
        trueElement, boolToElement,
        List.append_assoc] using combined
    apply GeneratedBudgetContract.b
    · simpa [MiniType.modifiers] using
        (semantic.thresholdInput (expected := true) trace)
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack]
      exact semantic.thresholdExecution firstUnit restTyped safe sumEq (by simp)
    · exact normalized
    · have payloadEq := congrArg witnessPayload trace.toInitialStack
      simpa using Nat.le_of_eq payloadEq.symm
  · change (CandidatePair.thresholdDissatisfaction threshold
      (CandidatePair.countCandidates (firstPair :: restPairs))).Supports _
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.thresholdDissatisfaction_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    have generated :=
      LeanMiniscript.Properties.CandidatePair.ChoiceFrames.generatedBudgets
        choices allSupported
    have semantic := generated.toGeneratedChoiceFrames
    have zeroSafe : ArithmeticScriptNatSafe 0 :=
      ArithmeticScriptNatSafe.of_lt (by change 0 < 2147483648; omega)
    have childrenResources := generated.thresholdChildrenBudget firstUnit restTyped zeroSafe sumEq
    have comparison := thresholdComparisonFrame threshold 0 flags txCtx
    have combined := childrenResources.append comparison
    have thresholdNeZero : scriptNat threshold ≠ scriptNat 0 := by
      intro encodedEq
      have thresholdDecoded := valid.2.2.decode false
      have zeroDecoded := decodeScriptNum_scriptNat_of_lt
        (n := 0) (by change 0 < 2147483648; omega) false
      rw [encodedEq, zeroDecoded] at thresholdDecoded
      simp only [Except.ok.injEq] at thresholdDecoded
      apply valid.1
      exact Int.ofNat.inj thresholdDecoded.symm
    have unequal : decide (scriptNat threshold = scriptNat 0) = false := by
      simp [thresholdNeZero]
    have normalized : ExecutesBudgetFrame
        (compile (.thresh threshold (first :: fragments)))
        witness.toInitialStack [falseElement] flags txCtx
        (frames.map witnessPayload).sum := by
      rw [trace.toInitialStack]
      simpa [compile, compileWithKeyHash, compileThresh,
        unequal, falseElement,
        boolToElement, List.append_assoc] using combined
    apply GeneratedBudgetContract.b
    · simpa [MiniType.modifiers] using
        (semantic.thresholdInput (expected := false) trace)
    · exact BooleanResultFacts.canonical false _ flags
    · rw [trace.toInitialStack]
      exact semantic.thresholdExecution firstUnit restTyped zeroSafe sumEq unequal
    · exact normalized
    · have payloadEq := congrArg witnessPayload trace.toInitialStack
      simpa using Nat.le_of_eq payloadEq.symm

end CandidatePair.SupportsGeneratedBudgets

theorem generatedBudgets_thresh
    {scriptCtx : ScriptContext} {env : SatEnv} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets
      (satisfactionCandidates first env) scriptCtx first ⟨.B, firstMods⟩
      flags env.txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedBudgetsList scriptCtx flags env.txCtx
      (satisfactionCandidatesList fragments env) fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    CandidatePair.SupportsGeneratedBudgets
      (satisfactionCandidates (.thresh threshold (first :: fragments)) env)
      scriptCtx (.thresh threshold (first :: fragments))
      ⟨.B, {
        z := CorrectnessModifiers.allZ
          (firstMods :: MiniType.modifiers restTypes)
        o := CorrectnessModifiers.oneOWithRestZ
          (firstMods :: MiniType.modifiers restTypes)
        d := true
        u := true }⟩ flags env.txCtx := by
  have valid : candidateThresholdValid threshold (first :: fragments).length :=
    ⟨by omega, atMost, safe⟩
  rw [satisfactionCandidates_thresh_valid threshold (first :: fragments) env
    valid]
  simpa [satisfactionCandidatesList_eq_map] using
    (CandidatePair.SupportsGeneratedBudgets.thresh firstSupported firstD
      firstUnit restSupported restTyped positive atMost safe)

/-- Invalid threshold candidates are empty while retaining their explicit type. -/
theorem generatedBudgets_thresh_invalid
    {scriptCtx : ScriptContext} {env : SatEnv} {threshold : Nat}
    {fragments : List CoreFragment} {ty : MiniType} {flags : ScriptFlags}
    (typed : HasType scriptCtx (.thresh threshold fragments) ty)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    CandidatePair.SupportsGeneratedBudgets
      (satisfactionCandidates (.thresh threshold fragments) env)
      scriptCtx (.thresh threshold fragments) ty flags env.txCtx := by
  rw [satisfactionCandidates_thresh_invalid threshold fragments env invalid]
  exact ⟨typed, CandidateResult.supports_impossible _,
    CandidateResult.supports_impossible _⟩

end LeanMiniscript.Properties
