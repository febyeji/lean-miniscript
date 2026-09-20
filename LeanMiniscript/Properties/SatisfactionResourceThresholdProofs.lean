import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Resource-aware threshold witnesses

The generated child relation keeps every selected resource contract in source
order.  Threshold assembly then advances one resource frame and one
`ThresholdResourcePath` together, so both public summaries describe the same
choice row.
-/

/-- Resource contracts selected by one source-order threshold choice row. -/
inductive GeneratedResourceChoiceFrames (flags : ScriptFlags)
    (txCtx : TxContext) : List CoreFragment → List MiniType → List Bool →
    List Witness → Prop where
  | nil : GeneratedResourceChoiceFrames flags txCtx [] [] [] []
  | cons {fragment : CoreFragment} {ty : MiniType} {truth : Bool}
      {frame : Witness} {fragments : List CoreFragment} {types : List MiniType}
      {truths : List Bool} {frames : List Witness}
      (head : GeneratedResourceContract fragment frame truth flags txCtx ty)
      (tail : GeneratedResourceChoiceFrames flags txCtx fragments types truths
        frames) :
      GeneratedResourceChoiceFrames flags txCtx (fragment :: fragments)
        (ty :: types) (truth :: truths) (frame :: frames)

namespace GeneratedResourceChoiceFrames

/-- Append one selected resource contract while retaining source order. -/
theorem snoc
    {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    {fragment : CoreFragment} {ty : MiniType} {truth : Bool} {frame : Witness}
    (prior : GeneratedResourceChoiceFrames flags txCtx fragments types truths
      frames)
    (child : GeneratedResourceContract fragment frame truth flags txCtx ty) :
    GeneratedResourceChoiceFrames flags txCtx (fragments ++ [fragment])
      (types ++ [ty]) (truths ++ [truth]) (frames ++ [frame]) := by
  induction prior with
  | nil => exact .cons child .nil
  | cons head tail ih => exact .cons head ih

/-- Erasing resource evidence recovers the established threshold child row. -/
theorem toGeneratedChoiceFrames
    {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedResourceChoiceFrames flags txCtx fragments types
      truths frames) :
    GeneratedChoiceFrames flags txCtx fragments types truths frames := by
  induction generated with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.toGeneratedContract ih

end GeneratedResourceChoiceFrames

/-- Source choice provenance selects resource contracts for every child. -/
theorem CandidatePair.ChoiceFrames.generatedResources
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames pairs truths frames)
    (supported : SupportsGeneratedResourcesList scriptCtx flags txCtx
      pairs fragments types) :
    GeneratedResourceChoiceFrames flags txCtx fragments types truths frames := by
  induction choices generalizing fragments types with
  | nil =>
      obtain ⟨rfl, rfl⟩ := SupportsGeneratedResourcesList.nil_inv supported
      exact .nil
  | snocSat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedResourcesList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.sat _ selected)
  | snocDsat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedResourcesList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.dsat _ selected)

private theorem thresholdAddFrame
    {saved result : StackElement} {savedValue resultValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : order.BinaryDecoded flags saved result savedValue resultValue) :
    ExecutesResourceFrame [.op .OP_ADD] (order.outputs saved result)
      [scriptNum (savedValue + resultValue)] flags ctx
      StackTraceBound.binary 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases order with
    | savedFirst =>
        exact Eval.add saved result savedValue resultValue rest [] altStack
          flags ctx _ decoded Eval.done
    | resultFirst =>
        simpa [WStackOrder.outputs, Int.add_comm] using
          (Eval.add result saved resultValue savedValue rest [] altStack
            flags ctx _ decoded Eval.done)
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · cases order <;> simp [WStackOrder.outputs, StackTraceBound.binary]
  · simp [StackTraceBound.binary]
  · intro rest
    simp [executedMultiSigKeyCharge]

private theorem thresholdPushFrame (value : Nat) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesResourceFrame [.pushNum value] [] [scriptNat value] flags ctx
      StackTraceBound.push 0 := by
  simpa [scriptNat] using
    ExecutesResourceFrame.pushNum (Int.ofNat value) flags ctx

private theorem thresholdEqualFrame
    (first second : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_EQUAL] [first, second]
      [boolToElement (decide (first = second))] flags ctx
      StackTraceBound.equal 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    by_cases equal : first = second
    · simpa [equal, boolToElement] using
        (Eval.equal_true first second rest [] altStack flags ctx _ equal Eval.done)
    · simpa [equal, boolToElement] using
        (Eval.equal_false first second rest [] altStack flags ctx _ equal Eval.done)
  · simp [StackTraceBound.equal]
  · simp [StackTraceBound.equal]
  · simp [StackTraceBound.equal]
  · intro rest
    simp [executedMultiSigKeyCharge]

private theorem thresholdComparisonFrame
    (threshold total : Nat) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.pushNum threshold, .op .OP_EQUAL]
      [scriptNat total]
      [boolToElement (decide (scriptNat threshold = scriptNat total))]
      flags ctx (StackTraceBound.push.sequential StackTraceBound.equal) 0 := by
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

private theorem stackPathBoundsList_append
    (left right : List CoreFragment) :
    stackPathBoundsList (left ++ right) =
      stackPathBoundsList left ++ stackPathBoundsList right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [stackPathBoundsList, ih]

private theorem opPathBoundsList_append
    (left right : List CoreFragment) :
    opPathBoundsList (left ++ right) =
      opPathBoundsList left ++ opPathBoundsList right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [opPathBoundsList, ih]



/-- Extend a nonempty threshold prefix by a generated Wdu tail while advancing
    the concrete frame and the jointly selected public-resource path together. -/
private theorem GeneratedResourceChoiceFrames.extendThresholdResources
    {flags : ScriptFlags} {txCtx : TxContext}
    {priorFragments fragments : List CoreFragment}
    {priorFrames frames : List Witness} {types : List MiniType}
    {truths : List Bool} {count total : Nat}
    {priorTrace : StackTraceBound} {priorDynamic : Nat}
    (priorNonempty : priorFragments ≠ [])
    (priorPath : ThresholdResourcePath
      (stackPathBoundsList priorFragments) (opPathBoundsList priorFragments)
      count priorTrace priorDynamic)
    (priorResources : ExecutesResourceFrame (compileThresh priorFragments)
      (priorFrames.map Witness.toInitialStack).flatten [scriptNat count]
      flags txCtx priorTrace priorDynamic)
    (generated : GeneratedResourceChoiceFrames flags txCtx fragments types
      truths frames)
    (restTyped : thresholdRestTypes types)
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    ∃ finalTrace finalDynamic,
      ThresholdResourcePath
        (stackPathBoundsList (priorFragments ++ fragments))
        (opPathBoundsList (priorFragments ++ fragments)) total
        finalTrace finalDynamic ∧
      ExecutesResourceFrame (compileThresh (priorFragments ++ fragments))
        ((priorFrames ++ frames).map Witness.toInitialStack).flatten
        [scriptNat total] flags txCtx finalTrace finalDynamic := by
  induction generated generalizing priorFragments priorFrames count
      priorTrace priorDynamic total with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Nat.add_zero] at totalEq
      subst total
      exact ⟨priorTrace, priorDynamic, by simpa using priorPath,
        by simpa using priorResources⟩
  | @cons fragment ty truth frame fragments types truths frames head tail ih =>
      cases ty with
      | mk base mods =>
          simp only [thresholdRestTypes] at restTyped
          obtain ⟨baseEq, childD, childUnit, restTyped⟩ := restTyped
          subst base
          cases head with
          | @w _ result value childTrace childDynamic input order facts executed
              resources stackSelected opSelected =>
            have boundsNonempty : stackPathBoundsList priorFragments ≠ [] := by
              intro empty
              cases priorFragments with
              | nil => exact priorNonempty rfl
              | cons priorHead priorTail =>
                  simp [stackPathBoundsList] at empty
            have boundsNotEmpty :
                (stackPathBoundsList priorFragments).isEmpty = false := by
              simpa [List.isEmpty_iff] using boundsNonempty
            have extendedPath : ThresholdResourcePath
                (stackPathBoundsList (priorFragments ++ [fragment]))
                (opPathBoundsList (priorFragments ++ [fragment]))
                (count + truth.toNat)
                (priorTrace.sequential
                  (childTrace.thresholdChild
                    (stackPathBoundsList priorFragments).isEmpty))
                (priorDynamic + childDynamic) := by
              cases truth with
              | false =>
                  have stackDsat : (stackPathBounds fragment).dsat =
                      some childTrace := by
                    simpa [selectedStackSummary] using stackSelected
                  have opDsat : (opPathBounds fragment).dsat =
                      some childDynamic := by
                    simpa [selectedOpSummary] using opSelected
                  simpa [stackPathBoundsList_append, opPathBoundsList_append,
                    stackPathBoundsList, opPathBoundsList] using
                    (ThresholdResourcePath.dsat priorPath stackDsat opDsat)
              | true =>
                  have stackSat : (stackPathBounds fragment).sat =
                      some childTrace := by
                    simpa [selectedStackSummary] using stackSelected
                  have opSat : (opPathBounds fragment).sat =
                      some childDynamic := by
                    simpa [selectedOpSummary] using opSelected
                  simpa [stackPathBoundsList_append, opPathBoundsList_append,
                    stackPathBoundsList, opPathBoundsList] using
                    (ThresholdResourcePath.sat priorPath stackSat opSat)
            have resultEq := facts.eq_boolToElement_of_unit childUnit
            have childFrame : ExecutesResourceFrame (compile fragment)
                (scriptNat count :: frame.toInitialStack)
                (order.outputs (scriptNat count) (boolToElement truth))
                flags txCtx childTrace childDynamic := by
              simpa [resultEq] using resources (scriptNat count)
            have decoded := order.binaryDecoded_scriptNat_boolToElement
              (threshold_accumulator_safe safe totalEq) truth flags
            have childAdded : ExecutesResourceFrame
                (compile fragment ++ [.op .OP_ADD])
                (scriptNat count :: frame.toInitialStack)
                [scriptNat (count + truth.toNat)] flags txCtx
                (childTrace.sequential StackTraceBound.binary)
                childDynamic := by
              simpa [scriptNat] using
                childFrame.append (thresholdAddFrame decoded)
            have priorWithSuffix := priorResources.withSuffix
              (suffix := frame.toInitialStack)
            have combined := priorWithSuffix.append childAdded
            have nextResources : ExecutesResourceFrame
                (compileThresh (priorFragments ++ [fragment]))
                (((priorFrames ++ [frame]).map Witness.toInitialStack).flatten)
                [scriptNat (count + truth.toNat)] flags txCtx
                (priorTrace.sequential
                  (childTrace.thresholdChild
                    (stackPathBoundsList priorFragments).isEmpty))
                (priorDynamic + childDynamic) := by
              rw [compileThresh_append_child priorFragments fragment
                priorNonempty]
              simpa [boundsNotEmpty, StackTraceBound.thresholdChild,
                List.map_append, List.flatten_append, List.append_assoc] using
                combined
            have stepped := threshold_accumulator_step totalEq
            simpa [List.append_assoc] using
              ih (priorFragments := priorFragments ++ [fragment])
              (priorFrames := priorFrames ++ [frame])
              (count := count + truth.toNat)
              (priorTrace := priorTrace.sequential
                (childTrace.thresholdChild
                  (stackPathBoundsList priorFragments).isEmpty))
              (priorDynamic := priorDynamic + childDynamic)
              (total := total) (by simp) extendedPath nextResources
              restTyped safe stepped



/-- A nonempty generated threshold row has one concrete joint resource path and
    one exact frame ending in its canonical accumulated count. -/
private theorem GeneratedResourceChoiceFrames.thresholdChildrenResources
    {flags : ScriptFlags} {txCtx : TxContext} {total : Nat}
    {first : CoreFragment} {fragments : List CoreFragment}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedResourceChoiceFrames flags txCtx
      (first :: fragments) (⟨.B, firstMods⟩ :: restTypes) truths frames)
    (firstUnit : firstMods.u = true)
    (restTyped : thresholdRestTypes restTypes)
    (safe : ArithmeticScriptNatSafe total)
    (sumEq : (truths.map Bool.toNat).sum = total) :
    ∃ trace dynamic,
      ThresholdResourcePath
        (stackPathBoundsList (first :: fragments))
        (opPathBoundsList (first :: fragments)) total trace dynamic ∧
      ExecutesResourceFrame (compileThresh (first :: fragments))
        (frames.map Witness.toInitialStack).flatten [scriptNat total]
        flags txCtx trace dynamic := by
  cases generated with
  | @cons _ _ firstTruth firstFrame _ _ tailTruths tailFrames
      firstContract tail =>
      cases firstContract with
      | @b _ result value firstTrace firstDynamic input facts executed resources
          stackSelected opSelected =>
          have resultEq := facts.eq_boolToElement_of_unit firstUnit
          have firstResources : ExecutesResourceFrame (compile first)
              firstFrame.toInitialStack [scriptNat firstTruth.toNat]
              flags txCtx firstTrace firstDynamic := by
            cases firstTruth <;>
              simpa [resultEq, boolToElement, scriptNat, scriptNum_zero,
                scriptNum_one] using resources
          have firstPath : ThresholdResourcePath
              (stackPathBoundsList [first]) (opPathBoundsList [first])
              firstTruth.toNat
              (StackTraceBound.empty.sequential
                (firstTrace.thresholdChild true)) firstDynamic := by
            cases firstTruth with
            | false =>
                have stackDsat : (stackPathBounds first).dsat =
                    some firstTrace := by
                  simpa [selectedStackSummary] using stackSelected
                have opDsat : (opPathBounds first).dsat =
                    some firstDynamic := by
                  simpa [selectedOpSummary] using opSelected
                simpa [stackPathBoundsList, opPathBoundsList] using
                  (ThresholdResourcePath.dsat ThresholdResourcePath.nil
                    stackDsat opDsat)
            | true =>
                have stackSat : (stackPathBounds first).sat =
                    some firstTrace := by
                  simpa [selectedStackSummary] using stackSelected
                have opSat : (opPathBounds first).sat =
                    some firstDynamic := by
                  simpa [selectedOpSummary] using opSelected
                simpa [stackPathBoundsList, opPathBoundsList] using
                  (ThresholdResourcePath.sat ThresholdResourcePath.nil
                    stackSat opSat)
          have firstBounded : ExecutesResourceFrame (compileThresh [first])
              (([firstFrame].map Witness.toInitialStack).flatten)
              [scriptNat firstTruth.toNat]
              flags txCtx
              (StackTraceBound.empty.sequential
                (firstTrace.thresholdChild true)) firstDynamic := by
            have lifted := firstResources.mono
              (upper := StackTraceBound.empty.sequential
                (firstTrace.thresholdChild true))
              (upperDynamic := firstDynamic)
              (by simp [StackTraceBound.thresholdChild,
                StackTraceBound.sequential, StackTraceBound.empty])
              (Int.le_max_left _ _) (Nat.le_refl _)
            simpa [compile, compileThresh, compileThreshWithKeyHash,
              compileThreshTail, compileThreshTailWithKeyHash] using lifted
          have totalEq : firstTruth.toNat +
              (tailTruths.map Bool.toNat).sum = total := by
            simpa using sumEq
          simpa using tail.extendThresholdResources
            (priorFragments := [first]) (priorFrames := [firstFrame])
            (count := firstTruth.toNat)
            (priorTrace := StackTraceBound.empty.sequential
              (firstTrace.thresholdChild true))
            (priorDynamic := firstDynamic) (total := total)
            (by simp) firstPath firstBounded restTyped safe totalEq



namespace CandidatePair.SupportsGeneratedResources

/-- Resource-aware generated support for one valid exact-count threshold row. -/
theorem thresh
    {firstPair : CandidatePair} {restPairs : List CandidatePair}
    {scriptCtx : ScriptContext} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedResourcesList scriptCtx flags txCtx
      restPairs fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    CandidatePair.SupportsGeneratedResources
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
      LeanMiniscript.Properties.CandidatePair.ChoiceFrames.generatedResources
        choices allSupported
    have semantic := generated.toGeneratedChoiceFrames
    obtain ⟨pathTrace, dynamic, path, childrenResources⟩ :=
      generated.thresholdChildrenResources firstUnit restTyped safe sumEq
    have comparison := thresholdComparisonFrame threshold threshold flags txCtx
    have combined := childrenResources.append comparison
    have normalized : ExecutesResourceFrame
        (compile (.thresh threshold (first :: fragments)))
        witness.toInitialStack [trueElement] flags txCtx
        pathTrace.thresholdComparison dynamic := by
      rw [trace.toInitialStack]
      simpa [compile, compileWithKeyHash, compileThresh,
        StackTraceBound.thresholdComparison, trueElement, boolToElement,
        List.append_assoc] using combined
    obtain ⟨stackLimit, opLimit, stackEq, opEq, netLe, execLe, dynamicLe⟩ :=
      path.bounds_thresh
    have bounded := normalized.mono netLe execLe dynamicLe
    apply GeneratedResourceContract.b
    · simpa [MiniType.modifiers] using
        (semantic.thresholdInput (expected := true) trace)
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack]
      exact semantic.thresholdExecution firstUnit restTyped safe sumEq (by simp)
    · exact bounded
    · simpa [selectedStackSummary] using stackEq
    · simpa [selectedOpSummary] using opEq
  · change (CandidatePair.thresholdDissatisfaction threshold
      (CandidatePair.countCandidates (firstPair :: restPairs))).Supports _
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.thresholdDissatisfaction_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    have generated :=
      LeanMiniscript.Properties.CandidatePair.ChoiceFrames.generatedResources
        choices allSupported
    have semantic := generated.toGeneratedChoiceFrames
    have zeroSafe : ArithmeticScriptNatSafe 0 :=
      ArithmeticScriptNatSafe.of_lt (by change 0 < 2147483648; omega)
    obtain ⟨pathTrace, dynamic, path, childrenResources⟩ :=
      generated.thresholdChildrenResources firstUnit restTyped zeroSafe sumEq
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
    have normalized : ExecutesResourceFrame
        (compile (.thresh threshold (first :: fragments)))
        witness.toInitialStack [falseElement] flags txCtx
        pathTrace.thresholdComparison dynamic := by
      rw [trace.toInitialStack]
      simpa [compile, compileWithKeyHash, compileThresh,
        StackTraceBound.thresholdComparison, unequal, falseElement,
        boolToElement, List.append_assoc] using combined
    obtain ⟨stackLimit, opLimit, stackEq, opEq, netLe, execLe, dynamicLe⟩ :=
      path.bounds_thresh_dsat (threshold := threshold)
    have bounded := normalized.mono netLe execLe dynamicLe
    apply GeneratedResourceContract.b
    · simpa [MiniType.modifiers] using
        (semantic.thresholdInput (expected := false) trace)
    · exact BooleanResultFacts.canonical false _ flags
    · rw [trace.toInitialStack]
      exact semantic.thresholdExecution firstUnit restTyped zeroSafe sumEq unequal
    · exact bounded
    · simpa [selectedStackSummary] using stackEq
    · simpa [selectedOpSummary] using opEq

end CandidatePair.SupportsGeneratedResources



/-- Recursive-facing resource theorem for a valid executable threshold row. -/
theorem generatedResources_thresh
    {scriptCtx : ScriptContext} {env : SatEnv} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags}
    (firstSupported : CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates first env) scriptCtx first ⟨.B, firstMods⟩
      flags env.txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedResourcesList scriptCtx flags env.txCtx
      (satisfactionCandidatesList fragments env) fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    CandidatePair.SupportsGeneratedResources
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
    (CandidatePair.SupportsGeneratedResources.thresh firstSupported firstD
      firstUnit restSupported restTyped positive atMost safe)

/-- Invalid threshold candidates are empty while retaining their explicit type. -/
theorem generatedResources_thresh_invalid
    {scriptCtx : ScriptContext} {env : SatEnv} {threshold : Nat}
    {fragments : List CoreFragment} {ty : MiniType} {flags : ScriptFlags}
    (typed : HasType scriptCtx (.thresh threshold fragments) ty)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates (.thresh threshold fragments) env)
      scriptCtx (.thresh threshold fragments) ty flags env.txCtx := by
  rw [satisfactionCandidates_thresh_invalid threshold fragments env invalid]
  exact ⟨typed, CandidateResult.supports_impossible _,
    CandidateResult.supports_impossible _⟩

end LeanMiniscript.Properties
