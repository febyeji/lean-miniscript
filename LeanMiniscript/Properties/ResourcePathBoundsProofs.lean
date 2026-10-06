import LeanMiniscript.Properties.ResourcePaths

/-! Threshold-path bounds and agreement with the resource summary tables. -/

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script ResourceAnalysis

/-- Forget dynamic opcode charges and the execution-peak coordinate while
    retaining the legacy net-difference path used by witness-length proofs. -/
theorem ThresholdResourcePath.toThresholdStackPath
    {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
    {count dynamic : Nat} {trace : StackTraceBound}
    (path : ThresholdResourcePath stackBounds opBounds count trace dynamic) :
    ThresholdStackPath stackBounds count trace.netDiff := by
  induction path with
  | nil => exact .nil
  | @sat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      have extended := ThresholdStackPath.sat ih stackSelected
      cases stackBounds with
      | nil => simpa [StackTraceBound.thresholdChild,
          StackTraceBound.sequential] using extended
      | cons head tail =>
          simpa [StackTraceBound.thresholdChild, StackTraceBound.sequential,
            StackTraceBound.binary, Int.add_assoc] using extended
  | @dsat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      have extended := ThresholdStackPath.dsat ih stackSelected
      cases stackBounds with
      | nil => simpa [StackTraceBound.thresholdChild,
          StackTraceBound.sequential] using extended
      | cons head tail =>
          simpa [StackTraceBound.thresholdChild, StackTraceBound.sequential,
            StackTraceBound.binary, Int.add_assoc] using extended

private theorem ThresholdStackPath.nil_inv {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath [] count netDiff) : count = 0 ∧ netDiff = 0 := by
  generalize boundsEq : ([] : List StackPathBounds) = bounds at path
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | sat prior selected => simp at boundsEq
  | dsat prior selected => simp at boundsEq

private theorem stackThresholdFold_append (first : Bool)
    (states : List StackTraceSet) (bounds : List StackPathBounds)
    (child : StackPathBounds) :
    stackThresholdFold first states (bounds ++ [child]) =
      stackThresholdStep (stackThresholdFold first states bounds)
        (appendThresholdAdd (first && bounds.isEmpty) child) := by
  induction bounds generalizing first states with
  | nil => simp [stackThresholdFold]
  | cons bound bounds ih =>
      simp only [List.cons_append, stackThresholdFold, List.isEmpty_cons,
        Bool.and_false, appendThresholdAdd]
      exact ih false (stackThresholdStep states
        (if first then bound else
          { sat := StackTraceSet.sequential bound.sat
              (some StackTraceBound.binary)
            dsat := StackTraceSet.sequential bound.dsat
              (some StackTraceBound.binary) }))

private theorem stackThresholdStep_getD_zero
    (states : List StackTraceSet) (child : StackPathBounds) :
    (stackThresholdStep states child).getD 0 none =
      StackTraceSet.sequential (states.getD 0 none) child.dsat := by
  cases states <;> simp [stackThresholdStep, StackTraceSet.sequential]

private theorem stackThresholdMiddle_getD
    (child : StackPathBounds) (previous : StackTraceSet)
    (rest : List StackTraceSet) (count : Nat) :
    (stackThresholdMiddle child previous rest).getD count none =
      match count with
      | 0 =>
          StackTraceSet.choice
            (StackTraceSet.sequential (rest.getD 0 none) child.dsat)
            (StackTraceSet.sequential previous child.sat)
      | count + 1 =>
          StackTraceSet.choice
            (StackTraceSet.sequential (rest.getD (count + 1) none) child.dsat)
            (StackTraceSet.sequential (rest.getD count none) child.sat) := by
  induction rest generalizing previous count with
  | nil =>
      cases count <;> simp [stackThresholdMiddle, StackTraceSet.sequential,
        StackTraceSet.choice]
  | cons current rest ih =>
      cases count with
      | zero => simp [stackThresholdMiddle]
      | succ count =>
          simp only [stackThresholdMiddle, List.getD_cons_succ]
          cases count with
          | zero => simpa using ih current 0
          | succ count =>
              simpa [Nat.succ_eq_add_one] using ih current (count + 1)

private theorem stackThresholdStep_getD_succ
    (states : List StackTraceSet) (child : StackPathBounds) (count : Nat) :
    (stackThresholdStep states child).getD (count + 1) none =
      StackTraceSet.choice
        (StackTraceSet.sequential (states.getD (count + 1) none) child.dsat)
        (StackTraceSet.sequential (states.getD count none) child.sat) := by
  cases states with
  | nil => simp [stackThresholdStep, StackTraceSet.sequential,
      StackTraceSet.choice]
  | cons first rest =>
      simp only [stackThresholdStep, List.getD_cons_succ]
      rw [stackThresholdMiddle_getD]
      cases count <;> simp

private theorem opThresholdFold_append
    (states : List PathMaximum) (bounds : List OpPathBounds)
    (child : OpPathBounds) :
    opThresholdFold states (bounds ++ [child]) =
      opThresholdStep (opThresholdFold states bounds) child := by
  induction bounds generalizing states with
  | nil => simp [opThresholdFold]
  | cons bound bounds ih =>
      simp only [List.cons_append, opThresholdFold]
      exact ih (opThresholdStep states bound)

private theorem opThresholdStep_getD_zero
    (states : List PathMaximum) (child : OpPathBounds) :
    (opThresholdStep states child).getD 0 none =
      PathMaximum.sequential (states.getD 0 none) child.dsat := by
  cases states <;> simp [opThresholdStep, PathMaximum.sequential]

private theorem opThresholdMiddle_getD
    (child : OpPathBounds) (previous : PathMaximum)
    (rest : List PathMaximum) (count : Nat) :
    (opThresholdMiddle child previous rest).getD count none =
      match count with
      | 0 =>
          PathMaximum.choice
            (PathMaximum.sequential (rest.getD 0 none) child.dsat)
            (PathMaximum.sequential previous child.sat)
      | count + 1 =>
          PathMaximum.choice
            (PathMaximum.sequential (rest.getD (count + 1) none) child.dsat)
            (PathMaximum.sequential (rest.getD count none) child.sat) := by
  induction rest generalizing previous count with
  | nil =>
      cases count <;> simp [opThresholdMiddle, PathMaximum.sequential,
        PathMaximum.choice]
  | cons current rest ih =>
      cases count with
      | zero => simp [opThresholdMiddle]
      | succ count =>
          simp only [opThresholdMiddle, List.getD_cons_succ]
          cases count with
          | zero => simpa using ih current 0
          | succ count =>
              simpa [Nat.succ_eq_add_one] using ih current (count + 1)

private theorem opThresholdStep_getD_succ
    (states : List PathMaximum) (child : OpPathBounds) (count : Nat) :
    (opThresholdStep states child).getD (count + 1) none =
      PathMaximum.choice
        (PathMaximum.sequential (states.getD (count + 1) none) child.dsat)
        (PathMaximum.sequential (states.getD count none) child.sat) := by
  cases states with
  | nil => simp [opThresholdStep, PathMaximum.sequential, PathMaximum.choice]
  | cons first rest =>
      simp only [opThresholdStep, List.getD_cons_succ]
      rw [opThresholdMiddle_getD]
      cases count <;> simp

private def stackTraceBound
    (summary : StackTraceSet) (trace : StackTraceBound) : Prop :=
  ∃ limit, summary = some limit ∧
    trace.netDiff ≤ limit.netDiff ∧ trace.exec ≤ limit.exec

private theorem stackTraceBound_sequential
    {left right : StackTraceSet} {leftTrace rightTrace : StackTraceBound}
    (leftBound : stackTraceBound left leftTrace)
    (rightBound : stackTraceBound right rightTrace) :
    stackTraceBound (StackTraceSet.sequential left right)
      (leftTrace.sequential rightTrace) := by
  obtain ⟨leftLimit, rfl, leftNet, leftExec⟩ := leftBound
  obtain ⟨rightLimit, rfl, rightNet, rightExec⟩ := rightBound
  refine ⟨leftLimit.sequential rightLimit, rfl, ?_, ?_⟩
  · simp only [StackTraceBound.sequential]
    omega
  · simp only [StackTraceBound.sequential]
    exact Int.max_le.mpr ⟨
      Int.le_trans rightExec (Int.le_max_left _ _),
      Int.le_trans (Int.add_le_add rightNet leftExec)
        (Int.le_max_right _ _)⟩

private theorem stackTraceBound_choiceLeft
    {left right : StackTraceSet} {trace : StackTraceBound}
    (bounded : stackTraceBound left trace) :
    stackTraceBound (StackTraceSet.choice left right) trace := by
  obtain ⟨leftLimit, rfl, netBound, execBound⟩ := bounded
  cases right with
  | none => exact ⟨leftLimit, rfl, netBound, execBound⟩
  | some rightLimit =>
      exact ⟨{
        netDiff := max leftLimit.netDiff rightLimit.netDiff
        exec := max leftLimit.exec rightLimit.exec }, rfl,
        Int.le_trans netBound (Int.le_max_left _ _),
        Int.le_trans execBound (Int.le_max_left _ _)⟩

private theorem stackTraceBound_choiceRight
    {left right : StackTraceSet} {trace : StackTraceBound}
    (bounded : stackTraceBound right trace) :
    stackTraceBound (StackTraceSet.choice left right) trace := by
  obtain ⟨rightLimit, rfl, netBound, execBound⟩ := bounded
  cases left with
  | none => exact ⟨rightLimit, rfl, netBound, execBound⟩
  | some leftLimit =>
      exact ⟨{
        netDiff := max leftLimit.netDiff rightLimit.netDiff
        exec := max leftLimit.exec rightLimit.exec }, rfl,
        Int.le_trans netBound (Int.le_max_right _ _),
        Int.le_trans execBound (Int.le_max_right _ _)⟩

private def dynamicChargeBound (summary : PathMaximum) (charge : Nat) : Prop :=
  ∃ limit, summary = some limit ∧ charge ≤ limit

private theorem dynamicChargeBound_sequential
    {left right : PathMaximum} {leftCharge rightCharge : Nat}
    (leftBound : dynamicChargeBound left leftCharge)
    (rightBound : dynamicChargeBound right rightCharge) :
    dynamicChargeBound (PathMaximum.sequential left right)
      (leftCharge + rightCharge) := by
  obtain ⟨leftLimit, rfl, leftLe⟩ := leftBound
  obtain ⟨rightLimit, rfl, rightLe⟩ := rightBound
  exact ⟨leftLimit + rightLimit, rfl, Nat.add_le_add leftLe rightLe⟩

private theorem dynamicChargeBound_choiceLeft
    {left right : PathMaximum} {charge : Nat}
    (bounded : dynamicChargeBound left charge) :
    dynamicChargeBound (PathMaximum.choice left right) charge := by
  obtain ⟨leftLimit, rfl, bound⟩ := bounded
  cases right with
  | none => exact ⟨leftLimit, rfl, bound⟩
  | some rightLimit =>
      exact ⟨max leftLimit rightLimit, rfl,
        Nat.le_trans bound (Nat.le_max_left _ _)⟩

private theorem dynamicChargeBound_choiceRight
    {left right : PathMaximum} {charge : Nat}
    (bounded : dynamicChargeBound right charge) :
    dynamicChargeBound (PathMaximum.choice left right) charge := by
  obtain ⟨rightLimit, rfl, bound⟩ := bounded
  cases left with
  | none => exact ⟨rightLimit, rfl, bound⟩
  | some leftLimit =>
      exact ⟨max leftLimit rightLimit, rfl,
        Nat.le_trans bound (Nat.le_max_right _ _)⟩

private theorem stackTraceBound_thresholdChildSat
    {child : StackPathBounds} {trace : StackTraceBound}
    (selected : child.sat = some trace) (first : Bool) :
    stackTraceBound (appendThresholdAdd first child).sat
      (trace.thresholdChild first) := by
  cases first with
  | false =>
      exact stackTraceBound_sequential
        ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩
        ⟨StackTraceBound.binary, rfl, Int.le_refl _, Int.le_refl _⟩
  | true => exact ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩

private theorem stackTraceBound_thresholdChildDsat
    {child : StackPathBounds} {trace : StackTraceBound}
    (selected : child.dsat = some trace) (first : Bool) :
    stackTraceBound (appendThresholdAdd first child).dsat
      (trace.thresholdChild first) := by
  cases first with
  | false =>
      exact stackTraceBound_sequential
        ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩
        ⟨StackTraceBound.binary, rfl, Int.le_refl _, Int.le_refl _⟩
  | true => exact ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩

private def stackNetBound (summary : StackTraceSet) (netDiff : Int) : Prop :=
  ∃ trace, summary = some trace ∧ netDiff ≤ trace.netDiff

private theorem stackNetBound_sequential
    {left right : StackTraceSet} {leftNet rightNet : Int}
    (leftBound : stackNetBound left leftNet)
    (rightBound : stackNetBound right rightNet) :
    stackNetBound (StackTraceSet.sequential left right) (leftNet + rightNet) := by
  obtain ⟨leftTrace, rfl, leftLe⟩ := leftBound
  obtain ⟨rightTrace, rfl, rightLe⟩ := rightBound
  exact ⟨leftTrace.sequential rightTrace, rfl, by
    simp only [StackTraceBound.sequential]
    omega⟩

private theorem stackNetBound_choiceLeft
    {left right : StackTraceSet} {netDiff : Int}
    (bounded : stackNetBound left netDiff) :
    stackNetBound (StackTraceSet.choice left right) netDiff := by
  obtain ⟨leftTrace, rfl, bound⟩ := bounded
  cases right with
  | none => exact ⟨leftTrace, rfl, bound⟩
  | some rightTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl,
        Int.le_trans bound (Int.le_max_left _ _)⟩

private theorem stackNetBound_choiceRight
    {left right : StackTraceSet} {netDiff : Int}
    (bounded : stackNetBound right netDiff) :
    stackNetBound (StackTraceSet.choice left right) netDiff := by
  obtain ⟨rightTrace, rfl, bound⟩ := bounded
  cases left with
  | none => exact ⟨rightTrace, rfl, bound⟩
  | some leftTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl,
        Int.le_trans bound (Int.le_max_right _ _)⟩

private theorem stackThresholdFold_bounds_path
    {bounds : List StackPathBounds} {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath bounds count netDiff) :
    stackNetBound
      ((stackThresholdFold true [some StackTraceBound.empty] bounds).getD
        count none) netDiff := by
  induction path with
  | nil => exact ⟨StackTraceBound.empty, rfl, Int.le_refl 0⟩
  | @sat bounds count netDiff child childTrace prior selected ih =>
      rw [stackThresholdFold_append, stackThresholdStep_getD_succ]
      apply stackNetBound_choiceRight
      by_cases empty : bounds = []
      · subst bounds
        have inv := prior.nil_inv
        rw [inv.1, inv.2] at ih ⊢
        simp only [List.isEmpty_nil, Bool.and_true, appendThresholdAdd]
        simpa using stackNetBound_sequential ih
          ⟨childTrace, selected, Int.le_refl childTrace.netDiff⟩
      · have notEmpty : bounds.isEmpty = false := by
          simpa [List.isEmpty_iff] using empty
        simp only [notEmpty, Bool.and_false, appendThresholdAdd]
        rw [selected]
        have childBound :
            stackNetBound
              (StackTraceSet.sequential (some childTrace)
                (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
          stackNetBound_sequential
            ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
            ⟨StackTraceBound.binary, rfl, by
              simp [StackTraceBound.binary]⟩
        simpa [empty, Int.add_assoc] using
          stackNetBound_sequential ih childBound
  | @dsat bounds count netDiff child childTrace prior selected ih =>
      rw [stackThresholdFold_append]
      cases count with
      | zero =>
        rw [stackThresholdStep_getD_zero]
        by_cases empty : bounds = []
        · subst bounds
          have netZero := (prior.nil_inv).2
          rw [netZero] at ih ⊢
          simp only [List.isEmpty_nil, Bool.and_true, appendThresholdAdd]
          simpa using stackNetBound_sequential ih
            ⟨childTrace, selected, Int.le_refl childTrace.netDiff⟩
        · have notEmpty : bounds.isEmpty = false := by
            simpa [List.isEmpty_iff] using empty
          simp only [notEmpty, Bool.and_false, appendThresholdAdd]
          rw [selected]
          have childBound :
              stackNetBound
                (StackTraceSet.sequential (some childTrace)
                  (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
            stackNetBound_sequential
              ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
              ⟨StackTraceBound.binary, rfl, by
                simp [StackTraceBound.binary]⟩
          simpa [empty, Int.add_assoc] using
            stackNetBound_sequential ih childBound
      | succ previous =>
        rw [stackThresholdStep_getD_succ]
        apply stackNetBound_choiceLeft
        by_cases empty : bounds = []
        · subst bounds
          obtain ⟨countEq, _⟩ := prior.nil_inv
          simp at countEq
        · have notEmpty : bounds.isEmpty = false := by
            simpa [List.isEmpty_iff] using empty
          simp only [notEmpty, Bool.and_false, appendThresholdAdd]
          rw [selected]
          have childBound :
              stackNetBound
                (StackTraceSet.sequential (some childTrace)
                  (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
            stackNetBound_sequential
              ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
              ⟨StackTraceBound.binary, rfl, by
                simp [StackTraceBound.binary]⟩
          simpa [empty, Int.add_assoc] using
            stackNetBound_sequential ih childBound

private theorem thresholdResourceFold_bounds_path
    {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
    {count dynamic : Nat} {trace : StackTraceBound}
    (path : ThresholdResourcePath stackBounds opBounds count trace dynamic) :
    stackTraceBound
        ((stackThresholdFold true [some StackTraceBound.empty] stackBounds).getD
          count none) trace ∧
      dynamicChargeBound
        ((opThresholdFold [some 0] opBounds).getD count none) dynamic := by
  induction path with
  | nil =>
      exact ⟨⟨StackTraceBound.empty, rfl, Int.le_refl _, Int.le_refl _⟩,
        ⟨0, rfl, Nat.le_refl _⟩⟩
  | @sat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      rw [stackThresholdFold_append, stackThresholdStep_getD_succ,
        opThresholdFold_append, opThresholdStep_getD_succ]
      constructor
      · apply stackTraceBound_choiceRight
        simpa using stackTraceBound_sequential ih.1
          (stackTraceBound_thresholdChildSat stackSelected stackBounds.isEmpty)
      · apply dynamicChargeBound_choiceRight
        exact dynamicChargeBound_sequential ih.2
          ⟨childDynamic, opSelected, Nat.le_refl _⟩
  | @dsat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      rw [stackThresholdFold_append, opThresholdFold_append]
      cases count with
      | zero =>
          rw [stackThresholdStep_getD_zero, opThresholdStep_getD_zero]
          constructor
          · simpa using stackTraceBound_sequential ih.1
              (stackTraceBound_thresholdChildDsat stackSelected
                stackBounds.isEmpty)
          · exact dynamicChargeBound_sequential ih.2
              ⟨childDynamic, opSelected, Nat.le_refl _⟩
      | succ count =>
          rw [stackThresholdStep_getD_succ, opThresholdStep_getD_succ]
          constructor
          · apply stackTraceBound_choiceLeft
            simpa using stackTraceBound_sequential ih.1
              (stackTraceBound_thresholdChildDsat stackSelected
                stackBounds.isEmpty)
          · apply dynamicChargeBound_choiceLeft
            exact dynamicChargeBound_sequential ih.2
              ⟨childDynamic, opSelected, Nat.le_refl _⟩

/-- A concrete exact-count threshold path is bounded by the public
    satisfaction summary for that threshold. The internal dynamic-programming
    table remains an implementation detail. -/
theorem ThresholdStackPath.bounds_thresh
    {fragments : List CoreFragment} {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath (stackPathBoundsList fragments) count netDiff) :
    ∃ trace,
      (stackPathBounds (.thresh count fragments)).sat = some trace ∧
        netDiff ≤ trace.netDiff := by
  obtain ⟨stateTrace, stateEq, bounded⟩ :=
    stackThresholdFold_bounds_path path
  let suffix := StackTraceBound.push.sequential StackTraceBound.equal
  refine ⟨stateTrace.sequential suffix, ?_, ?_⟩
  · simp only [stackPathBounds]
    rw [stateEq]
    rfl
  · simp only [StackTraceBound.sequential, suffix, StackTraceBound.push,
      StackTraceBound.equal]
    omega

/-- An all-dissatisfaction threshold path is bounded by the public
    dissatisfaction summary, independently of the threshold literal. -/
theorem ThresholdStackPath.bounds_thresh_dsat
    {fragments : List CoreFragment} {threshold : Nat} {netDiff : Int}
    (path : ThresholdStackPath (stackPathBoundsList fragments) 0 netDiff) :
    ∃ trace,
      (stackPathBounds (.thresh threshold fragments)).dsat = some trace ∧
        netDiff ≤ trace.netDiff := by
  obtain ⟨stateTrace, stateEq, bounded⟩ :=
    stackThresholdFold_bounds_path path
  let suffix := StackTraceBound.push.sequential StackTraceBound.equal
  refine ⟨stateTrace.sequential suffix, ?_, ?_⟩
  · simp only [stackPathBounds]
    rw [stateEq]
    rfl
  · simp only [StackTraceBound.sequential, suffix, StackTraceBound.push,
      StackTraceBound.equal]
    omega

/-- A concrete exact-count threshold choice is bounded by both public resource
    summaries for the same satisfaction path. The returned stack bound includes
    the final threshold literal and equality comparison. -/
theorem ThresholdResourcePath.bounds_thresh
    {fragments : List CoreFragment} {count dynamic : Nat}
    {trace : StackTraceBound}
    (path : ThresholdResourcePath (stackPathBoundsList fragments)
      (opPathBoundsList fragments) count trace dynamic) :
    ∃ stackLimit opLimit,
      (stackPathBounds (.thresh count fragments)).sat = some stackLimit ∧
      (opPathBounds (.thresh count fragments)).sat = some opLimit ∧
      trace.thresholdComparison.netDiff ≤ stackLimit.netDiff ∧
      trace.thresholdComparison.exec ≤ stackLimit.exec ∧
      dynamic ≤ opLimit := by
  obtain ⟨stackBound, dynamicBound⟩ :=
    thresholdResourceFold_bounds_path path
  have suffixBound : stackTraceBound
      (some (StackTraceBound.push.sequential StackTraceBound.equal))
      (StackTraceBound.push.sequential StackTraceBound.equal) :=
    ⟨_, rfl, Int.le_refl _, Int.le_refl _⟩
  obtain ⟨stackLimit, stackEq, netBound, execBound⟩ :=
    stackTraceBound_sequential stackBound suffixBound
  obtain ⟨opLimit, opEq, dynamicLe⟩ := dynamicBound
  refine ⟨stackLimit, opLimit, ?_, ?_, netBound, execBound, dynamicLe⟩
  · simpa [stackPathBounds, StackTraceBound.thresholdComparison] using stackEq
  · simpa [opPathBounds] using opEq

/-- An all-dissatisfaction threshold choice is bounded by both public
    dissatisfaction summaries. Its dynamic charge is independent of the
    threshold literal used by the enclosing fragment. -/
theorem ThresholdResourcePath.bounds_thresh_dsat
    {fragments : List CoreFragment} {threshold dynamic : Nat}
    {trace : StackTraceBound}
    (path : ThresholdResourcePath (stackPathBoundsList fragments)
      (opPathBoundsList fragments) 0 trace dynamic) :
    ∃ stackLimit opLimit,
      (stackPathBounds (.thresh threshold fragments)).dsat = some stackLimit ∧
      (opPathBounds (.thresh threshold fragments)).dsat = some opLimit ∧
      trace.thresholdComparison.netDiff ≤ stackLimit.netDiff ∧
      trace.thresholdComparison.exec ≤ stackLimit.exec ∧
      dynamic ≤ opLimit := by
  obtain ⟨stackBound, dynamicBound⟩ :=
    thresholdResourceFold_bounds_path path
  have suffixBound : stackTraceBound
      (some (StackTraceBound.push.sequential StackTraceBound.equal))
      (StackTraceBound.push.sequential StackTraceBound.equal) :=
    ⟨_, rfl, Int.le_refl _, Int.le_refl _⟩
  obtain ⟨stackLimit, stackEq, netBound, execBound⟩ :=
    stackTraceBound_sequential stackBound suffixBound
  obtain ⟨opLimit, opEq, dynamicLe⟩ := dynamicBound
  refine ⟨stackLimit, opLimit, ?_, ?_, netBound, execBound, dynamicLe⟩
  · simpa [stackPathBounds, StackTraceBound.thresholdComparison] using stackEq
  · simpa [opPathBounds] using opEq

end LeanMiniscript.Properties
