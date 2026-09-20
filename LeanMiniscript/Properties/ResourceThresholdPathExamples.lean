import LeanMiniscript.Properties.ResourceBounds

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript

/-! Regression examples for joint threshold stack and opcode paths. -/

private def firstMulti (key : PubKey) : CoreFragment :=
  .multi 1 [key]

private def secondMulti (first second : PubKey) : CoreFragment :=
  .multi 1 [first, second]

private def firstMultiTrace : StackTraceBound := ⟨1, 4⟩
private def secondMultiTrace : StackTraceBound := ⟨1, 5⟩

private def mixedThresholdTrace : StackTraceBound :=
  (StackTraceBound.empty.sequential
      (firstMultiTrace.thresholdChild true)).sequential
    (secondMultiTrace.thresholdChild false)

/-- Selecting the one-key child satisfaction and the two-key child
    dissatisfaction records one satisfied child and three executed legacy
    multisignature keys on the same source path. -/
private theorem mixedThresholdPath (first second : PubKey) :
    ThresholdResourcePath
      (stackPathBoundsList [firstMulti first, secondMulti first second])
      (opPathBoundsList [firstMulti first, secondMulti first second])
      1 mixedThresholdTrace 3 := by
  simpa [stackPathBoundsList, opPathBoundsList, mixedThresholdTrace,
      firstMultiTrace, secondMultiTrace] using
    (ThresholdResourcePath.dsat
      (stackChild := stackPathBounds (secondMulti first second))
      (opChild := opPathBounds (secondMulti first second))
      (childTrace := secondMultiTrace) (childDynamic := 2)
      (ThresholdResourcePath.sat
        (stackChild := stackPathBounds (firstMulti first))
        (opChild := opPathBounds (firstMulti first))
        (childTrace := firstMultiTrace) (childDynamic := 1)
        ThresholdResourcePath.nil (by rfl) (by rfl))
      (by rfl) (by rfl))

/-- The public satisfaction summaries jointly cover the concrete stack trace
    and dynamic key charge selected by the threshold row. -/
example (first second : PubKey) :
    ∃ stackLimit opLimit,
      (stackPathBounds
        (.thresh 1 [firstMulti first, secondMulti first second])).sat =
          some stackLimit ∧
      (opPathBounds
        (.thresh 1 [firstMulti first, secondMulti first second])).sat =
          some opLimit ∧
      mixedThresholdTrace.thresholdComparison.netDiff ≤ stackLimit.netDiff ∧
      mixedThresholdTrace.thresholdComparison.exec ≤ stackLimit.exec ∧
      3 ≤ opLimit :=
  (mixedThresholdPath first second).bounds_thresh

private def allDissatisfiedThresholdTrace : StackTraceBound :=
  (StackTraceBound.empty.sequential
      (firstMultiTrace.thresholdChild true)).sequential
    (secondMultiTrace.thresholdChild false)

private theorem allDissatisfiedThresholdPath (first second : PubKey) :
    ThresholdResourcePath
      (stackPathBoundsList [firstMulti first, secondMulti first second])
      (opPathBoundsList [firstMulti first, secondMulti first second])
      0 allDissatisfiedThresholdTrace 3 := by
  simpa [stackPathBoundsList, opPathBoundsList, allDissatisfiedThresholdTrace,
      firstMultiTrace, secondMultiTrace] using
    (ThresholdResourcePath.dsat
      (stackChild := stackPathBounds (secondMulti first second))
      (opChild := opPathBounds (secondMulti first second))
      (childTrace := secondMultiTrace) (childDynamic := 2)
      (ThresholdResourcePath.dsat
        (stackChild := stackPathBounds (firstMulti first))
        (opChild := opPathBounds (firstMulti first))
        (childTrace := firstMultiTrace) (childDynamic := 1)
        ThresholdResourcePath.nil (by rfl) (by rfl))
      (by rfl) (by rfl))

/-- The all-dissatisfaction path is reusable for any enclosing threshold
    literal because its child choices and dynamic charge do not change. -/
example (first second : PubKey) (threshold : Nat) :
    ∃ stackLimit opLimit,
      (stackPathBounds
        (.thresh threshold [firstMulti first, secondMulti first second])).dsat =
          some stackLimit ∧
      (opPathBounds
        (.thresh threshold [firstMulti first, secondMulti first second])).dsat =
          some opLimit ∧
      allDissatisfiedThresholdTrace.thresholdComparison.netDiff ≤
        stackLimit.netDiff ∧
      allDissatisfiedThresholdTrace.thresholdComparison.exec ≤ stackLimit.exec ∧
      3 ≤ opLimit :=
  (allDissatisfiedThresholdPath first second).bounds_thresh_dsat

end LeanMiniscript.Properties
