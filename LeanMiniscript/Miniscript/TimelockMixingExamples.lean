import LeanMiniscript.Miniscript.Checked

namespace LeanMiniscript.Miniscript

/-! # Timelock classification and mixing regressions -/

/-- The BIP 68 type flag is a bit, not a numeric threshold. -/
example : TimelockUsage.sequenceLocktimeIsTime
    (2 * SEQUENCE_LOCKTIME_TYPE_FLAG) = false := by
  native_decide

example : TimelockUsage.sequenceLocktimeIsTime
    (3 * SEQUENCE_LOCKTIME_TYPE_FLAG) = true := by
  native_decide

example : TimelockUsage.fromOlder (2 * SEQUENCE_LOCKTIME_TYPE_FLAG) =
    { relativeHeight := true } := by
  native_decide

example : TimelockUsage.fromOlder (3 * SEQUENCE_LOCKTIME_TYPE_FLAG) =
    { relativeTime := true } := by
  native_decide

private def sameClassAbsolute : CoreFragment :=
  .and_v (.v (.after 1)) (.after 2)

/-- Timelock compatibility is not a correctness type modifier. -/
example : inferType .p2wsh sameClassAbsolute = some ⟨.B, { z := true }⟩ := by
  native_decide

example : sameClassAbsolute.WellFormed .p2wsh := by
  native_decide

private def mixedAbsolute : CoreFragment :=
  .and_v (.v (.after (LOCKTIME_THRESHOLD - 1))) (.after LOCKTIME_THRESHOLD)

/-- AND-like combinators reject height/time mixing in one lock family. -/
example : ¬ mixedAbsolute.WellFormed .p2wsh := by
  native_decide

private def mixedRelative : CoreFragment :=
  .and_v
    (.v (.older (2 * SEQUENCE_LOCKTIME_TYPE_FLAG)))
    (.older (3 * SEQUENCE_LOCKTIME_TYPE_FLAG))

example : ¬ mixedRelative.WellFormed .p2wsh := by
  native_decide

/-- Absolute and relative locks may use different units. -/
example : (CoreFragment.and_v (.v (.after 1))
    (.older SEQUENCE_LOCKTIME_TYPE_FLAG)).WellFormed .p2wsh := by
  native_decide

/-- OR branches may use different absolute lock units. -/
example : (CoreFragment.or_i (.after (LOCKTIME_THRESHOLD - 1))
    (.after LOCKTIME_THRESHOLD)).WellFormed .p2wsh := by
  native_decide

private def exclusiveAbsoluteAndor : CoreFragment :=
  .andor .zero
    (.after (LOCKTIME_THRESHOLD - 1))
    (.after LOCKTIME_THRESHOLD)

/-- The Y and Z branches of `andor(X,Y,Z)` are mutually exclusive, so their
    height/time locks do not conflict. -/
example : exclusiveAbsoluteAndor.WellFormed .p2wsh := by
  native_decide

example : (inferType .p2wsh exclusiveAbsoluteAndor).isSome = true := by
  native_decide

example : (CheckedFragment.ofRaw? .p2wsh exclusiveAbsoluteAndor).isSome = true := by
  native_decide

private def absoluteTimedCondition : CoreFragment :=
  .n (.or_i .zero (.after (LOCKTIME_THRESHOLD - 1)))

/-- The satisfied X/Y path still rejects mixed lock units. -/
example : ¬ (CoreFragment.andor absoluteTimedCondition
    (.after LOCKTIME_THRESHOLD) .one).WellFormed .p2wsh := by
  native_decide

/-- The dissatisfied X/Z path does not combine X's satisfaction timelock with
    the Z branch. -/
example : (CoreFragment.andor absoluteTimedCondition .one
    (.after LOCKTIME_THRESHOLD)).WellFormed .p2wsh := by
  native_decide

private def exclusiveRelativeAndor : CoreFragment :=
  .andor .zero
    (.older (2 * SEQUENCE_LOCKTIME_TYPE_FLAG))
    (.older (3 * SEQUENCE_LOCKTIME_TYPE_FLAG))

example : exclusiveRelativeAndor.WellFormed .p2wsh := by
  native_decide

private def relativeTimedCondition : CoreFragment :=
  .n (.or_i .zero (.older (2 * SEQUENCE_LOCKTIME_TYPE_FLAG)))

example : ¬ (CoreFragment.andor relativeTimedCondition
    (.older (3 * SEQUENCE_LOCKTIME_TYPE_FLAG)) .one).WellFormed .p2wsh := by
  native_decide

example : (CoreFragment.andor relativeTimedCondition .one
    (.older (3 * SEQUENCE_LOCKTIME_TYPE_FLAG))).WellFormed .p2wsh := by
  native_decide

/-- An enclosing AND preserves the path exclusivity already checked inside its
    child. -/
example : (CoreFragment.and_v (.v exclusiveAbsoluteAndor) .one).WellFormed .p2wsh := by
  native_decide

example : (inferType .p2wsh
    (.and_v (.v exclusiveAbsoluteAndor) .one)).isSome = true := by
  native_decide

/-- A threshold only imposes mixing compatibility when at least two branches
    must be satisfied. -/
example : (CoreFragment.thresh 1 [
    .after (LOCKTIME_THRESHOLD - 1),
    .after LOCKTIME_THRESHOLD
  ]).WellFormed .p2wsh := by
  native_decide

example : ¬ (CoreFragment.thresh 2 [
    .after (LOCKTIME_THRESHOLD - 1),
    .after LOCKTIME_THRESHOLD
  ]).WellFormed .p2wsh := by
  native_decide

private def typedHeightCondition : CoreFragment :=
  .n (.or_i .zero (.after (LOCKTIME_THRESHOLD - 1)))

private def typedTimeCondition : CoreFragment :=
  .n (.or_i .zero (.after LOCKTIME_THRESHOLD))

private def typedMixedThreshold : CoreFragment :=
  .thresh 2 [typedHeightCondition, .a typedTimeCondition]

/-- Distinct threshold children with mixed units remain rejected even when the
    complete threshold expression is type-correct. -/
example : (inferType .p2wsh typedMixedThreshold).isSome = true := by
  native_decide

example : ¬ typedMixedThreshold.WellFormed .p2wsh := by
  native_decide

private def thresholdChildWithExclusiveLocks : CoreFragment :=
  .n (.or_i .zero exclusiveAbsoluteAndor)

/-- Threshold compatibility compares distinct children and preserves exclusive
    timelock branches contained in one child. -/
example : (CoreFragment.thresh 2 [
    thresholdChildWithExclusiveLocks,
    .a .zero
  ]).WellFormed .p2wsh := by
  native_decide

example : (inferType .p2wsh (.thresh 2 [
    thresholdChildWithExclusiveLocks,
    .a .zero
  ])).isSome = true := by
  native_decide

example : (CheckedFragment.ofRaw? .p2wsh (.thresh 2 [
    thresholdChildWithExclusiveLocks,
    .a .zero
  ])).isSome = true := by
  native_decide

end LeanMiniscript.Miniscript
