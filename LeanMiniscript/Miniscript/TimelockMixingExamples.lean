import LeanMiniscript.Miniscript.TypeInference
import LeanMiniscript.Miniscript.ValidationDecidable

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

end LeanMiniscript.Miniscript
