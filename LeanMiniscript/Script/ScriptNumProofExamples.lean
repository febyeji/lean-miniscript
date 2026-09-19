import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Script

/-- The largest nonnegative four-byte Script number round-trips in strict
    minimal-data mode. -/
example : decodeScriptNum (scriptNat 2147483647) true
    maxArithmeticScriptNumBytes = .ok (2147483647 : Int) :=
  decodeScriptNum_scriptNat_of_lt (by native_decide) true

/-- Its canonical encoding is truthy. -/
example : castToBool (scriptNat 2147483647) = true :=
  castToBool_scriptNat_of_pos_of_lt (by native_decide) (by native_decide)

/-- The exclusive boundary is rejected by the proof-carrying arithmetic
    guard before any numeric opcode proof can consume it. -/
example : ¬ ArithmeticScriptNatSafe maxArithmeticScriptNatExclusive := by
  intro safe
  exact Nat.lt_irrefl maxArithmeticScriptNatExclusive safe.1

/-- Every possible Script element size has an exact arithmetic decode. -/
example (size : Nat) (bounded : size ≤ maxScriptElementSize)
    (minimal : Bool) :
    decodeScriptNum (scriptNat size) minimal maxArithmeticScriptNumBytes =
      .ok (Int.ofNat size) :=
  decodeScriptNum_scriptNat_of_le_maxScriptElementSize bounded minimal

/-- A successful ordinary decode remains valid at the extended timelock byte
    limit. -/
example (minimal : Bool) :
    decodeScriptNum (scriptNat 500000000) minimal
      maxTimelockScriptNumBytes = .ok (500000000 : Int) := by
  apply decodeScriptNum_mono (small := maxArithmeticScriptNumBytes)
  · native_decide
  · exact decodeScriptNum_scriptNat_of_lt (by native_decide) minimal

end LeanMiniscript.Script
