import LeanMiniscript.Miniscript.Sane

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Properties

private def fixtureKey : PubKey :=
  PubKey.ofBytes ⟨#[2] ++ (List.replicate 32 17).toArray⟩

private def isOk {α : Type} : Except SaneError α → Bool
  | .ok _ => true
  | .error _ => false

private def hasError {α : Type} (expected : SaneError) :
    Except SaneError α → Bool
  | .ok _ => false
  | .error actual => actual == expected

private def wrapN : Nat → CoreFragment → CoreFragment
  | 0, fragment => fragment
  | n + 1, fragment => .n (wrapN n fragment)

/-- Static sanity follows Bitcoin Core's vacuous `m` and `s` properties: `0`
    is sane even though it has no satisfaction. -/
example : isOk (checkSane .p2wsh .zero) = true := by
  native_decide

example : hasError .signatureNotRequired (checkSane .p2wsh .one) = true := by
  native_decide

example : hasError .notTopLevel
    (checkSane .p2wsh (.pk_k fixtureKey)) = true := by
  native_decide

example : hasError .duplicateKeys
    (checkSane .p2wsh
      (.or_i (.c (.pk_k fixtureKey)) (.c (.pk_k fixtureKey)))) = true := by
  native_decide

example : hasError .malleable
    (checkSane .p2wsh (.or_i .one .one)) = true := by
  native_decide

example : isOk (checkSane .p2wsh (.c (.pk_k fixtureKey))) = true := by
  native_decide

/-- CHECKSIG contributes its static opcode once. Two hundred `n:` wrappers
    bring this fragment exactly to the P2WSH limit of 201 operations. -/
example : isOk
    (checkSane .p2wsh (wrapN 200 (.c (.pk_k fixtureKey)))) = true := by
  native_decide

example : hasError .resourceLimitsExceeded
    (checkSane .p2wsh (wrapN 201 (.c (.pk_k fixtureKey)))) = true := by
  native_decide

private def indexedCompressedKey (index : Nat) : PubKey :=
  PubKey.ofBytes
    ⟨#[0x02] ++ Array.replicate 31 0 ++ #[UInt8.ofNat index]⟩

private def prependVerifiedKeys : List Nat → CoreFragment → CoreFragment
  | [], tail => tail
  | index :: indices, tail =>
      .and_v (.v (.c (.pk_k (indexedCompressedKey index))))
        (prependVerifiedKeys indices tail)

/-- Core's VERIFY substitutions keep this 100-signature P2WSH fragment below
    both the 3600-byte script limit and the 201-opcode limit. -/
private def verifyOptimizationBoundary : CoreFragment :=
  prependVerifiedKeys (List.range 99)
    (.and_v (.v (.after 1)) (.c (.pk_k (indexedCompressedKey 99))))

example : (resourceUsage verifyOptimizationBoundary).scriptSize = some 3503 := by
  native_decide

example : maxSatisfactionOpCount verifyOptimizationBoundary = some 102 := by
  native_decide

example : maxSatisfactionInitialStack verifyOptimizationBoundary = some 100 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh verifyOptimizationBoundary = true := by
  native_decide

example : isOk (checkSane .p2wsh verifyOptimizationBoundary) = true := by
  native_decide

example : isOk (checkSaneSurface .p2wsh (.pk fixtureKey)) = true := by
  native_decide

end LeanMiniscript.Miniscript
