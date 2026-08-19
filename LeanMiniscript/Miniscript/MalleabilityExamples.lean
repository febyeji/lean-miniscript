import LeanMiniscript.Miniscript.MalleabilityInferenceProofs
import LeanMiniscript.Miniscript.TypeInference
import LeanMiniscript.Miniscript.ValidationDecidable

namespace LeanMiniscript.Miniscript

/-! # Build-checked BIP 379 malleability fixtures -/

private def compressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0x11).toArray⟩

private def xOnlyKey : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0x22).toArray⟩

private def hash256Fixture : Hash256 :=
  Hash256.ofBytes ⟨(List.replicate 32 0x33).toArray⟩

private def hash160Fixture : Hash160 :=
  Hash160.ofBytes ⟨(List.replicate 20 0x44).toArray⟩

private def signedB : CoreFragment := .c (.pk_k compressedKey)
private def signedW : CoreFragment := .s signedB
private def verifyTrue : CoreFragment := .v .one

inductive MalleabilityConstructorTag where
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 | hash160
  | andV | andB | orB | orC | orD | orI | andor
  | a | s | c | d | v | j | n
  | thresh | multi | multiA
  deriving DecidableEq

private def CoreFragment.malleabilityConstructorTag :
    CoreFragment → MalleabilityConstructorTag
  | .zero => .zero
  | .one => .one
  | .pk_k _ => .pkK
  | .pk_h _ => .pkH
  | .older _ => .older
  | .after _ => .after
  | .sha256 _ => .sha256
  | .hash256 _ => .hash256
  | .ripemd160 _ => .ripemd160
  | .hash160 _ => .hash160
  | .and_v _ _ => .andV
  | .and_b _ _ => .andB
  | .or_b _ _ => .orB
  | .or_c _ _ => .orC
  | .or_d _ _ => .orD
  | .or_i _ _ => .orI
  | .andor _ _ _ => .andor
  | .a _ => .a
  | .s _ => .s
  | .c _ => .c
  | .d _ => .d
  | .v _ => .v
  | .j _ => .j
  | .n _ => .n
  | .thresh _ _ => .thresh
  | .multi _ _ => .multi
  | .multi_a _ _ => .multiA

structure MalleabilityFixture where
  tag : MalleabilityConstructorTag
  ctx : ScriptContext
  fragment : CoreFragment
  expected : MalleabilityModifiers

private def MalleabilityFixture.passes (fixture : MalleabilityFixture) : Bool :=
  fixture.fragment.malleabilityConstructorTag == fixture.tag &&
  decide (fixture.fragment.WellFormed fixture.ctx) &&
  (inferType fixture.ctx fixture.fragment).isSome &&
  match inferMalleability fixture.ctx fixture.fragment with
  | some actual => actual == fixture.expected
  | none => false

/-- One valid, correctly typed fixture for every current core constructor. -/
def malleabilityFixtures : List MalleabilityFixture := [
  { tag := .zero, ctx := .p2wsh, fragment := .zero,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .one, ctx := .p2wsh, fragment := .one,
    expected := { f := true, nonMalleable := true } },
  { tag := .pkK, ctx := .p2wsh, fragment := .pk_k compressedKey,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .pkH, ctx := .p2wsh, fragment := .pk_h compressedKey,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .older, ctx := .p2wsh, fragment := .older 42,
    expected := { f := true, nonMalleable := true } },
  { tag := .after, ctx := .p2wsh, fragment := .after 500000000,
    expected := { f := true, nonMalleable := true } },
  { tag := .sha256, ctx := .p2wsh, fragment := .sha256 hash256Fixture,
    expected := { nonMalleable := true } },
  { tag := .hash256, ctx := .p2wsh, fragment := .hash256 hash256Fixture,
    expected := { nonMalleable := true } },
  { tag := .ripemd160, ctx := .p2wsh, fragment := .ripemd160 hash160Fixture,
    expected := { nonMalleable := true } },
  { tag := .hash160, ctx := .p2wsh, fragment := .hash160 hash160Fixture,
    expected := { nonMalleable := true } },
  { tag := .andV, ctx := .p2wsh, fragment := .and_v verifyTrue .zero,
    expected := { s := true, nonMalleable := true } },
  { tag := .andB, ctx := .p2wsh, fragment := .and_b .zero signedW,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .orB, ctx := .p2wsh, fragment := .or_b .zero signedW,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .orC, ctx := .p2wsh, fragment := .or_c .zero verifyTrue,
    expected := { f := true, nonMalleable := true } },
  { tag := .orD, ctx := .p2wsh, fragment := .or_d .zero .one,
    expected := { f := true, nonMalleable := true } },
  { tag := .orI, ctx := .p2wsh, fragment := .or_i .zero .one,
    expected := { e := true, nonMalleable := true } },
  { tag := .andor, ctx := .p2wsh, fragment := .andor .zero .one .zero,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .a, ctx := .p2wsh, fragment := .a .zero,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .s, ctx := .p2wsh, fragment := .s signedB,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .c, ctx := .p2wsh, fragment := signedB,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .d, ctx := .p2wsh, fragment := .d verifyTrue,
    expected := { e := true, nonMalleable := true } },
  { tag := .v, ctx := .p2wsh, fragment := .v .zero,
    expected := { s := true, f := true, nonMalleable := true } },
  { tag := .j, ctx := .p2wsh, fragment := .j (.sha256 hash256Fixture),
    expected := { nonMalleable := true } },
  { tag := .n, ctx := .p2wsh, fragment := .n .zero,
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .thresh, ctx := .p2wsh,
    fragment := .thresh 1 [.zero, signedW],
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .multi, ctx := .p2wsh,
    fragment := .multi 1 [compressedKey],
    expected := { s := true, e := true, nonMalleable := true } },
  { tag := .multiA, ctx := .tapscript,
    fragment := .multi_a 1 [xOnlyKey],
    expected := { s := true, e := true, nonMalleable := true } }
]

example : malleabilityFixtures.all MalleabilityFixture.passes = true := by
  native_decide

/-- Fixture coverage stays exhaustive when the current tag type is inspected. -/
theorem malleabilityFixtures_cover (tag : MalleabilityConstructorTag) :
    tag ∈ malleabilityFixtures.map (·.tag) := by
  cases tag <;> native_decide

/-! ## Context rejection and malleability-requirement boundaries -/

example : inferMalleability .tapscript (.multi 1 [xOnlyKey]) = none := by
  native_decide

example : inferMalleability .p2wsh (.multi_a 1 [compressedKey]) = none := by
  native_decide

private def nonExpressiveOr : CoreFragment :=
  .or_b .zero (.s (.sha256 hash256Fixture))

example : (inferType .p2wsh nonExpressiveOr).isSome = true := by
  native_decide

example : inferMalleability .p2wsh nonExpressiveOr =
    some { e := true, nonMalleable := false } := by
  native_decide

example : inferMalleability .p2wsh (.or_i .one .one) =
    some { f := true, nonMalleable := false } := by
  native_decide

/-! The following golden cases exercise Boolean branches not distinguished by
the one-fixture-per-constructor coverage above. -/

private def signedForcedB : CoreFragment :=
  .and_v (.v signedB) .one

example : inferMalleability .p2wsh (.and_b .one (.a .one)) =
    some { f := true, nonMalleable := true } := by
  native_decide

example : inferMalleability .p2wsh (.and_b signedForcedB (.a .zero)) =
    some { s := true, f := true, nonMalleable := true } := by
  native_decide

example : inferMalleability .p2wsh (.and_b .zero (.a signedForcedB)) =
    some { s := true, f := true, nonMalleable := true } := by
  native_decide

private def unsignedExpressiveB : CoreFragment := .or_i .zero .one
private def unsignedExpressiveW : CoreFragment := .a unsignedExpressiveB

private def thresholdAtRequirementBoundary : CoreFragment :=
  .thresh 2 [unsignedExpressiveB, unsignedExpressiveW]

private def thresholdBeyondRequirement : CoreFragment :=
  .thresh 1 [unsignedExpressiveB, unsignedExpressiveW]

example : (inferType .p2wsh thresholdAtRequirementBoundary).isSome = true := by
  native_decide

example : inferMalleability .p2wsh thresholdAtRequirementBoundary =
    some { nonMalleable := true } := by
  native_decide

example : inferMalleability .p2wsh thresholdBeyondRequirement = some {} := by
  native_decide

end LeanMiniscript.Miniscript
