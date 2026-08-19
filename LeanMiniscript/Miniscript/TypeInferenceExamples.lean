import LeanMiniscript.Miniscript.TypeInferenceProofs
import LeanMiniscript.Miniscript.ValidationDecidable
import LeanMiniscript.Miniscript.Checked

namespace LeanMiniscript.Miniscript

/-!
# Build-checked BIP 379 correctness-typing fixtures

The expected types below follow the correctness table at
`bitcoin/bips@442e9628b3dcca1b65f0df8af2308f8260e00caa`. In particular, the
`d:` wrapper is `Bond` in P2WSH and `Bondu` in Tapscript because only the latter
context consensus-enforces MINIMALIF.
-/

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
private def legacyMulti : CoreFragment := .multi 1 [compressedKey]
private def verifySignedB : CoreFragment := .v signedB
private def verifyLegacyMulti : CoreFragment := .v legacyMulti
private def nonUnitNonzeroB : CoreFragment :=
  .and_v verifyLegacyMulti (.older 1)
private def nonUnitOneArgB : CoreFragment :=
  .or_i (.older 1) (.older 2)
private def dVerifyTrue : CoreFragment := .d verifyTrue

inductive CorrectnessConstructorTag where
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 | hash160
  | andV | andB | orB | orC | orD | orI | andor
  | a | s | c | d | v | j | n
  | thresh | multi | multiA
  deriving DecidableEq

private def CoreFragment.correctnessConstructorTag :
    CoreFragment → CorrectnessConstructorTag
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

structure CorrectnessFixture where
  tag : CorrectnessConstructorTag
  ctx : ScriptContext
  fragment : CoreFragment
  expected : MiniType

private def CorrectnessFixture.passes (fixture : CorrectnessFixture) : Bool :=
  fixture.fragment.correctnessConstructorTag == fixture.tag &&
  decide (fixture.fragment.WellFormed fixture.ctx) &&
  inferType fixture.ctx fixture.fragment == some fixture.expected

/-- One context-valid fixture with its exact BIP 379 correctness type for every
    current core constructor. -/
def correctnessFixtures : List CorrectnessFixture := [
  { tag := .zero, ctx := .p2wsh, fragment := .zero,
    expected := ⟨.B, { z := true, d := true, u := true }⟩ },
  { tag := .one, ctx := .p2wsh, fragment := .one,
    expected := ⟨.B, { z := true, u := true }⟩ },
  { tag := .pkK, ctx := .p2wsh, fragment := .pk_k compressedKey,
    expected := ⟨.K, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .pkH, ctx := .p2wsh, fragment := .pk_h compressedKey,
    expected := ⟨.K, { n := true, d := true, u := true }⟩ },
  { tag := .older, ctx := .p2wsh, fragment := .older 42,
    expected := ⟨.B, { z := true }⟩ },
  { tag := .after, ctx := .p2wsh, fragment := .after 500000000,
    expected := ⟨.B, { z := true }⟩ },
  { tag := .sha256, ctx := .p2wsh, fragment := .sha256 hash256Fixture,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .hash256, ctx := .p2wsh, fragment := .hash256 hash256Fixture,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .ripemd160, ctx := .p2wsh, fragment := .ripemd160 hash160Fixture,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .hash160, ctx := .p2wsh, fragment := .hash160 hash160Fixture,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .andV, ctx := .p2wsh, fragment := .and_v verifyTrue .zero,
    expected := ⟨.B, { z := true, u := true }⟩ },
  { tag := .andB, ctx := .p2wsh, fragment := .and_b .zero (.a .zero),
    expected := ⟨.B, { d := true, u := true }⟩ },
  { tag := .orB, ctx := .p2wsh, fragment := .or_b .zero (.a .zero),
    expected := ⟨.B, { d := true, u := true }⟩ },
  { tag := .orC, ctx := .p2wsh, fragment := .or_c .zero verifyTrue,
    expected := ⟨.V, { z := true }⟩ },
  { tag := .orD, ctx := .p2wsh, fragment := .or_d .zero .one,
    expected := ⟨.B, { z := true, u := true }⟩ },
  { tag := .orI, ctx := .p2wsh, fragment := .or_i .zero .one,
    expected := ⟨.B, { o := true, d := true, u := true }⟩ },
  { tag := .andor, ctx := .p2wsh, fragment := .andor .zero .one .zero,
    expected := ⟨.B, { z := true, d := true, u := true }⟩ },
  { tag := .a, ctx := .p2wsh, fragment := .a .zero,
    expected := ⟨.W, { d := true, u := true }⟩ },
  { tag := .s, ctx := .p2wsh, fragment := signedW,
    expected := ⟨.W, { d := true, u := true }⟩ },
  { tag := .c, ctx := .p2wsh, fragment := signedB,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .d, ctx := .p2wsh, fragment := .d verifyTrue,
    expected := ⟨.B, { o := true, n := true, d := true }⟩ },
  { tag := .v, ctx := .p2wsh, fragment := .v .zero,
    expected := ⟨.V, { z := true }⟩ },
  { tag := .j, ctx := .p2wsh, fragment := .j (.sha256 hash256Fixture),
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },
  { tag := .n, ctx := .p2wsh, fragment := .n .zero,
    expected := ⟨.B, { z := true, d := true, u := true }⟩ },
  { tag := .thresh, ctx := .p2wsh,
    fragment := .thresh 1 [.zero, .a .zero],
    expected := ⟨.B, { d := true, u := true }⟩ },
  { tag := .multi, ctx := .p2wsh,
    fragment := .multi 1 [compressedKey],
    expected := ⟨.B, { n := true, d := true, u := true }⟩ },
  { tag := .multiA, ctx := .tapscript,
    fragment := .multi_a 1 [xOnlyKey],
    expected := ⟨.B, { d := true, u := true }⟩ }
]

example : correctnessFixtures.all CorrectnessFixture.passes = true := by
  native_decide

/-- The valid fixture table stays exhaustive as the constructor tag evolves. -/
theorem correctnessFixtures_cover (tag : CorrectnessConstructorTag) :
    tag ∈ correctnessFixtures.map (·.tag) := by
  cases tag <;> native_decide

/-! ## Correctness-modifier propagation boundaries -/

/-- Branch-sensitive fixtures complement constructor coverage by exercising
    both disjuncts and true/false propagation boundaries in the BIP 379
    correctness formulas. -/
def correctnessPropagationFixtures : List CorrectnessFixture := [
  -- `and_v`: both `o` disjuncts and both `n` disjuncts.
  { tag := .andV, ctx := .p2wsh,
    fragment := .and_v verifyTrue signedB,
    expected := ⟨.B, { o := true, n := true, u := true }⟩ },
  { tag := .andV, ctx := .p2wsh,
    fragment := .and_v verifySignedB .one,
    expected := ⟨.B, { o := true, n := true, u := true }⟩ },
  { tag := .andV, ctx := .p2wsh,
    fragment := nonUnitNonzeroB,
    expected := ⟨.B, { n := true }⟩ },
  { tag := .andV, ctx := .p2wsh,
    fragment := .and_v verifyTrue legacyMulti,
    expected := ⟨.B, { n := true, u := true }⟩ },

  -- `and_b`: each `d` operand can independently clear the result; `n`
  -- propagates from the B child.
  { tag := .andB, ctx := .p2wsh,
    fragment := .and_b .one (.a .zero),
    expected := ⟨.B, { u := true }⟩ },
  { tag := .andB, ctx := .p2wsh,
    fragment := .and_b .zero (.a .one),
    expected := ⟨.B, { u := true }⟩ },
  { tag := .andB, ctx := .p2wsh,
    fragment := .and_b signedB (.a .zero),
    expected := ⟨.B, { n := true, d := true, u := true }⟩ },

  -- `or_c`/`or_d`: z/o and result d/u propagation.
  { tag := .orC, ctx := .p2wsh,
    fragment := .or_c signedB verifyTrue,
    expected := ⟨.V, { o := true }⟩ },
  { tag := .orC, ctx := .p2wsh,
    fragment := .or_c .zero verifySignedB,
    expected := ⟨.V, {}⟩ },
  { tag := .orD, ctx := .p2wsh,
    fragment := .or_d signedB .one,
    expected := ⟨.B, { o := true, u := true }⟩ },
  { tag := .orD, ctx := .p2wsh,
    fragment := .or_d .zero .zero,
    expected := ⟨.B, { z := true, d := true, u := true }⟩ },
  { tag := .orD, ctx := .p2wsh,
    fragment := .or_d .zero (.older 1),
    expected := ⟨.B, { z := true }⟩ },
  { tag := .orD, ctx := .p2wsh,
    fragment := .or_d .zero dVerifyTrue,
    expected := ⟨.B, { d := true }⟩ },

  -- `or_i`: false d/u results in addition to the all-true constructor case.
  { tag := .orI, ctx := .p2wsh,
    fragment := .or_i .one .one,
    expected := ⟨.B, { o := true, u := true }⟩ },
  { tag := .orI, ctx := .p2wsh,
    fragment := .or_i .one (.older 1),
    expected := ⟨.B, { o := true }⟩ },
  { tag := .orI, ctx := .p2wsh,
    fragment := .or_i .zero (.older 1),
    expected := ⟨.B, { o := true, d := true }⟩ },

  -- `andor`: both `o` disjuncts plus false d/u propagation.
  { tag := .andor, ctx := .p2wsh,
    fragment := .andor .zero signedB signedB,
    expected := ⟨.B, { o := true, d := true, u := true }⟩ },
  { tag := .andor, ctx := .p2wsh,
    fragment := .andor signedB .one .zero,
    expected := ⟨.B, { o := true, d := true, u := true }⟩ },
  { tag := .andor, ctx := .p2wsh,
    fragment := .andor .zero (.older 1) .one,
    expected := ⟨.B, { z := true }⟩ },
  { tag := .andor, ctx := .p2wsh,
    fragment := .andor .zero .one dVerifyTrue,
    expected := ⟨.B, { d := true }⟩ },

  -- Wrapper propagation for d/u and z/o/n.
  { tag := .a, ctx := .p2wsh, fragment := .a .one,
    expected := ⟨.W, { u := true }⟩ },
  { tag := .a, ctx := .p2wsh, fragment := .a (.older 1),
    expected := ⟨.W, {}⟩ },
  { tag := .a, ctx := .p2wsh, fragment := .a dVerifyTrue,
    expected := ⟨.W, { d := true }⟩ },
  { tag := .s, ctx := .p2wsh, fragment := .s (.or_i .one .one),
    expected := ⟨.W, { u := true }⟩ },
  { tag := .s, ctx := .p2wsh, fragment := .s nonUnitOneArgB,
    expected := ⟨.W, {}⟩ },
  { tag := .s, ctx := .p2wsh, fragment := .s dVerifyTrue,
    expected := ⟨.W, { d := true }⟩ },
  { tag := .c, ctx := .p2wsh,
    fragment := .c (.and_v verifyTrue (.pk_k compressedKey)),
    expected := ⟨.B, { o := true, n := true, u := true }⟩ },
  { tag := .c, ctx := .p2wsh, fragment := .c (.pk_h compressedKey),
    expected := ⟨.B, { n := true, d := true, u := true }⟩ },
  { tag := .v, ctx := .p2wsh, fragment := verifySignedB,
    expected := ⟨.V, { o := true, n := true }⟩ },
  { tag := .v, ctx := .p2wsh, fragment := verifyLegacyMulti,
    expected := ⟨.V, { n := true }⟩ },
  { tag := .j, ctx := .p2wsh, fragment := .j nonUnitNonzeroB,
    expected := ⟨.B, { n := true, d := true }⟩ },
  { tag := .n, ctx := .p2wsh, fragment := .n .one,
    expected := ⟨.B, { z := true, u := true }⟩ },
  { tag := .n, ctx := .p2wsh, fragment := .n signedB,
    expected := ⟨.B, { o := true, n := true, d := true, u := true }⟩ },

  -- `thresh`: all-z and exactly-one-o outcomes.
  { tag := .thresh, ctx := .p2wsh, fragment := .thresh 1 [.zero],
    expected := ⟨.B, { z := true, d := true, u := true }⟩ },
  { tag := .thresh, ctx := .p2wsh, fragment := .thresh 1 [signedB],
    expected := ⟨.B, { o := true, d := true, u := true }⟩ },

  -- Every parent rule that consumes the Tapscript-only `d:u` result.
  { tag := .orC, ctx := .tapscript,
    fragment := .or_c dVerifyTrue verifyTrue,
    expected := ⟨.V, { o := true }⟩ },
  { tag := .orD, ctx := .tapscript,
    fragment := .or_d dVerifyTrue .one,
    expected := ⟨.B, { o := true, u := true }⟩ },
  { tag := .andor, ctx := .tapscript,
    fragment := .andor dVerifyTrue .one .zero,
    expected := ⟨.B, { o := true, d := true, u := true }⟩ },
  { tag := .thresh, ctx := .tapscript,
    fragment := .thresh 1 [dVerifyTrue],
    expected := ⟨.B, { o := true, d := true, u := true }⟩ }
]

example : correctnessPropagationFixtures.all CorrectnessFixture.passes = true := by
  native_decide

/-! ## Ill-typed constructor boundaries -/

private def typingRejected (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  (inferType ctx fragment).isNone

private def rejectedTypingFixtures : List (ScriptContext × CoreFragment) := [
  (.p2wsh, .and_v .zero .one),
  (.p2wsh, .and_b .zero .one),
  (.p2wsh, .or_b .one (.a .zero)),
  (.p2wsh, .or_c .one verifyTrue),
  (.p2wsh, .or_d .one .zero),
  (.p2wsh, .or_i .zero (.pk_k compressedKey)),
  (.p2wsh, .andor .one .one .zero),
  (.p2wsh, .a (.pk_k compressedKey)),
  (.p2wsh, .s .zero),
  (.p2wsh, .c .zero),
  (.p2wsh, .d (.v signedB)),
  (.p2wsh, .v (.pk_k compressedKey)),
  (.p2wsh, .j .one),
  (.p2wsh, .n (.pk_k compressedKey)),
  (.p2wsh, .thresh 1 []),
  (.p2wsh, .multi 0 [compressedKey]),
  (.tapscript, .multi_a 2 [xOnlyKey])
]

example : rejectedTypingFixtures.all (fun fixture =>
    typingRejected fixture.1 fixture.2) = true := by
  native_decide

/-! ## Context-sensitive `d:` regressions -/

example : inferType .p2wsh dVerifyTrue =
    some ⟨.B, { o := true, n := true, d := true }⟩ := by
  native_decide

example : inferType .tapscript dVerifyTrue =
    some ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  native_decide

/-- P2WSH does not overstate `d:` as unit: every parent rule that requires a
    Bdu child rejects the context-weaker result. The matching Tapscript cases
    are checked with exact result types in `correctnessPropagationFixtures`. -/
private def p2wshDUnitParentRejections : List CoreFragment := [
  .or_c dVerifyTrue verifyTrue,
  .or_d dVerifyTrue .one,
  .andor dVerifyTrue .one .zero,
  .thresh 1 [dVerifyTrue]
]

example : p2wshDUnitParentRejections.all
    (fun fragment => (inferType .p2wsh fragment).isNone) = true := by
  native_decide

/-! ## Context validation remains a distinct checked boundary -/

private def checkedTypingRejected
    (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  match CheckedFragment.ofRaw? ctx fragment with
  | none => true
  | some _ => false

/-- Legacy multisig still has a local stack-shape type in Tapscript, but the
    checked boundary rejects it because the opcode is unavailable there. -/
example : inferType .tapscript (.multi 1 [xOnlyKey]) =
    some ⟨.B, { n := true, d := true, u := true }⟩ := by
  native_decide

example : checkedTypingRejected .tapscript (.multi 1 [xOnlyKey]) = true := by
  native_decide

/-- CHECKSIGADD multisig is rejected by the checked P2WSH boundary. -/
example : checkedTypingRejected .p2wsh (.multi_a 1 [compressedKey]) = true := by
  native_decide

end LeanMiniscript.Miniscript
