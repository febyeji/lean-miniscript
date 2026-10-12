import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Script.CryptoOracle

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

mutual
/-- Two compiler hash resolvers agree on precisely the `pk_h` leaves whose
digests are embedded in this fragment's script. Other key forms need no hash
agreement. -/
def CoreFragment.KeyHashAgreement (left right : PubKey → Hash160) : CoreFragment → Prop
  | .pk_h key => left key = right key
  | .and_v x y | .and_b x y | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
      x.KeyHashAgreement left right ∧ y.KeyHashAgreement left right
  | .andor x y z =>
      x.KeyHashAgreement left right ∧ y.KeyHashAgreement left right ∧ z.KeyHashAgreement left right
  | .a x | .s x | .c x | .d x | .v x | .j x | .n x => x.KeyHashAgreement left right
  | .thresh _ fragments => CoreFragment.KeyHashAgreementList left right fragments
  | _ => True

/-- Hash agreement for threshold children in source order. -/
def CoreFragment.KeyHashAgreementList (left right : PubKey → Hash160) : List CoreFragment → Prop
  | [] => True
  | first :: rest => first.KeyHashAgreement left right ∧ KeyHashAgreementList left right rest
end

mutual
/-- Agreement at embedded key hashes preserves the complete compiled script,
including verification folding and threshold tails. -/
theorem compileWithKeyHash_eq_of_agreement
    {left right : PubKey → Hash160} (fragment : CoreFragment)
    (agreement : fragment.KeyHashAgreement left right) :
    compileWithKeyHash left fragment = compileWithKeyHash right fragment := by
  cases fragment with
  | pk_h key =>
      change left key = right key at agreement
      simp only [compileWithKeyHash, agreement]
  | and_v x y | and_b x y | or_b x y | or_c x y | or_d x y | or_i x y =>
      simp only [compileWithKeyHash, compileWithKeyHash_eq_of_agreement x agreement.1,
        compileWithKeyHash_eq_of_agreement y agreement.2]
  | andor x y z =>
      simp only [compileWithKeyHash, compileWithKeyHash_eq_of_agreement x agreement.1,
        compileWithKeyHash_eq_of_agreement y agreement.2.1,
        compileWithKeyHash_eq_of_agreement z agreement.2.2]
  | a x | s x | c x | d x | v x | j x | n x =>
      simp only [compileWithKeyHash, compileWithKeyHash_eq_of_agreement x agreement]
  | thresh k fragments =>
      simp only [compileWithKeyHash, compileThreshWithKeyHash_eq_of_agreement fragments agreement]
  | zero | one | pk_k | older | after | sha256 | hash256 | ripemd160 | hash160 | multi | multi_a => rfl

theorem compileThreshWithKeyHash_eq_of_agreement
    {left right : PubKey → Hash160} (fragments : List CoreFragment)
    (agreement : CoreFragment.KeyHashAgreementList left right fragments) :
    compileThreshWithKeyHash left fragments = compileThreshWithKeyHash right fragments := by
  cases fragments with
  | nil => rfl
  | cons first rest =>
      simp only [compileThreshWithKeyHash, compileWithKeyHash_eq_of_agreement first agreement.1,
        compileThreshTailWithKeyHash_eq_of_agreement rest agreement.2]

theorem compileThreshTailWithKeyHash_eq_of_agreement
    {left right : PubKey → Hash160} (fragments : List CoreFragment)
    (agreement : CoreFragment.KeyHashAgreementList left right fragments) :
    compileThreshTailWithKeyHash left fragments = compileThreshTailWithKeyHash right fragments := by
  cases fragments with
  | nil => rfl
  | cons first rest =>
      simp only [compileThreshTailWithKeyHash, compileWithKeyHash_eq_of_agreement first agreement.1,
        compileThreshTailWithKeyHash_eq_of_agreement rest agreement.2]
end

/-- Concrete and modeled compilers agree under the explicit HASH160 boundary
for the fragment's `pk_h` leaves. -/
theorem compileConcrete_eq_compile {fragment : CoreFragment}
    (agreement : fragment.KeyHashAgreement concreteKeyHash modelKeyHash) :
    compileConcrete fragment = compile fragment :=
  compileWithKeyHash_eq_of_agreement fragment agreement

/-- With concrete hashes, the existing oracle-refinement contract already
implies compiler agreement for every fragment. -/
theorem compileConcrete_eq_compile_of_refines
    {verifySignature verifySchnorrSignature : StackElement → StackElement → ByteArray → Bool}
    (agreement : (CryptoOracle.pureLeanHashes verifySignature verifySchnorrSignature).RefinesModel)
    (fragment : CoreFragment) : compileConcrete fragment = compile fragment := by
  have hashes : concreteKeyHash = modelKeyHash := by
    funext key
    exact congrArg Hash160.ofBytes (agreement.2.2.2.1 key.bytes)
  change compileWithKeyHash concreteKeyHash fragment = compileWithKeyHash modelKeyHash fragment
  rw [hashes]

end LeanMiniscript.Miniscript
