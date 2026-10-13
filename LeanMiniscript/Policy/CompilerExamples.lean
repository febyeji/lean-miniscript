import LeanMiniscript.Policy.Compiler
import LeanMiniscript.Miniscript.SatisfactionAvailability

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

private def hexA : String := "02" ++ String.ofList (List.replicate 64 'a')
private def hexB : String := "03" ++ String.ofList (List.replicate 64 'b')
private def hexC : String := "02" ++ String.ofList (List.replicate 64 'c')
private def hexH : String := String.ofList (List.replicate 64 'd')

/-- Compile policy text and print the Miniscript, or report the failure. -/
private def compiledText (ctx : ScriptContext) (input : String) : String :=
  match compilePolicyHex ctx input with
  | .ok sane => prettyCoreWith prettyPubKey sane.checked.fragment
  | .error (.parse _) => "parse error"
  | .error (.keyContext _) => "key context error"
  | .error (.sane error) => s!"not sane: {repr error}"

/-! ## Reference policies

These policies are the examples offered by the policy compiler page at
bitcoin.sipa.be/miniscript (single key, equal-odds keys, likely/unlikely keys,
two-factor with timeout, decaying 3-of-3, BOLT #3 `to_local`). That page
computes its outputs in the browser, so the expected Miniscripts below are
this compiler's results, pinned as regressions rather than cross-checked
fixtures. -/

example : compiledText .p2wsh s!"pk({hexA})" = s!"pk({hexA})" := by
  native_decide

example :
    compiledText .p2wsh s!"or(pk({hexA}),pk({hexB}))" =
      s!"or_b(pk({hexA}),s:pk({hexB}))" := by
  native_decide

example :
    compiledText .p2wsh s!"or(99@pk({hexA}),pk({hexB}))" =
      s!"or_d(pk({hexA}),pkh({hexB}))" := by
  native_decide

example :
    compiledText .p2wsh s!"and(pk({hexA}),or(99@pk({hexB}),older(12960)))" =
      s!"and_v(v:pk({hexA}),or_d(pk({hexB}),older(12960)))" := by
  native_decide

example :
    compiledText .p2wsh
        s!"thresh(3,pk({hexA}),pk({hexB}),pk({hexC}),older(12960))" =
      s!"thresh(3,pk({hexA}),s:pk({hexB}),s:pk({hexC}),sln:older(12960))" := by
  native_decide

/-- The BOLT #3 `to_local` policy. `andor(pk(local),older(1008),pk(revocation))`
    has the same script size and expected witness size as this result, but
    this compiler does not generate `andor` from `or(X,and(Y,Z))`.
    TODO(policy-andor): add `andor` candidates for disjunctions of
    conjunctions. -/
example :
    compiledText .p2wsh s!"or(pk({hexA}),and(pk({hexB}),older(1008)))" =
      s!"or_d(pk({hexA}),and_v(v:pk({hexB}),older(1008)))" := by
  native_decide

/-! ## Regression outputs of this compiler -/

example :
    compiledText .p2wsh s!"and(pk({hexA}),pk({hexB}))" =
      s!"and_v(v:pk({hexA}),pk({hexB}))" := by
  native_decide

/-- Key-only thresholds become `multi` in P2WSH. -/
example :
    compiledText .p2wsh s!"thresh(2,pk({hexA}),pk({hexB}),pk({hexC}))" =
      s!"multi(2,{hexA},{hexB},{hexC})" := by
  native_decide

example :
    compiledText .p2wsh s!"thresh(2,pk({hexA}),pk({hexB}),after(100))" =
      s!"thresh(2,pk({hexA}),s:pk({hexB}),sln:after(100))" := by
  native_decide

/-! ## Tapscript -/

private def xOnly (hex : String) : String := String.ofList (hex.toList.drop 2)

/-- Compressed keys are normalized to x-only keys and key-only thresholds
    become `multi_a`. -/
example :
    compiledText .tapscript s!"thresh(2,pk({hexA}),pk({hexB}),pk({hexC}))" =
      s!"multi_a(2,{xOnly hexA},{xOnly hexB},{xOnly hexC})" := by
  native_decide

example :
    compiledText .tapscript s!"and(pk({hexA}),or(99@pk({hexB}),older(12960)))" =
      s!"and_v(v:pk({xOnly hexA}),or_d(pk({xOnly hexB}),older(12960)))" := by
  native_decide

/-! ## Rejected policies -/

/-- A policy without a signature on every path is not sane. -/
example :
    compiledText .p2wsh "after(100)" =
      "not sane: LeanMiniscript.Miniscript.SaneError.signatureNotRequired" := by
  native_decide

/-- Repeated keys violate the non-malleability analysis assumption. -/
example :
    compiledText .p2wsh s!"or(pk({hexA}),pk({hexA}))" =
      "not sane: LeanMiniscript.Miniscript.SaneError.duplicateKeys" := by
  native_decide

/-- Every disjunction needs a signed branch for non-malleability. -/
example :
    compiledText .p2wsh s!"and(pk({hexA}),or(sha256({hexH}),after(100)))" =
      "not sane: LeanMiniscript.Miniscript.SaneError.malleable" := by
  native_decide

/-! ## Property checks

`CompilerProofs` proves meaning preservation for every policy. The checks
below exercise the executable compiler on a small corpus: every policy
compiles to a valid Miniscript, the structural translation type-checks, and
structural satisfiability agrees with the policy on every material over the
corpus atoms. -/

private def keyOf (hex : String) : PubKey :=
  match resolveHexKey hex with
  | .ok key => key
  | .error _ => PubKey.ofBytes ByteArray.empty

private def hashH : Hash256 :=
  match SurfaceParser.decodeHex? hexH with
  | some bytes => Hash256.ofBytes bytes
  | none => Hash256.ofBytes ByteArray.empty

private def corpus : List Policy :=
  let a := Policy.key (keyOf hexA)
  let b := Policy.key (keyOf hexB)
  let c := Policy.key (keyOf hexC)
  [ a,
    .or' a b,
    .or 99 a 1 b,
    .and a b,
    .and a (.or 99 b 1 (.older 12960)),
    .thresh 3 [a, b, c, .older 12960],
    .thresh 2 [a, b, c],
    .thresh 2 [a, .and b (.sha256 hashH), .or' c (.after 100)],
    .or' a (.and b (.older 1008)),
    .or 3 (.and a b) 1 (.or' (.and c (.older 144)) (.and (.sha256 hashH) a)),
    .and (.or' a .unsatisfiable) (.or' b .trivial),
    .thresh 1 [.sha256 hashH, .after 100, a] ]

/-- All materials over the corpus atoms. -/
private def materials : List Material := Id.run do
  let mut result := []
  for bits in List.range 64 do
    let bit (i : Nat) : Bool := (bits / 2 ^ i) % 2 == 1
    result := {
      signs := fun key =>
        (key == keyOf hexA && bit 0) || (key == keyOf hexB && bit 1) ||
          (key == keyOf hexC && bit 2)
      preimage := fun _ => bit 3
      after := fun _ => bit 4
      older := fun _ => bit 5 } :: result
  return result

private def agreesEverywhere (policy : Policy) (fragment : CoreFragment) : Bool :=
  materials.all fun material =>
    fragment.isSatisfiableWith material.atom == policy.eval material

private def checkedAgrees (ctx : ScriptContext) (policy : Policy) : Bool :=
  match compilePolicyChecked ctx policy with
  | some checked => agreesEverywhere policy checked.fragment
  | none => false

private def structuralTypes (ctx : ScriptContext) (policy : Policy) : Bool :=
  (CheckedFragment.ofRaw? ctx policy.toMiniscript).isSome &&
    agreesEverywhere policy policy.toMiniscript

example : corpus.all (checkedAgrees .p2wsh) = true := by native_decide

example : corpus.all (structuralTypes .p2wsh) = true := by native_decide

example :
    (corpus.filterMap (·.normalizeKeys .tapscript)).all
      (checkedAgrees .tapscript) = true := by
  native_decide

/-- Sane compilations also agree with the policy. -/
example :
    corpus.all (fun policy =>
      match compilePolicy .p2wsh policy with
      | .ok sane => agreesEverywhere policy sane.checked.fragment
      | .error _ => true) = true := by
  native_decide

/-- Nine of the twelve corpus policies have a sane compilation. -/
example :
    (corpus.filter (fun policy =>
      match compilePolicy .p2wsh policy with
      | .ok _ => true
      | .error _ => false)).length = 9 := by
  native_decide

/-! ## Satisfier-level behaviour -/

private def signatureOnlyFrom (key : PubKey) : SatEnv where
  signatureFor := fun candidate => if candidate == key then some trueElement else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => ⟨(List.replicate 32 34).toArray⟩
  txCtx := { version := 2, locktime := 100, sequence := 50, sigHash := ⟨#[]⟩ }

private def satisfiesWith (ctx : ScriptContext) (input : String) (env : SatEnv) :
    Bool :=
  match compilePolicyHex ctx input with
  | .ok sane => (satisfyFinal sane.checked.fragment env).isSome
  | .error _ => false

/-- Either signer can spend `or(pk(A),pk(B))`; a signature for a third key
    cannot. -/
example :
    satisfiesWith .p2wsh s!"or(pk({hexA}),pk({hexB}))"
        (signatureOnlyFrom (keyOf hexA)) = true ∧
      satisfiesWith .p2wsh s!"or(pk({hexA}),pk({hexB}))"
        (signatureOnlyFrom (keyOf hexB)) = true ∧
      satisfiesWith .p2wsh s!"or(pk({hexA}),pk({hexB}))"
        (signatureOnlyFrom (keyOf hexC)) = false := by
  native_decide

/-- `and(pk(A),pk(B))` needs both signatures. -/
example :
    satisfiesWith .p2wsh s!"and(pk({hexA}),pk({hexB}))"
      (signatureOnlyFrom (keyOf hexA)) = false := by
  native_decide

end LeanMiniscript.Policy
