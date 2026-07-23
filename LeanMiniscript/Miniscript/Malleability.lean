import LeanMiniscript.Miniscript.Context

namespace LeanMiniscript.Miniscript

/-!
# BIP 379 malleability typing

This module keeps the `s`, `f`, and `e` malleability properties separate from
the correctness type in `Types.lean`. The rules are transcribed from BIP 379 at
`bitcoin/bips@442e9628b3dcca1b65f0df8af2308f8260e00caa` and cross-checked
against `rust-miniscript@cb8262253af383a1a5b17363f6a013848f20534b`.

The context parameter records the BIP 379 split between legacy `multi` in
P2WSH and `multi_a` in Tapscript. Structural validity, correctness typing, and
timelock compatibility remain separate analyses.
-/

/-- The three BIP 379 properties used by the malleability analysis. -/
structure MalleabilityModifiers where
  /-- s (signed): every satisfaction requires a signature. -/
  s : Bool := false
  /-- f (forced): every dissatisfaction requires a signature. -/
  f : Bool := false
  /-- e (expressive): there is a unique unconditional dissatisfaction and any
      conditional dissatisfaction requires a signature. -/
  e : Bool := false
  deriving Repr, DecidableEq, BEq

namespace MalleabilityModifiers

/-- Every child has the expressive property. -/
def allE : List MalleabilityModifiers → Bool
  | [] => true
  | mods :: rest => mods.e && allE rest

/-- Every child has the signed property. -/
def allS : List MalleabilityModifiers → Bool
  | [] => true
  | mods :: rest => mods.s && allS rest

/-- Number of children whose satisfactions are not guaranteed to be signed. -/
def countNonS : List MalleabilityModifiers → Nat
  | [] => 0
  | mods :: rest => (if mods.s = true then 0 else 1) + countNonS rest

/-- The BIP 379 threshold requirement that at most `k` children are non-signed. -/
def atMostNonS (k : Nat) (mods : List MalleabilityModifiers) : Bool :=
  decide (countNonS mods ≤ k)

/-- A threshold is signed when at most `k - 1` children are non-signed. -/
def fewerThanNonS (k : Nat) (mods : List MalleabilityModifiers) : Bool :=
  decide (countNonS mods < k)

end MalleabilityModifiers

mutual
  /-- Relational BIP 379 malleability judgment for one core fragment. -/
  inductive HasMalleability (ctx : ScriptContext) :
      CoreFragment → MalleabilityModifiers → Prop where
    | zero :
        HasMalleability ctx .zero { s := true, e := true }
    | one :
        HasMalleability ctx .one { f := true }
    | pk_k (key : PubKey) :
        HasMalleability ctx (.pk_k key) { s := true, e := true }
    | pk_h (key : PubKey) :
        HasMalleability ctx (.pk_h key) { s := true, e := true }
    | older (n : Nat) :
        HasMalleability ctx (.older n) { f := true }
    | after (n : Nat) :
        HasMalleability ctx (.after n) { f := true }
    | sha256 (hash : Hash256) :
        HasMalleability ctx (.sha256 hash) {}
    | hash256 (hash : Hash256) :
        HasMalleability ctx (.hash256 hash) {}
    | ripemd160 (hash : Hash160) :
        HasMalleability ctx (.ripemd160 hash) {}
    | hash160 (hash : Hash160) :
        HasMalleability ctx (.hash160 hash) {}
    | and_v {x y : CoreFragment} {mx my : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx (.and_v x y) {
          s := mx.s || my.s
          f := mx.s || my.f
        }
    | and_b {x y : CoreFragment} {mx my : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx (.and_b x y) {
          s := mx.s || my.s
          f := (mx.f && my.f) || (mx.s && mx.f) || (my.s && my.f)
          e := mx.e && my.e && mx.s && my.s
        }
    | or_b {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        mx.e = true →
        mz.e = true →
        (mx.s || mz.s) = true →
        HasMalleability ctx (.or_b x z) {
          s := mx.s && mz.s
          e := true
        }
    | or_c {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        mx.e = true →
        (mx.s || mz.s) = true →
        HasMalleability ctx (.or_c x z) {
          s := mx.s && mz.s
          f := true
        }
    | or_d {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        mx.e = true →
        (mx.s || mz.s) = true →
        HasMalleability ctx (.or_d x z) {
          s := mx.s && mz.s
          f := mz.f
          e := mz.e
        }
    | or_i {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        (mx.s || mz.s) = true →
        HasMalleability ctx (.or_i x z) {
          s := mx.s && mz.s
          f := mx.f && mz.f
          e := (mx.e && mz.f) || (mz.e && mx.f)
        }
    | andor {x y z : CoreFragment}
        {mx my mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx z mz →
        mx.e = true →
        (mx.s || my.s || mz.s) = true →
        HasMalleability ctx (.andor x y z) {
          s := mz.s && (mx.s || my.s)
          f := mz.f && (mx.s || my.f)
          e := mz.e && (mx.s || my.f)
        }
    | a {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.a x) mods
    | s {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.s x) mods
    | c {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.c x) {
          s := true
          f := mods.f
          e := mods.e
        }
    | d {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.d x) {
          s := mods.s
          e := true
        }
    | v {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.v x) {
          s := mods.s
          f := true
        }
    | j {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.j x) {
          s := mods.s
          e := mods.f
        }
    | n {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.n x) mods
    | thresh {k : Nat} {fragments : List CoreFragment}
        {mods : List MalleabilityModifiers} :
        HasMalleabilityList ctx fragments mods →
        MalleabilityModifiers.allE mods = true →
        MalleabilityModifiers.atMostNonS k mods = true →
        HasMalleability ctx (.thresh k fragments) {
          s := MalleabilityModifiers.fewerThanNonS k mods
          e := MalleabilityModifiers.allS mods
        }
    | multi (k : Nat) (keys : List PubKey) :
        ctx.permitsLegacyMulti →
        HasMalleability ctx (.multi k keys) { s := true, e := true }
    | multi_a (k : Nat) (keys : List PubKey) :
        ctx.permitsCheckSigAddMulti →
        HasMalleability ctx (.multi_a k keys) { s := true, e := true }

  /-- Pointwise malleability derivations for threshold children. -/
  inductive HasMalleabilityList (ctx : ScriptContext) :
      List CoreFragment → List MalleabilityModifiers → Prop where
    | nil : HasMalleabilityList ctx [] []
    | cons {fragment : CoreFragment} {mods : MalleabilityModifiers}
        {fragments : List CoreFragment} {rest : List MalleabilityModifiers} :
        HasMalleability ctx fragment mods →
        HasMalleabilityList ctx fragments rest →
        HasMalleabilityList ctx (fragment :: fragments) (mods :: rest)
end

/-- A fragment is malleability-analyzable when the BIP 379 judgment assigns it
    a unique modifier set in the requested script context. -/
def malleabilityAnalyzable (ctx : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∃ mods, HasMalleability ctx fragment mods

end LeanMiniscript.Miniscript
