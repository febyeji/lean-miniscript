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

/-- The three BIP 379 properties together with the derived guarantee that the
    fragment can always be satisfied non-malleably. -/
structure MalleabilityModifiers where
  /-- s (signed): every satisfaction requires a signature. -/
  s : Bool := false
  /-- f (forced): every dissatisfaction requires a signature. -/
  f : Bool := false
  /-- e (expressive): there is a unique unconditional dissatisfaction and any
      conditional dissatisfaction requires a signature. -/
  e : Bool := false
  /-- The BIP 379 `Requires` column holds recursively for this fragment. This is
      kept separate from `s`, `f`, and `e` so a malleable fragment still has
      analyzable modifier properties. -/
  nonMalleable : Bool := false
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

/-- Every child is guaranteed to admit a non-malleable satisfaction. -/
def allNonMalleable : List MalleabilityModifiers → Bool
  | [] => true
  | mods :: rest => mods.nonMalleable && allNonMalleable rest

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
        HasMalleability ctx .zero { s := true, e := true, nonMalleable := true }
    | one :
        HasMalleability ctx .one { f := true, nonMalleable := true }
    | pk_k (key : PubKey) :
        HasMalleability ctx (.pk_k key) {
          s := true, e := true, nonMalleable := true
        }
    | pk_h (key : PubKey) :
        HasMalleability ctx (.pk_h key) {
          s := true, e := true, nonMalleable := true
        }
    | older (n : Nat) :
        HasMalleability ctx (.older n) { f := true, nonMalleable := true }
    | after (n : Nat) :
        HasMalleability ctx (.after n) { f := true, nonMalleable := true }
    | sha256 (hash : Hash256) :
        HasMalleability ctx (.sha256 hash) { nonMalleable := true }
    | hash256 (hash : Hash256) :
        HasMalleability ctx (.hash256 hash) { nonMalleable := true }
    | ripemd160 (hash : Hash160) :
        HasMalleability ctx (.ripemd160 hash) { nonMalleable := true }
    | hash160 (hash : Hash160) :
        HasMalleability ctx (.hash160 hash) { nonMalleable := true }
    | and_v {x y : CoreFragment} {mx my : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx (.and_v x y) {
          s := mx.s || my.s
          f := mx.s || my.f
          nonMalleable := mx.nonMalleable && my.nonMalleable
        }
    | and_b {x y : CoreFragment} {mx my : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx (.and_b x y) {
          s := mx.s || my.s
          f := (mx.f && my.f) || (mx.s && mx.f) || (my.s && my.f)
          e := mx.e && my.e && mx.s && my.s
          nonMalleable := mx.nonMalleable && my.nonMalleable
        }
    | or_b {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        HasMalleability ctx (.or_b x z) {
          s := mx.s && mz.s
          e := true
          nonMalleable :=
            mx.nonMalleable && mz.nonMalleable && mx.e && mz.e && (mx.s || mz.s)
        }
    | or_c {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        HasMalleability ctx (.or_c x z) {
          s := mx.s && mz.s
          f := true
          nonMalleable :=
            mx.nonMalleable && mz.nonMalleable && mx.e && (mx.s || mz.s)
        }
    | or_d {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        HasMalleability ctx (.or_d x z) {
          s := mx.s && mz.s
          f := mz.f
          e := mz.e
          nonMalleable :=
            mx.nonMalleable && mz.nonMalleable && mx.e && (mx.s || mz.s)
        }
    | or_i {x z : CoreFragment} {mx mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx z mz →
        HasMalleability ctx (.or_i x z) {
          s := mx.s && mz.s
          f := mx.f && mz.f
          e := (mx.e && mz.f) || (mz.e && mx.f)
          nonMalleable :=
            mx.nonMalleable && mz.nonMalleable && (mx.s || mz.s)
        }
    | andor {x y z : CoreFragment}
        {mx my mz : MalleabilityModifiers} :
        HasMalleability ctx x mx →
        HasMalleability ctx y my →
        HasMalleability ctx z mz →
        HasMalleability ctx (.andor x y z) {
          s := mz.s && (mx.s || my.s)
          f := mz.f && (mx.s || my.f)
          e := mz.e && (mx.s || my.f)
          nonMalleable := mx.nonMalleable && my.nonMalleable &&
            mz.nonMalleable && mx.e && (mx.s || my.s || mz.s)
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
          nonMalleable := mods.nonMalleable
        }
    | d {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.d x) {
          s := mods.s
          e := true
          nonMalleable := mods.nonMalleable
        }
    | v {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.v x) {
          s := mods.s
          f := true
          nonMalleable := mods.nonMalleable
        }
    | j {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.j x) {
          s := mods.s
          e := mods.f
          nonMalleable := mods.nonMalleable
        }
    | n {x : CoreFragment} {mods : MalleabilityModifiers} :
        HasMalleability ctx x mods →
        HasMalleability ctx (.n x) mods
    | thresh {k : Nat} {fragments : List CoreFragment}
        {mods : List MalleabilityModifiers} :
        HasMalleabilityList ctx fragments mods →
        HasMalleability ctx (.thresh k fragments) {
          s := MalleabilityModifiers.fewerThanNonS k mods
          e := MalleabilityModifiers.allS mods
          nonMalleable := MalleabilityModifiers.allNonMalleable mods &&
            MalleabilityModifiers.allE mods &&
            MalleabilityModifiers.atMostNonS k mods
        }
    | multi (k : Nat) (keys : List PubKey) :
        ctx.permitsLegacyMulti →
        HasMalleability ctx (.multi k keys) {
          s := true, e := true, nonMalleable := true
        }
    | multi_a (k : Nat) (keys : List PubKey) :
        ctx.permitsCheckSigAddMulti →
        HasMalleability ctx (.multi_a k keys) {
          s := true, e := true, nonMalleable := true
        }

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
    a unique modifier set in the requested script context. Failure of the
    non-malleability requirements is represented by `mods.nonMalleable = false`,
    not by absence of a derivation. -/
def malleabilityAnalyzable (ctx : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∃ mods, HasMalleability ctx fragment mods

end LeanMiniscript.Miniscript
