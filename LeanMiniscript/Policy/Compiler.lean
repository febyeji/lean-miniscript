import LeanMiniscript.Policy.Semantics
import LeanMiniscript.Policy.Text
import LeanMiniscript.Miniscript.Sane

/-!
# Policy compiler

Two compilers translate a `Policy` into Core Miniscript for a P2WSH or
Tapscript context.

* `Policy.toMiniscript` is a deterministic structural translation. Every
  policy node becomes a `Bdu` fragment (`0`, `or_i(1,0)`, `pk`, `ndv:after`,
  `ndv:older`, hashlocks, `and_b(X,a:Y)`, `or_d(X,Y)`, and
  `thresh(k,X1,a:X2,...)`), so the output type-checks for every well-formed
  policy. It favours uniformity over size.
* `compilePolicy` is a cost-based compiler in the spirit of rust-miniscript's
  `policy::compiler`. Each policy node yields candidate fragments built from
  its children's candidates with the BIP 379 connectives, closed under the
  wrappers `a s c d v j n t l u`. Candidates are typed with `inferType`,
  malleable candidates are dropped, and for each type and malleability class
  only the cheapest candidate under the node's satisfaction and
  dissatisfaction probabilities survives. Branch weights from `N@` set those
  probabilities. The cheapest top-level candidate that passes `checkSane` is
  returned, falling back to the structural translation.

The cost model counts serialized script bytes plus expected witness bytes,
following the satisfaction and dissatisfaction size table that
rust-miniscript uses. It only steers selection: `CompilerProofs` shows that
every candidate, and hence every result, has the policy's meaning regardless
of cost.
-/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript

/-! ## Structural translation -/

namespace Policy

mutual
  /-- Deterministic structural translation into `Bdu` Core Miniscript. -/
  def toMiniscript : Policy → CoreFragment
    | .unsatisfiable => .zero
    | .trivial => .or_i .one .zero
    | .key pubKey => .c (.pk_k pubKey)
    | .after n => .n (.d (.v (.after n)))
    | .older n => .n (.d (.v (.older n)))
    | .sha256 hash => .sha256 hash
    | .hash256 hash => .hash256 hash
    | .ripemd160 hash => .ripemd160 hash
    | .hash160 hash => .hash160 hash
    | .and left right => .and_b (toMiniscript left) (.a (toMiniscript right))
    | .or _ left _ right => .or_d (toMiniscript left) (toMiniscript right)
    | .thresh k subs => .thresh k (toMiniscriptList subs)

  /-- Threshold children: the first is `Bdu`, the rest are `a:`-wrapped `Wdu`. -/
  def toMiniscriptList : List Policy → List CoreFragment
    | [] => []
    | sub :: subs => toMiniscript sub :: toMiniscriptTail subs

  /-- Remaining threshold children, each wrapped with `a:`. -/
  def toMiniscriptTail : List Policy → List CoreFragment
    | [] => []
    | sub :: subs => .a (toMiniscript sub) :: toMiniscriptTail subs
end

end Policy

/-! ## Cost-based compilation -/

/-- Cost standing in for an impossible satisfaction or dissatisfaction. -/
def infiniteCost : Float := 1.0e18

/-- Witness bytes for one signature, including its length prefix. -/
def signatureCost : ScriptContext → Float
  | .p2wsh => 73
  | .tapscript => 66

/-- Witness bytes for one revealed public key, including its length prefix. -/
def keyRevealCost : ScriptContext → Float
  | .p2wsh => 34
  | .tapscript => 33

/-- Add two optional dissatisfaction costs. -/
def addCost : Option Float → Option Float → Option Float
  | some x, some y => some (x + y)
  | _, _ => none

/-- Cheaper of two optional costs. -/
def minCost : Option Float → Option Float → Option Float
  | some x, some y => some (if x ≤ y then x else y)
  | some x, none => some x
  | none, y => y

/-- A fragment shape with its expected satisfaction cost and dissatisfaction
    cost in witness bytes. -/
structure Template where
  fragment : CoreFragment
  sat : Float
  dsat : Option Float

/-- A typed compilation candidate with its cost summary. -/
structure Candidate where
  fragment : CoreFragment
  ty : MiniType
  malleability : Option MalleabilityModifiers
  size : Nat
  sat : Float
  dsat : Option Float
  /-- Generation order among equally cheap candidates: earlier templates, in
      particular those keeping the policy's branch order, win ties. -/
  order : Nat := 0

namespace Candidate

/-- Grouping key: candidates with equal types and malleability properties are
    interchangeable for every parent, so only the cheapest is kept. -/
def key (candidate : Candidate) : MiniType × Option MalleabilityModifiers :=
  (candidate.ty, candidate.malleability)

/-- Expected cost when satisfied with probability `satProb` and dissatisfied
    with probability `dsatProb`. Candidates without a dissatisfaction are only
    compared with each other, because the grouping key records the `d`
    property, so their missing dissatisfaction contributes nothing. -/
def score (satProb dsatProb : Float) (candidate : Candidate) : Float :=
  candidate.size.toFloat + satProb * candidate.sat +
    (match candidate.dsat with
      | some cost => dsatProb * cost
      | none => 0)

end Candidate

/-- Type a template. Untyped fragments and fragments known to be malleable
    are discarded; malleability is preserved by every connective. -/
def realizeTemplate (ctx : ScriptContext) (template : Template) :
    Option Candidate :=
  match inferType ctx template.fragment with
  | none => none
  | some ty =>
      let malleability := inferMalleability ctx template.fragment
      match malleability with
      | some mods =>
          if mods.nonMalleable then
            some {
              fragment := template.fragment
              ty
              malleability
              size := (Properties.resourceSerializedScriptSize
                template.fragment).toOption.getD 1000000
              sat := template.sat
              dsat := template.dsat }
          else none
      | none =>
          some {
            fragment := template.fragment
            ty
            malleability
            size := (Properties.resourceSerializedScriptSize
              template.fragment).toOption.getD 1000000
            sat := template.sat
            dsat := template.dsat }

/-- Type templates, numbering them from `index` in generation order. -/
def realizeFrom (ctx : ScriptContext) : Nat → List Template → List Candidate
  | _, [] => []
  | index, template :: templates =>
      match realizeTemplate ctx template with
      | some candidate =>
          { candidate with order := index } :: realizeFrom ctx (index + 1) templates
      | none => realizeFrom ctx (index + 1) templates

/-- Type a list of templates in generation order. -/
def realize (ctx : ScriptContext) (templates : List Template) : List Candidate :=
  realizeFrom ctx 0 templates

/-- Whether `candidate` should replace `other`: strictly cheaper, or equally
    cheap and generated earlier. -/
def Candidate.better (satProb dsatProb : Float) (candidate other : Candidate) :
    Bool :=
  candidate.score satProb dsatProb < other.score satProb dsatProb ||
    (candidate.score satProb dsatProb == other.score satProb dsatProb &&
      candidate.order < other.order)

/-- Insert a candidate, replacing in place a worse candidate with the same
    key. -/
def insertCheapest (satProb dsatProb : Float) (kept : List Candidate)
    (candidate : Candidate) : List Candidate :=
  match kept.find? (fun other => other.key == candidate.key) with
  | none => kept ++ [candidate]
  | some other =>
      if candidate.better satProb dsatProb other then
        kept.map (fun kept => if kept.key == candidate.key then candidate else kept)
      else kept

/-- Keep the cheapest candidate of each type and malleability class. -/
def prune (satProb dsatProb : Float) (candidates : List Candidate) :
    List Candidate :=
  candidates.foldl (insertCheapest satProb dsatProb) []

/-- The BIP 379 wrappers, including the `t`, `l`, and `u` sugar. -/
def wrapTemplates (candidate : Candidate) : List Template :=
  let x := candidate.fragment
  let s := candidate.sat
  let d := candidate.dsat
  [ ⟨.a x, s, d⟩, ⟨.s x, s, d⟩, ⟨.c x, s, d⟩, ⟨.d x, s + 2, some 1⟩,
    ⟨.v x, s, none⟩, ⟨.j x, s, some 1⟩, ⟨.n x, s, d⟩,
    ⟨.and_v x .one, s, none⟩, ⟨.or_i .zero x, s + 1, some 2⟩,
    ⟨.or_i x .zero, s + 2, some 1⟩ ]

/-- Wrapped candidates rank after every unwrapped candidate of equal cost, so
    `and_v(v:pk(A),pk(B))` is preferred to the script-identical
    `c:and_v(v:pk(A),pk_k(B))`. -/
def wrappedOrderOffset : Nat := 1000000

/-- One wrapper-closure round followed by pruning. -/
def closeOnce (ctx : ScriptContext) (satProb dsatProb : Float)
    (candidates : List Candidate) : List Candidate :=
  prune satProb dsatProb
    (candidates ++ candidates.flatMap (fun x =>
      (realize ctx (wrapTemplates x)).map (fun wrapped =>
        { wrapped with order := x.order + wrappedOrderOffset })))

/-- Bounded wrapper closure. Three rounds reach every useful wrapper chain of
    length three, such as `s:n:l:` or `n:d:v:`. -/
def closeWrappers (ctx : ScriptContext) (satProb dsatProb : Float)
    (candidates : List Candidate) : List Candidate :=
  closeOnce ctx satProb dsatProb
    (closeOnce ctx satProb dsatProb
      (closeOnce ctx satProb dsatProb (prune satProb dsatProb candidates)))

/-- Leaf templates for atomic policies. -/
def leafTemplates (ctx : ScriptContext) : Policy → List Template
  | .unsatisfiable => [⟨.zero, infiniteCost, some 0⟩]
  | .trivial => [⟨.one, 0, none⟩]
  | .key pubKey =>
      [⟨.pk_k pubKey, signatureCost ctx, some 1⟩,
        ⟨.pk_h pubKey, signatureCost ctx + keyRevealCost ctx,
          some (1 + keyRevealCost ctx)⟩]
  | .after n => [⟨.after n, 0, none⟩]
  | .older n => [⟨.older n, 0, none⟩]
  | .sha256 hash => [⟨.sha256 hash, 33, some 33⟩]
  | .hash256 hash => [⟨.hash256 hash, 33, some 33⟩]
  | .ripemd160 hash => [⟨.ripemd160 hash, 33, some 33⟩]
  | .hash160 hash => [⟨.hash160 hash, 33, some 33⟩]
  | _ => []

/-- Conjunction templates with `x` executed first. -/
def andTemplates (x y : Candidate) : List Template :=
  let s := x.sat + y.sat
  [ ⟨.and_v x.fragment y.fragment, s, none⟩,
    ⟨.and_b x.fragment y.fragment, s, addCost x.dsat y.dsat⟩,
    ⟨.andor x.fragment y.fragment .zero, s, addCost x.dsat (some 0)⟩ ]

/-- Disjunction templates with `x` executed first, where `x` is taken with
    probability `px` and `z` with probability `pz`. -/
def orTemplates (x z : Candidate) (px pz : Float) : List Template :=
  let xd := x.dsat.getD infiniteCost
  let zd := z.dsat.getD infiniteCost
  [ ⟨.or_b x.fragment z.fragment, px * (x.sat + zd) + pz * (xd + z.sat),
      addCost x.dsat z.dsat⟩,
    ⟨.or_d x.fragment z.fragment, px * x.sat + pz * (xd + z.sat),
      addCost x.dsat z.dsat⟩,
    ⟨.or_c x.fragment z.fragment, px * x.sat + pz * (xd + z.sat), none⟩,
    ⟨.or_i x.fragment z.fragment, px * (2 + x.sat) + pz * (1 + z.sat),
      minCost (x.dsat.map (· + 2)) (z.dsat.map (· + 1))⟩ ]

/-- A direct `andor(x,y,z)` candidate for the common policy shape
`or(x,and(y,z))`. It evaluates the left branch once and preserves the
policy's branch semantics while avoiding the selector overhead of `or_d`. -/
def andorTemplates (x y z : Candidate) : List Template :=
  [⟨.andor z.fragment y.fragment x.fragment,
    min (z.sat + y.sat) (z.dsat.getD infiniteCost + x.sat),
    minCost (addCost z.dsat x.dsat) (addCost (some z.sat) y.dsat)⟩]

def directAndorTemplates (right : Policy) (lefts middles tails : List Candidate) : List Template :=
  match right with
  | .and _ _ =>
      lefts.flatMap fun x =>
        middles.flatMap fun y => tails.flatMap fun z => andorTemplates x y z
  | _ => []

/-- Pick the cheapest candidate satisfying a predicate. -/
def pickBest (satProb dsatProb : Float) (predicate : Candidate → Bool) :
    List Candidate → Option Candidate
  | [] => none
  | candidate :: candidates =>
      match pickBest satProb dsatProb predicate candidates with
      | none => if predicate candidate then some candidate else none
      | some best =>
          if predicate candidate &&
              candidate.score satProb dsatProb ≤ best.score satProb dsatProb then
            some candidate
          else some best

/-- Whether a candidate is `Bdu`, as required of the first threshold child. -/
def isBdu (candidate : Candidate) : Bool :=
  candidate.ty.base == .B && candidate.ty.mods.d && candidate.ty.mods.u

/-- Whether a candidate is `Wdu`, as required of later threshold children. -/
def isWdu (candidate : Candidate) : Bool :=
  candidate.ty.base == .W && candidate.ty.mods.d && candidate.ty.mods.u

/-- Choose the cheapest `Wdu` candidate for each later threshold child. -/
def chooseThreshTail (satProb dsatProb : Float) :
    List (List Candidate) → Option (List Candidate)
  | [] => some []
  | choices :: rest => do
      let best ← pickBest satProb dsatProb isWdu choices
      let tail ← chooseThreshTail satProb dsatProb rest
      pure (best :: tail)

/-- Choose a `Bdu` first child and `Wdu` later children. -/
def chooseThreshChildren (satProb dsatProb : Float) :
    List (List Candidate) → Option (List Candidate)
  | [] => none
  | choices :: rest => do
      let first ← pickBest satProb dsatProb isBdu choices
      let tail ← chooseThreshTail satProb dsatProb rest
      pure (first :: tail)

/-- Expected satisfaction cost of `thresh(k, ...)`: every child is
    dissatisfied except the `k` children cheapest to satisfy instead. -/
def threshSatCost (k : Nat) (children : List Candidate) : Float :=
  let dsats := children.map (fun child => child.dsat.getD infiniteCost)
  let deltas := children.map (fun child =>
    child.sat - child.dsat.getD infiniteCost)
  let sorted := deltas.mergeSort (fun a b => a ≤ b)
  dsats.foldl (· + ·) 0 + (sorted.take k).foldl (· + ·) 0

/-- Dissatisfaction cost of `thresh(k, ...)`. -/
def threshDsatCost (children : List Candidate) : Option Float :=
  children.foldl (fun total child => addCost total child.dsat) (some 0)

/-- Keys of a threshold whose branches are all `pk(...)`. -/
def allKeys : List Policy → Option (List PubKey)
  | [] => some []
  | .key pubKey :: subs => (allKeys subs).map (pubKey :: ·)
  | _ :: _ => none

/-- Multisignature templates for a key-only threshold. -/
def multiTemplates (ctx : ScriptContext) (k : Nat) (subs : List Policy) :
    List Template :=
  match allKeys subs with
  | none => []
  | some keys =>
      let n := keys.length
      match ctx with
      | .p2wsh =>
          [⟨.multi k keys, 1 + k.toFloat * signatureCost ctx,
            some (k.toFloat + 1)⟩]
      | .tapscript =>
          [⟨.multi_a k keys,
            k.toFloat * signatureCost ctx + (n - k).toFloat,
            some n.toFloat⟩]

/-- Threshold templates from per-child candidate lists. -/
def threshTemplates (satProb dsatProb : Float) (k : Nat)
    (childCandidates : List (List Candidate)) : List Template :=
  match chooseThreshChildren satProb dsatProb childCandidates with
  | none => []
  | some children =>
      [⟨.thresh k (children.map Candidate.fragment), threshSatCost k children,
        threshDsatCost children⟩]

/-- Branch probabilities from `N@` weights. -/
def branchWeights (leftWeight rightWeight : Nat) : Float × Float :=
  if leftWeight + rightWeight = 0 then (0.5, 0.5)
  else
    let total := (leftWeight + rightWeight).toFloat
    (leftWeight.toFloat / total, rightWeight.toFloat / total)

mutual
  /-- Pruned compilation candidates for a policy node satisfied with
      probability `satProb` and dissatisfied with probability `dsatProb`. -/
  def compileCandidates (ctx : ScriptContext) :
      Policy → Float → Float → List Candidate
    | .and left right, satProb, dsatProb =>
        let lefts := compileCandidates ctx left satProb dsatProb
        let rights := compileCandidates ctx right satProb dsatProb
        closeWrappers ctx satProb dsatProb
          (realize ctx
            ((lefts.flatMap fun x => rights.flatMap fun y => andTemplates x y) ++
              (rights.flatMap fun y => lefts.flatMap fun x => andTemplates y x)))
    | .or leftWeight left rightWeight right, satProb, dsatProb =>
        let (px, pz) := branchWeights leftWeight rightWeight
        let lefts := compileCandidates ctx left (satProb * px)
          (dsatProb + satProb * pz)
        let rights := compileCandidates ctx right (satProb * pz)
          (dsatProb + satProb * px)
        let middles := match right with
          | .and middle _ => compileCandidates ctx middle (satProb * pz) dsatProb
          | _ => []
        let tails := match right with
          | .and _ tail => compileCandidates ctx tail (satProb * pz) dsatProb
          | _ => []
        closeWrappers ctx satProb dsatProb
          (realize ctx
            (directAndorTemplates right lefts middles tails ++
              (lefts.flatMap fun x => rights.flatMap fun z => orTemplates x z px pz) ++
              (rights.flatMap fun z => lefts.flatMap fun x =>
                orTemplates z x pz px)))
    | .thresh k subs, satProb, dsatProb =>
        let n := subs.length.toFloat
        let childSat := if n == 0 then 0 else satProb * k.toFloat / n
        let childDsat :=
          if n == 0 then dsatProb
          else dsatProb + satProb * (n - k.toFloat) / n
        let children := compileCandidatesList ctx subs childSat childDsat
        closeWrappers ctx satProb dsatProb
          (realize ctx (threshTemplates childSat childDsat k children ++
            multiTemplates ctx k subs))
    | leaf, satProb, dsatProb =>
        closeWrappers ctx satProb dsatProb (realize ctx (leafTemplates ctx leaf))

  /-- Candidate lists for threshold children. -/
  def compileCandidatesList (ctx : ScriptContext) :
      List Policy → Float → Float → List (List Candidate)
    | [], _, _ => []
    | sub :: subs, satProb, dsatProb =>
        compileCandidates ctx sub satProb dsatProb ::
          compileCandidatesList ctx subs satProb dsatProb
end

/-- Top-level `B` candidates, cheapest first. -/
def rankedFragments (ctx : ScriptContext) (policy : Policy) : List CoreFragment :=
  let top := (compileCandidates ctx policy 1 0).filter
    (fun candidate => candidate.ty.base == .B)
  (top.mergeSort (fun a b => a.better 1 0 b || !(b.better 1 0 a))).map
    Candidate.fragment

/-- The first fragment in a list that passes the static sanity check. -/
def firstSane (ctx : ScriptContext) :
    List CoreFragment → Option (SaneFragment ctx)
  | [] => none
  | fragment :: fragments =>
      match checkSane ctx fragment with
      | .ok sane => some sane
      | .error _ => firstSane ctx fragments

/-- The first fragment in a list that is well-formed and well-typed. -/
def firstChecked (ctx : ScriptContext) :
    List CoreFragment → Option (CheckedFragment ctx)
  | [] => none
  | fragment :: fragments =>
      match CheckedFragment.ofRaw? ctx fragment with
      | some checked => some checked
      | none => firstChecked ctx fragments

/-- Compile a policy to a statically sane Miniscript: the cheapest sane
    cost-based candidate. When no candidate is sane, the error explains why
    the cheapest candidate, or the structural translation when there is no
    candidate at all, fails the static sanity check. -/
def compilePolicy (ctx : ScriptContext) (policy : Policy) :
    Except SaneError (SaneFragment ctx) :=
  let ranked := rankedFragments ctx policy
  match firstSane ctx ranked with
  | some sane => .ok sane
  | none =>
      match ranked with
      | best :: _ => checkSane ctx best
      | [] => checkSane ctx policy.toMiniscript

/-- Compile a policy to a valid (well-formed, well-typed, top-level `B`)
    Miniscript without requiring static sanity. -/
def compilePolicyChecked (ctx : ScriptContext) (policy : Policy) :
    Option (CheckedFragment ctx) :=
  match firstChecked ctx (rankedFragments ctx policy) with
  | some checked => some checked
  | none => CheckedFragment.ofRaw? ctx policy.toMiniscript

namespace Policy

mutual
  /-- Normalize every key to the representation embedded in the context's
      Script: compressed keys stay as they are in P2WSH and become x-only in
      Tapscript. Fails on a key with the wrong serialized shape. -/
  def normalizeKeys (ctx : ScriptContext) : Policy → Option Policy
    | .key pubKey => (SurfaceParser.normalizeKeyForContext ctx pubKey).map .key
    | .and left right => do
        pure (.and (← normalizeKeys ctx left) (← normalizeKeys ctx right))
    | .or leftWeight left rightWeight right => do
        pure (.or leftWeight (← normalizeKeys ctx left) rightWeight
          (← normalizeKeys ctx right))
    | .thresh k subs => (normalizeKeysList ctx subs).map (.thresh k)
    | policy => some policy

  /-- Normalize the keys of every policy in a list. -/
  def normalizeKeysList (ctx : ScriptContext) : List Policy → Option (List Policy)
    | [] => some []
    | sub :: subs => do
        pure ((← normalizeKeys ctx sub) :: (← normalizeKeysList ctx subs))
end

end Policy

/-- Failures of the text-to-Miniscript policy compiler. -/
inductive PolicyCompileError where
  | parse (error : SurfaceParseError)
  | keyContext (ctx : ScriptContext)
  | sane (error : SaneError)
  deriving Repr, BEq

/-- Parse policy text with hexadecimal keys, normalize keys for the context,
    and compile it to a sane Miniscript. -/
def compilePolicyHex (ctx : ScriptContext) (input : String) :
    Except PolicyCompileError (SaneFragment ctx) :=
  match parsePolicyHex input with
  | .error error => .error (.parse error)
  | .ok policy =>
      match policy.normalizeKeys ctx with
      | none => .error (.keyContext ctx)
      | some policy =>
          match compilePolicy ctx policy with
          | .ok sane => .ok sane
          | .error error => .error (.sane error)

end LeanMiniscript.Policy
