import LeanMiniscript.Miniscript.Validation

/-!
# Spending policies

`Policy` is the high-level policy language accepted by rust-miniscript's
`policy::Concrete` and Bitcoin Core's policy compiler tests. Leaves reuse the
resolved Miniscript key, hash, and timelock representations, so a policy can be
compiled without a second key or digest boundary.

Policies are context-free. `Policy.WellFormed` states the side conditions that
the selected P2WSH or Tapscript context imposes on the compiled Miniscript.
-/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript

/-- High-level spending policy AST.

    `or` carries the relative branch probabilities written as `N@` in policy
    text; an omitted weight is `1`. Weights guide cost-based compilation only
    and never change the policy's meaning. -/
inductive Policy where
  | unsatisfiable
  | trivial
  | key (key : PubKey)
  | after (n : Nat)
  | older (n : Nat)
  | sha256 (hash : Hash256)
  | hash256 (hash : Hash256)
  | ripemd160 (hash : Hash160)
  | hash160 (hash : Hash160)
  | and (left right : Policy)
  | or (leftWeight : Nat) (left : Policy) (rightWeight : Nat) (right : Policy)
  | thresh (k : Nat) (subs : List Policy)
  deriving Repr, Inhabited

namespace Policy

/-- Unweighted disjunction; both branches carry the default weight `1`. -/
def or' (left right : Policy) : Policy :=
  .or 1 left 1 right

mutual
  /-- Timelock classes used by a policy. Matches `CoreFragment.timelocks` on
      every compiled fragment. -/
  def timelocks : Policy → TimelockUsage
    | .after n => TimelockUsage.fromAfter n
    | .older n => TimelockUsage.fromOlder n
    | .and left right => left.timelocks.union right.timelocks
    | .or _ left _ right => left.timelocks.union right.timelocks
    | .thresh _ subs => listTimelocks subs
    | _ => .empty

  /-- Timelock classes used by a list of policies. -/
  def listTimelocks : List Policy → TimelockUsage
    | [] => .empty
    | sub :: subs => sub.timelocks.union (listTimelocks subs)
end

/-- Every pair of threshold branches avoids a cross-branch height/time mix. -/
def listTimelocksPairwiseCompatible : List Policy → Prop
  | [] => True
  | sub :: subs =>
      sub.timelocks.compatibleWith (listTimelocks subs) ∧
        listTimelocksPairwiseCompatible subs

mutual
  /-- Side conditions required to compile a policy in a script context: keys
      must have the context's serialized shape, hashes their digest length,
      timelocks the BIP 379 range, thresholds a valid arity, and conjunctive
      combinations must not mix height- and time-based locks. -/
  def WellFormed (ctx : ScriptContext) : Policy → Prop
    | .unsatisfiable => True
    | .trivial => True
    | .key pubKey => validResolvedPubKey ctx pubKey
    | .after n => validTimelockArg n
    | .older n => validTimelockArg n
    | .sha256 hash => validHash256 hash
    | .hash256 hash => validHash256 hash
    | .ripemd160 hash => validHash160 hash
    | .hash160 hash => validHash160 hash
    | .and left right =>
        WellFormed ctx left ∧ WellFormed ctx right ∧
          left.timelocks.compatibleWith right.timelocks
    | .or _ left _ right => WellFormed ctx left ∧ WellFormed ctx right
    | .thresh k subs =>
        validThreshold k subs.length ∧ allWellFormed ctx subs ∧
          (2 ≤ k → listTimelocksPairwiseCompatible subs) ∧
          k < MAX_BIP_ARITHMETIC_VALUE

  /-- Every policy in a list is well-formed. -/
  def allWellFormed (ctx : ScriptContext) : List Policy → Prop
    | [] => True
    | sub :: subs => WellFormed ctx sub ∧ allWellFormed ctx subs
end

mutual
  /-- Number of policy AST nodes. -/
  def nodeCount : Policy → Nat
    | .and left right => 1 + left.nodeCount + right.nodeCount
    | .or _ left _ right => 1 + left.nodeCount + right.nodeCount
    | .thresh _ subs => 1 + listNodeCount subs
    | _ => 1

  /-- Number of policy AST nodes in a list. -/
  def listNodeCount : List Policy → Nat
    | [] => 0
    | sub :: subs => sub.nodeCount + listNodeCount subs
end

end Policy

end LeanMiniscript.Policy
