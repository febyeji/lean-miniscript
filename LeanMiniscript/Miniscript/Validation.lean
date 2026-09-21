import LeanMiniscript.Miniscript.Context

namespace LeanMiniscript.Miniscript

/-- BIP 379 restricts `after` and `older` arguments to positive values below
    bit 31, independently of the wider raw Script-number operand boundary. -/
def MAX_BIP_LOCK_VALUE : Nat := 2147483648

/-- Exclusive signed four-byte bound for Miniscript arithmetic literals. -/
def MAX_BIP_ARITHMETIC_VALUE : Nat := MAX_BIP_LOCK_VALUE

/-- Values below this threshold are interpreted as block heights; values at or
    above it are interpreted as timestamps. -/
def LOCKTIME_THRESHOLD : Nat := 500000000

/-- BIP 68 sequence type flag (bit 22). -/
def SEQUENCE_LOCKTIME_TYPE_FLAG : Nat := 4194304

/-- SHA256/HASH256 hashes are represented by 32 bytes. -/
def validHash256 (hash : Hash256) : Prop :=
  hash.size = 32

/-- HASH160/RIPEMD160 hashes are represented by 20 bytes. -/
def validHash160 (hash : Hash160) : Prop :=
  hash.size = 20

/-- Shared arity invariant for threshold-like fragments. -/
def validThreshold (k n : Nat) : Prop :=
  1 ≤ k ∧ k ≤ n

/-- Legacy `multi` admits at most 20 public keys. -/
def validLegacyMultiKeyCount (n : Nat) : Prop :=
  n ≤ 20

/-- BIP 379 and Bitcoin Core admit at most 999 public keys in a Tapscript
    `multi_a` fragment. -/
def MAX_PUBKEYS_PER_MULTI_A : Nat := 999

/-- Tapscript `multi_a` public-key count bound. -/
def validCheckSigAddMultiKeyCount (n : Nat) : Prop :=
  n ≤ MAX_PUBKEYS_PER_MULTI_A

/-- AST-level timelock argument check used by `older` and `after`. -/
def validTimelockArg (n : Nat) : Prop :=
  1 ≤ n ∧ n < MAX_BIP_LOCK_VALUE

/-- Timelock classes used by the BIP 379 timelock-mixing side condition. -/
structure TimelockUsage where
  absoluteHeight : Bool := false
  absoluteTime : Bool := false
  relativeHeight : Bool := false
  relativeTime : Bool := false
  deriving Repr, DecidableEq, BEq

namespace TimelockUsage

/-- No timelocks. -/
def empty : TimelockUsage := {}

/-- Combine timelock usage from two subexpressions. -/
def union (x y : TimelockUsage) : TimelockUsage where
  absoluteHeight := x.absoluteHeight || y.absoluteHeight
  absoluteTime := x.absoluteTime || y.absoluteTime
  relativeHeight := x.relativeHeight || y.relativeHeight
  relativeTime := x.relativeTime || y.relativeTime

/-- Absolute locktime class for `after(n)`. -/
def fromAfter (m : Nat) : TimelockUsage :=
  if m < LOCKTIME_THRESHOLD then
    { absoluteHeight := true }
  else
    { absoluteTime := true }

/-- Whether BIP 68 bit 22 classifies a relative lock as time-based.
    Dividing by `2^22` and taking parity tests that bit without treating it as
    a numeric threshold; higher sequence bits do not change the classification. -/
def sequenceLocktimeIsTime (m : Nat) : Bool :=
  (m / SEQUENCE_LOCKTIME_TYPE_FLAG) % 2 == 1

/-- Relative locktime class for `older(n)`. -/
def fromOlder (m : Nat) : TimelockUsage :=
  if sequenceLocktimeIsTime m then
    { relativeTime := true }
  else
    { relativeHeight := true }

/-- BIP 379 forbids mixing height and time locks of the same absolute/relative
    family inside AND-like combinators and `thresh` when `k >= 2`. -/
def compatible (usage : TimelockUsage) : Prop :=
  ¬ (usage.absoluteHeight = true ∧ usage.absoluteTime = true) ∧
  ¬ (usage.relativeHeight = true ∧ usage.relativeTime = true)

/-- Two child summaries can execute together without mixing height and time
    locks. Each child's internal `k` property is checked recursively, so this
    predicate tests only conflicts that cross the child boundary. -/
def compatibleWith (x y : TimelockUsage) : Prop :=
  ¬ ((x.absoluteHeight = true ∧ y.absoluteTime = true) ∨
      (x.absoluteTime = true ∧ y.absoluteHeight = true)) ∧
  ¬ ((x.relativeHeight = true ∧ y.relativeTime = true) ∨
      (x.relativeTime = true ∧ y.relativeHeight = true))

end TimelockUsage

namespace CoreFragment

mutual
  /-- Timelock usage summary for a core fragment. -/
  def timelocks : CoreFragment → TimelockUsage
    | .zero => .empty
    | .one => .empty
    | .pk_k _ => .empty
    | .pk_h _ => .empty
    | .older m => TimelockUsage.fromOlder m
    | .after m => TimelockUsage.fromAfter m
    | .sha256 _ => .empty
    | .hash256 _ => .empty
    | .ripemd160 _ => .empty
    | .hash160 _ => .empty
    | .and_v x y => (timelocks x).union (timelocks y)
    | .and_b x y => (timelocks x).union (timelocks y)
    | .or_b x y => (timelocks x).union (timelocks y)
    | .or_c x y => (timelocks x).union (timelocks y)
    | .or_d x y => (timelocks x).union (timelocks y)
    | .or_i x y => (timelocks x).union (timelocks y)
    | .andor x y z => (timelocks x).union ((timelocks y).union (timelocks z))
    | .a x => timelocks x
    | .s x => timelocks x
    | .c x => timelocks x
    | .d x => timelocks x
    | .v x => timelocks x
    | .j x => timelocks x
    | .n x => timelocks x
    | .thresh _ fragments => listTimelocks fragments
    | .multi _ _ => .empty
    | .multi_a _ _ => .empty

  /-- Timelock usage summary for a list of core fragments. -/
  def listTimelocks : List CoreFragment → TimelockUsage
    | [] => .empty
    | fragment :: fragments => (timelocks fragment).union (listTimelocks fragments)
end

/-- Timelock mixing check for an AND-like pair. -/
def andTimelocksCompatible (x y : CoreFragment) : Prop :=
  (timelocks x).compatibleWith (timelocks y)

/-- In `andor(X,Y,Z)`, only the satisfied X/Y path combines timelocks. The Z
    branch follows an unconditional dissatisfaction of X and is exclusive with
    Y, matching the BIP 379 `k` rule. The third argument preserves the public
    helper's constructor-shaped API. -/
def andorTimelocksCompatible (x y _z : CoreFragment) : Prop :=
  andTimelocksCompatible x y

/-- Every pair of threshold children can execute together without a cross-child
    timelock conflict. This preserves valid exclusive branches inside a child. -/
def listTimelocksPairwiseCompatible : List CoreFragment → Prop
  | [] => True
  | fragment :: fragments =>
      (timelocks fragment).compatibleWith (listTimelocks fragments) ∧
      listTimelocksPairwiseCompatible fragments

mutual
  /-- Every public key in a list is usable in the given script context. -/
  def allKeysValid (ctx : ScriptContext) : List PubKey → Prop
    | [] => True
    | key :: keys => validResolvedPubKey ctx key ∧ allKeysValid ctx keys

  /-- Every core fragment in a list is well-formed in the given context. -/
  def allWellFormed (ctx : ScriptContext) : List CoreFragment → Prop
    | [] => True
    | fragment :: fragments => WellFormed ctx fragment ∧ allWellFormed ctx fragments

  /-- BIP-facing structural well-formedness for core Miniscript fragments.

      This is deliberately separate from `Syntax.lean`: it records context and
      side conditions, while `CoreFragment` remains the raw AST. -/
  def WellFormed (ctx : ScriptContext) : CoreFragment → Prop
    | .zero => True
    | .one => True
    | .pk_k key => validResolvedPubKey ctx key
    | .pk_h key => validResolvedPubKey ctx key
    | .older m => validTimelockArg m
    | .after m => validTimelockArg m
    | .sha256 hash => validHash256 hash
    | .hash256 hash => validHash256 hash
    | .ripemd160 hash => validHash160 hash
    | .hash160 hash => validHash160 hash
    | .and_v x y => WellFormed ctx x ∧ WellFormed ctx y ∧ andTimelocksCompatible x y
    | .and_b x y => WellFormed ctx x ∧ WellFormed ctx y ∧ andTimelocksCompatible x y
    | .or_b x y => WellFormed ctx x ∧ WellFormed ctx y
    | .or_c x y => WellFormed ctx x ∧ WellFormed ctx y
    | .or_d x y => WellFormed ctx x ∧ WellFormed ctx y
    | .or_i x y => WellFormed ctx x ∧ WellFormed ctx y
    | .andor x y z =>
        WellFormed ctx x ∧ WellFormed ctx y ∧ WellFormed ctx z ∧
        andorTimelocksCompatible x y z
    | .a x => WellFormed ctx x
    | .s x => WellFormed ctx x
    | .c x => WellFormed ctx x
    | .d x => WellFormed ctx x
    | .v x => WellFormed ctx x
    | .j x => WellFormed ctx x
    | .n x => WellFormed ctx x
    | .thresh k fragments =>
        validThreshold k fragments.length ∧
        allWellFormed ctx fragments ∧
        (2 ≤ k → listTimelocksPairwiseCompatible fragments) ∧
        k < MAX_BIP_ARITHMETIC_VALUE
    | .multi k keys =>
        ctx.permitsLegacyMulti ∧
        validThreshold k keys.length ∧
        validLegacyMultiKeyCount keys.length ∧
        allKeysValid ctx keys
    | .multi_a k keys =>
        ctx.permitsCheckSigAddMulti ∧
        validThreshold k keys.length ∧
        validCheckSigAddMultiKeyCount keys.length ∧
        allKeysValid ctx keys
end

end CoreFragment

namespace SurfaceFragment

/-- Well-formedness for surface Miniscript after lowering syntactic sugar. -/
def WellFormed (ctx : ScriptContext) (fragment : SurfaceFragment) : Prop :=
  (desugar fragment).WellFormed ctx

end SurfaceFragment

end LeanMiniscript.Miniscript
