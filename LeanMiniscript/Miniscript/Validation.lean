import LeanMiniscript.Miniscript.Context

namespace LeanMiniscript.Miniscript

/-- BIP 65/68 locktime and sequence arguments must fit below bit 31. -/
def MAX_BIP_LOCK_VALUE : Nat := 2147483648

/-- Values below this threshold are interpreted as block heights; values at or
    above it are interpreted as timestamps. -/
def LOCKTIME_THRESHOLD : Nat := 500000000

/-- BIP 68 sequence type flag. Values at or above this flag are conservatively
    classified as time-based relative timelocks in this AST-level model. -/
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

/-- Relative locktime class for `older(n)`. -/
def fromOlder (m : Nat) : TimelockUsage :=
  if m < SEQUENCE_LOCKTIME_TYPE_FLAG then
    { relativeHeight := true }
  else
    { relativeTime := true }

/-- BIP 379 forbids mixing height and time locks of the same absolute/relative
    family inside AND-like combinators and `thresh` when `k >= 2`. -/
def compatible (usage : TimelockUsage) : Prop :=
  ¬ (usage.absoluteHeight = true ∧ usage.absoluteTime = true) ∧
  ¬ (usage.relativeHeight = true ∧ usage.relativeTime = true)

instance (usage : TimelockUsage) : Decidable usage.compatible := by
  unfold compatible
  infer_instance

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
  ((timelocks x).union (timelocks y)).compatible

/-- Timelock mixing check for an AND-like triple. -/
def andorTimelocksCompatible (x y z : CoreFragment) : Prop :=
  ((timelocks x).union ((timelocks y).union (timelocks z))).compatible

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
        (2 ≤ k → (listTimelocks fragments).compatible)
    | .multi k keys =>
        ctx.permitsLegacyMulti ∧
        validThreshold k keys.length ∧
        validLegacyMultiKeyCount keys.length ∧
        allKeysValid ctx keys
    | .multi_a k keys =>
        ctx.permitsCheckSigAddMulti ∧
        validThreshold k keys.length ∧
        allKeysValid ctx keys
end

/-- Executable decision procedure for public-key list validity. -/
def allKeysValidDecidable (ctx : ScriptContext) (keys : List PubKey) :
    Decidable (allKeysValid ctx keys) := by
  cases keys with
  | nil =>
      simp only [allKeysValid]
      infer_instance
  | cons key keys =>
      letI := allKeysValidDecidable ctx keys
      simp only [allKeysValid, validResolvedPubKey]
      cases ctx <;> infer_instance

mutual
  /-- Executable decision procedure for fragment-list well-formedness. -/
  def allWellFormedDecidable (ctx : ScriptContext) (fragments : List CoreFragment) :
      Decidable (allWellFormed ctx fragments) := by
    cases fragments with
    | nil =>
        simp only [allWellFormed]
        infer_instance
    | cons fragment fragments =>
        letI := wellFormedDecidable ctx fragment
        letI := allWellFormedDecidable ctx fragments
        simp only [allWellFormed]
        infer_instance

  /-- Executable decision procedure for core-fragment well-formedness. -/
  def wellFormedDecidable (ctx : ScriptContext) (fragment : CoreFragment) :
      Decidable (WellFormed ctx fragment) := by
    cases fragment with
    | zero | one | pk_k | pk_h | older | after | sha256 | hash256 |
        ripemd160 | hash160 =>
        simp only [WellFormed, validResolvedPubKey, validTimelockArg,
          validHash256, validHash160]
        cases ctx <;> infer_instance
    | and_v x y | and_b x y | or_b x y | or_c x y | or_d x y | or_i x y =>
        letI := wellFormedDecidable ctx x
        letI := wellFormedDecidable ctx y
        simp only [WellFormed, andTimelocksCompatible]
        infer_instance
    | andor x y z =>
        letI := wellFormedDecidable ctx x
        letI := wellFormedDecidable ctx y
        letI := wellFormedDecidable ctx z
        simp only [WellFormed, andorTimelocksCompatible]
        infer_instance
    | a x | s x | c x | d x | v x | j x | n x =>
        simpa only [WellFormed] using wellFormedDecidable ctx x
    | thresh _ fragments =>
        letI := allWellFormedDecidable ctx fragments
        simp only [WellFormed, validThreshold]
        infer_instance
    | multi _ keys | multi_a _ keys =>
        letI := allKeysValidDecidable ctx keys
        simp only [WellFormed, ScriptContext.permitsLegacyMulti,
          ScriptContext.permitsCheckSigAddMulti, validThreshold,
          validLegacyMultiKeyCount]
        cases ctx <;> infer_instance
end

instance (ctx : ScriptContext) (fragment : CoreFragment) :
    Decidable (WellFormed ctx fragment) :=
  wellFormedDecidable ctx fragment

end CoreFragment

namespace SurfaceFragment

/-- Well-formedness for surface Miniscript after lowering syntactic sugar. -/
def WellFormed (ctx : ScriptContext) (fragment : SurfaceFragment) : Prop :=
  (desugar fragment).WellFormed ctx

instance (ctx : ScriptContext) (fragment : SurfaceFragment) :
    Decidable (WellFormed ctx fragment) :=
  CoreFragment.wellFormedDecidable ctx (desugar fragment)

end SurfaceFragment

end LeanMiniscript.Miniscript
