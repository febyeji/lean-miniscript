import LeanMiniscript.Miniscript.Syntax
import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Witness
import LeanMiniscript.Script.SignatureChecks

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A typed hashlock target for preimage lookup. -/
inductive HashLock where
  | sha256 : Hash256 → HashLock
  | hash256 : Hash256 → HashLock
  | ripemd160 : Hash160 → HashLock
  | hash160 : Hash160 → HashLock

namespace HashLock

/-- The cryptographic relation required of a supplied preimage. Hash functions
    remain opaque at the formal boundary. -/
def Matches : HashLock → StackElement → Prop
  | .sha256 expected, preimage =>
      LeanMiniscript.Script.sha256 preimage = expected.bytes
  | .hash256 expected, preimage =>
      LeanMiniscript.Script.hash256 preimage = expected.bytes
  | .ripemd160 expected, preimage =>
      LeanMiniscript.Script.ripemd160 preimage = expected.bytes
  | .hash160 expected, preimage =>
      LeanMiniscript.Script.hash160 preimage = expected.bytes

end HashLock

/-- An environment provides the "real-world" data needed for satisfaction:
    concrete signatures, preimages, and the transaction context. -/
structure SatEnv where
  /-- Return the exact stack element to use as a signature, when available. -/
  signatureFor : PubKey → Option StackElement
  /-- Return the exact preimage stack element for a typed hashlock. -/
  preimageFor : HashLock → Option StackElement
  /-- Transaction data used by signature and timelock checks. -/
  txCtx : TxContext

namespace SatEnv

/-- Every piece of material returned by an environment satisfies the abstract
    cryptographic boundary used by `Eval`. -/
def Sound (env : SatEnv) : Prop :=
  (∀ key signature,
      env.signatureFor key = some signature →
      verifySigFor checkSig checkSchnorrSig env.txCtx signature key.bytes = true) ∧
  (∀ key : PubKey,
      verifySigFor checkSig checkSchnorrSig env.txCtx falseElement key.bytes = false) ∧
  (∀ lock preimage,
      env.preimageFor lock = some preimage →
      lock.Matches preimage)

/-- Supplied signatures and their keys pass the version-specific byte checks selected by
    the execution flags. Cryptographic soundness alone does not imply this. -/
def EncodingSound (env : SatEnv) (flags : ScriptFlags) : Prop :=
  ∀ key signature,
    env.signatureFor key = some signature →
    checkSigEncodingFor flags env.txCtx.sigVersion signature key.bytes = .ok ()

end SatEnv

/-- Whether a possible witness remains usable during recursive BIP 379
    selection. `dontUse` retains a semantically possible witness for
    composition and proofs while preventing the composite from being chosen. -/
inductive CandidateStatus where
  | usable
  | dontUse
  deriving Repr, DecidableEq, BEq

/-- Whether a witness comes from a canonical BIP 379 table row or from a valid
    but non-canonical alternative retained for later malleability analysis. -/
inductive CandidateOrigin where
  | canonical
  | nonCanonical
  deriving Repr, DecidableEq, BEq

namespace CandidateStatus

/-- Combining witnesses propagates `DONTUSE`: the composite is usable only
    when both constituents are usable. -/
def combine : CandidateStatus → CandidateStatus → CandidateStatus
  | .usable, .usable => .usable
  | _, _ => .dontUse

@[simp] theorem combine_eq_usable_iff (left right : CandidateStatus) :
    combine left right = .usable ↔ left = .usable ∧ right = .usable := by
  cases left <;> cases right <;> simp [combine]

end CandidateStatus

namespace CandidateOrigin

/-- A composite is canonical exactly when both constituents are canonical. -/
def combine : CandidateOrigin → CandidateOrigin → CandidateOrigin
  | .canonical, .canonical => .canonical
  | _, _ => .nonCanonical

@[simp] theorem combine_eq_canonical_iff (left right : CandidateOrigin) :
    combine left right = .canonical ↔
      left = .canonical ∧ right = .canonical := by
  cases left <;> cases right <;> simp [combine]

end CandidateOrigin

/-- One possible satisfaction or dissatisfaction witness together with the
    metadata needed by later BIP 379 candidate selection. Candidate cost is
    computed from `witness`, rather than stored, so it cannot become stale. -/
structure SatisfactionCandidate where
  witness : Witness
  hasSig : Bool
  status : CandidateStatus := .usable
  origin : CandidateOrigin := .canonical
  deriving Repr

namespace SatisfactionCandidate

/-- Additive BIP 379 candidate cost. Item length prefixes are included; the
    outer witness item-count prefix belongs to full wire serialization and is
    excluded here. -/
def cost (candidate : SatisfactionCandidate) : Nat :=
  Witness.candidateCost candidate.witness

/-- Compose candidates for fragments that execute in the order `first`, then
    `second`. Signature presence is disjunctive, while `DONTUSE` and
    non-canonical origins propagate through the composition. -/
def combine (first second : SatisfactionCandidate) : SatisfactionCandidate where
  witness := Witness.combine first.witness second.witness
  hasSig := first.hasSig || second.hasSig
  status := first.status.combine second.status
  origin := first.origin.combine second.origin

@[simp] theorem combine_witness
    (first second : SatisfactionCandidate) :
    (combine first second).witness =
      Witness.combine first.witness second.witness := by
  rfl

@[simp] theorem combine_hasSig
    (first second : SatisfactionCandidate) :
    (combine first second).hasSig = (first.hasSig || second.hasSig) := by
  rfl

@[simp] theorem combine_cost
    (first second : SatisfactionCandidate) :
    (combine first second).cost = first.cost + second.cost := by
  simp [cost, combine]

@[simp] theorem combine_status_eq_usable_iff
    (first second : SatisfactionCandidate) :
    (combine first second).status = .usable ↔
      first.status = .usable ∧ second.status = .usable := by
  simp [combine]

@[simp] theorem combine_origin_eq_canonical_iff
    (first second : SatisfactionCandidate) :
    (combine first second).origin = .canonical ↔
      first.origin = .canonical ∧ second.origin = .canonical := by
  simp [combine]

end SatisfactionCandidate

/-- A candidate may be impossible or carry a concrete witness. Keeping
    impossibility outside `SatisfactionCandidate` makes invalid states such as
    an "available" candidate without a witness unrepresentable. -/
inductive CandidateResult where
  | impossible
  | candidate : SatisfactionCandidate → CandidateResult
  deriving Repr

namespace CandidateResult

/-- Construct a selectable canonical candidate. -/
def usable (witness : Witness) (hasSig : Bool) : CandidateResult :=
  .candidate { witness, hasSig }

/-- Construct a possible candidate which BIP selection must not use. DONTUSE
    status and canonical origin are independent, so callers must classify the
    origin explicitly. Hashlock dissatisfactions, for example, are canonical
    table rows that are nevertheless DONTUSE. -/
def dontUse (witness : Witness) (hasSig : Bool)
    (origin : CandidateOrigin) : CandidateResult :=
  .candidate { witness, hasSig, status := .dontUse, origin }

/-- Extract every concrete witness, including one marked `DONTUSE`. -/
def witness? : CandidateResult → Option Witness
  | .impossible => none
  | .candidate value => some value.witness

/-- Project a witness unless it is marked DONTUSE. This only enforces the
    DONTUSE boundary; top-level timelock/HASSIG policy is a later selection
    step. -/
def usableWitness? : CandidateResult → Option Witness
  | .impossible => none
  | .candidate value =>
      match value.status with
      | .usable => some value.witness
      | .dontUse => none

/-- Compose two possible results. Impossibility is absorbing. -/
def combine : CandidateResult → CandidateResult → CandidateResult
  | .candidate first, .candidate second => .candidate (first.combine second)
  | _, _ => .impossible

@[simp] theorem usable_witness? (witness : Witness) (hasSig : Bool) :
    (usable witness hasSig).usableWitness? = some witness := by
  rfl

@[simp] theorem dontUse_usableWitness? (witness : Witness) (hasSig : Bool)
    (origin : CandidateOrigin) :
    (dontUse witness hasSig origin).usableWitness? = none := by
  rfl

@[simp] theorem impossible_usableWitness? :
    (impossible : CandidateResult).usableWitness? = none := by
  rfl

@[simp] theorem combine_eq_impossible_iff
    (left right : CandidateResult) :
    combine left right = .impossible ↔
      left = .impossible ∨ right = .impossible := by
  cases left <;> cases right <;> simp [combine]

end CandidateResult

/-- The best currently known satisfaction and dissatisfaction for one
    fragment. Both sides are retained because parent fragments often need one
    of each to construct their own candidates. -/
structure CandidatePair where
  sat : CandidateResult := .impossible
  dsat : CandidateResult := .impossible
  deriving Repr

/-- Compute the candidate pair for the currently supported basic B-type
    fragments. Unsupported rows are explicitly impossible on both sides. -/
@[simp] def satisfactionCandidates : CoreFragment → SatEnv → CandidatePair
  | .zero, _ => { dsat := .usable [] false }
  | .one, _ => { sat := .usable [] false }
  | .c (.pk_k key), env =>
      { sat := match env.signatureFor key with
          | none => .impossible
          | some signature => .usable [signature] true
        dsat := .usable [falseElement] false }
  | .older n, env =>
      { sat := if sequenceSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | .after n, env =>
      { sat := if locktimeSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | _, _ => {}

/-- Compute a satisfaction witness for the currently supported basic B-type
    fragments. Timelocks consult the same transaction predicates as `Eval`, and
    signatures are returned in serialized witness order. Composite fragments
    and hashlocks remain unsupported until their candidate-selection rules are
    represented explicitly. -/
def satisfy : CoreFragment → SatEnv → Option Witness
  | .one, _ => some []
  | .c (.pk_k key), env => List.singleton <$> env.signatureFor key
  | .older n, env => if sequenceSatisfied n env.txCtx then some [] else none
  | .after n, env => if locktimeSatisfied n env.txCtx then some [] else none
  | _, _ => none

/-- Compute a clean dissatisfaction witness for the currently supported basic
    B-type fragments. `0` needs no witness; `c(pk_k)` uses the canonical empty
    signature whose failure is part of `SatEnv.Sound`. -/
def dissatisfy : CoreFragment → SatEnv → Option Witness
  | .zero, _ => some []
  | .c (.pk_k _), _ => some [falseElement]
  | _, _ => none

/-- The paired candidate API preserves the existing public satisfaction
    algorithm on every currently supported and unsupported constructor. -/
theorem satisfactionCandidates_sat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat.usableWitness? =
      satisfy fragment env := by
  cases fragment <;> simp [satisfy]
  case older n =>
    by_cases available : sequenceSatisfied n env.txCtx <;> simp [available]
  case after n =>
    by_cases available : locktimeSatisfied n env.txCtx <;> simp [available]
  case c fragment =>
    cases fragment <;> try rfl
    case pk_k key =>
      cases selected : env.signatureFor key <;>
        simp [selected, List.singleton]

/-- The paired candidate API preserves the existing public dissatisfaction
    algorithm on every currently supported and unsupported constructor. -/
theorem satisfactionCandidates_dsat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).dsat.usableWitness? =
      dissatisfy fragment env := by
  cases fragment <;> simp [dissatisfy]
  case c fragment => cases fragment <;> rfl

/- These equations preserve the original public API while the implementation
   moves to paired candidates. They also keep existing proof scripts independent
   of the representation of `CandidateResult`. -/

@[simp] theorem satisfy_one (env : SatEnv) :
    satisfy .one env = some [] := by
  rfl

@[simp] theorem satisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    satisfy (.c (.pk_k key)) env = List.singleton <$> env.signatureFor key := by
  cases selected : env.signatureFor key <;>
    simp [satisfy, selected, List.singleton]

@[simp] theorem satisfy_older (n : Nat) (env : SatEnv) :
    satisfy (.older n) env =
      if sequenceSatisfied n env.txCtx then some [] else none := by
  by_cases available : sequenceSatisfied n env.txCtx <;>
    simp [satisfy, available]

@[simp] theorem satisfy_after (n : Nat) (env : SatEnv) :
    satisfy (.after n) env =
      if locktimeSatisfied n env.txCtx then some [] else none := by
  by_cases available : locktimeSatisfied n env.txCtx <;>
    simp [satisfy, available]

@[simp] theorem dissatisfy_zero (env : SatEnv) :
    dissatisfy .zero env = some [] := by
  rfl

@[simp] theorem dissatisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    dissatisfy (.c (.pk_k key)) env = some [falseElement] := by
  rfl

-- TODO(theorem): Extend satisfaction and dissatisfaction correctness through
-- hashlocks, wrappers, connectives, thresholds, `multi`, and `multi_a`.
-- TODO: Analyze non-malleable satisfaction (unique canonical witness)

end LeanMiniscript.Miniscript
