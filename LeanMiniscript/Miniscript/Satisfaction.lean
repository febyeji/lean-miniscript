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

/-- Apply the hash operation selected by a typed hashlock. Hash functions
    remain opaque at the formal boundary. -/
def digest : HashLock → StackElement → StackElement
  | .sha256 _, preimage => LeanMiniscript.Script.sha256 preimage
  | .hash256 _, preimage => LeanMiniscript.Script.hash256 preimage
  | .ripemd160 _, preimage => LeanMiniscript.Script.ripemd160 preimage
  | .hash160 _, preimage => LeanMiniscript.Script.hash160 preimage

/-- The digest committed to by a typed hashlock. -/
def expected : HashLock → StackElement
  | .sha256 hash | .hash256 hash => hash.bytes
  | .ripemd160 hash | .hash160 hash => hash.bytes

/-- The core fragment represented by a typed hashlock. -/
def fragment : HashLock → CoreFragment
  | .sha256 hash => .sha256 hash
  | .hash256 hash => .hash256 hash
  | .ripemd160 hash => .ripemd160 hash
  | .hash160 hash => .hash160 hash

/-- The complete BIP 379 preimage relation, including the mandatory 32-byte
    input length enforced by the compiled `SIZE 32 EQUALVERIFY` prefix. -/
def Matches (lock : HashLock) (preimage : StackElement) : Prop :=
  preimage.size = 32 ∧ lock.digest preimage = lock.expected

/-- A 32-byte value which executes a hashlock to false rather than aborting. -/
def Mismatches (lock : HashLock) (nonPreimage : StackElement) : Prop :=
  nonPreimage.size = 32 ∧ lock.digest nonPreimage ≠ lock.expected

end HashLock

/-- An environment provides the "real-world" data needed for satisfaction:
    concrete signatures, preimages, and the transaction context. -/
structure SatEnv where
  /-- Return the exact stack element to use as a signature, when available. -/
  signatureFor : PubKey → Option StackElement
  /-- Return the exact preimage stack element for a typed hashlock. -/
  preimageFor : HashLock → Option StackElement
  /-- Return a 32-byte nonpreimage used for the hashlock's unconditional
      semantic dissatisfaction. The soundness predicate records its relation
      to each target. -/
  nonPreimageFor : HashLock → StackElement
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
      lock.Matches preimage) ∧
  (∀ lock : HashLock, lock.Mismatches (env.nonPreimageFor lock))

/-- A returned signature verifies under the environment transaction. -/
theorem Sound.signatureValid {env : SatEnv} (sound : env.Sound)
    {key : PubKey} {signature : StackElement}
    (selected : env.signatureFor key = some signature) :
    verifySigFor checkSig checkSchnorrSig env.txCtx signature key.bytes = true :=
  sound.1 key signature selected

/-- The canonical empty signature is rejected for every key. -/
theorem Sound.emptySignatureInvalid {env : SatEnv} (sound : env.Sound)
    (key : PubKey) :
    verifySigFor checkSig checkSchnorrSig env.txCtx falseElement key.bytes = false :=
  sound.2.1 key

/-- Every returned hash preimage has the exact size and digest required by its
    target. -/
theorem Sound.preimageMatches {env : SatEnv} (sound : env.Sound)
    {lock : HashLock} {preimage : StackElement}
    (selected : env.preimageFor lock = some preimage) :
    lock.Matches preimage :=
  sound.2.2.1 lock preimage selected

/-- Every hash dissatisfaction supplied by the environment is a 32-byte
    nonpreimage. -/
theorem Sound.nonPreimageMismatches {env : SatEnv} (sound : env.Sound)
    (lock : HashLock) :
    lock.Mismatches (env.nonPreimageFor lock) :=
  sound.2.2.2 lock

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

/-- Construct the BIP 379 key row. `keyTail` is empty for `pk_k` and contains
    the revealed key for `pk_h`; the signature remains first in serialized
    witness order so it lies below the K fragment's own arguments at runtime. -/
def keyCandidates (key : PubKey) (keyTail : Witness)
    (env : SatEnv) : CandidatePair where
  sat := match env.signatureFor key with
    | none => .impossible
    | some signature => .usable (signature :: keyTail) true
  dsat := .usable (falseElement :: keyTail) false

/-- Construct a hashlock row. A matching preimage is selectable when
    available. The canonical nonpreimage dissatisfaction remains available
    for recursive semantics but is always marked DONTUSE by BIP 379. -/
def hashCandidates (lock : HashLock) (env : SatEnv) : CandidatePair where
  sat := match env.preimageFor lock with
    | none => .impossible
    | some preimage => .usable [preimage] false
  dsat := .dontUse [env.nonPreimageFor lock] false .canonical

/-- Compute the candidate pair for the supported leaf rows. Wrapper `c` and
    the linear wrappers `a`, `s`, and `n` preserve the complete child pair;
    `v` preserves only satisfaction because V fragments cannot dissatisfy.
    Unsupported rows are explicitly impossible on both sides. -/
@[simp] def satisfactionCandidates : CoreFragment → SatEnv → CandidatePair
  | .zero, _ => { dsat := .usable [] false }
  | .one, _ => { sat := .usable [] false }
  | .pk_k key, env => keyCandidates key [] env
  | .pk_h key, env => keyCandidates key [key.bytes] env
  | .older n, env =>
      { sat := if sequenceSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | .after n, env =>
      { sat := if locktimeSatisfied n env.txCtx then .usable [] false
          else .impossible }
  | .sha256 hash, env => hashCandidates (.sha256 hash) env
  | .hash256 hash, env => hashCandidates (.hash256 hash) env
  | .ripemd160 hash, env => hashCandidates (.ripemd160 hash) env
  | .hash160 hash, env => hashCandidates (.hash160 hash) env
  | .c fragment, env => satisfactionCandidates fragment env
  | .a fragment, env => satisfactionCandidates fragment env
  | .s fragment, env => satisfactionCandidates fragment env
  | .v fragment, env => { sat := (satisfactionCandidates fragment env).sat }
  | .n fragment, env => satisfactionCandidates fragment env
  | _, _ => {}

/-- Project the usable satisfaction candidate. This is the leaf/composition
    projection only; final timelock/HASSIG policy remains a later step. -/
def satisfy (fragment : CoreFragment) (env : SatEnv) : Option Witness :=
  (satisfactionCandidates fragment env).sat.usableWitness?

/-- Project the usable dissatisfaction candidate. Canonical hash
    dissatisfactions are deliberately absent here because their raw candidates
    are DONTUSE. -/
def dissatisfy (fragment : CoreFragment) (env : SatEnv) : Option Witness :=
  (satisfactionCandidates fragment env).dsat.usableWitness?

/-- The paired candidate API is the single source for public satisfaction. -/
theorem satisfactionCandidates_sat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat.usableWitness? =
      satisfy fragment env := by
  rfl

/-- The paired candidate API is the single source for public dissatisfaction. -/
theorem satisfactionCandidates_dsat_witness
    (fragment : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).dsat.usableWitness? =
      dissatisfy fragment env := by
  rfl

/- These equations preserve the original public API while the implementation
   moves to paired candidates. They also keep existing proof scripts independent
   of the representation of `CandidateResult`. -/

@[simp] theorem satisfy_one (env : SatEnv) :
    satisfy .one env = some [] := by
  rfl

@[simp] theorem satisfy_pk_k (key : PubKey) (env : SatEnv) :
    satisfy (.pk_k key) env = List.singleton <$> env.signatureFor key := by
  cases selected : env.signatureFor key <;>
    simp [satisfy, keyCandidates, selected, List.singleton]

@[simp] theorem satisfy_pk_h (key : PubKey) (env : SatEnv) :
    satisfy (.pk_h key) env =
      (fun signature => [signature, key.bytes]) <$> env.signatureFor key := by
  cases selected : env.signatureFor key <;>
    simp [satisfy, keyCandidates, selected]

@[simp] theorem satisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    satisfy (.c (.pk_k key)) env = List.singleton <$> env.signatureFor key := by
  simpa [satisfy] using satisfy_pk_k key env

@[simp] theorem satisfy_c_pk_h (key : PubKey) (env : SatEnv) :
    satisfy (.c (.pk_h key)) env =
      (fun signature => [signature, key.bytes]) <$> env.signatureFor key := by
  simpa [satisfy] using satisfy_pk_h key env

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

@[simp] theorem satisfy_sha256 (hash : Hash256) (env : SatEnv) :
    satisfy (.sha256 hash) env =
      List.singleton <$> env.preimageFor (.sha256 hash) := by
  cases selected : env.preimageFor (.sha256 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_hash256 (hash : Hash256) (env : SatEnv) :
    satisfy (.hash256 hash) env =
      List.singleton <$> env.preimageFor (.hash256 hash) := by
  cases selected : env.preimageFor (.hash256 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_ripemd160 (hash : Hash160) (env : SatEnv) :
    satisfy (.ripemd160 hash) env =
      List.singleton <$> env.preimageFor (.ripemd160 hash) := by
  cases selected : env.preimageFor (.ripemd160 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem satisfy_hash160 (hash : Hash160) (env : SatEnv) :
    satisfy (.hash160 hash) env =
      List.singleton <$> env.preimageFor (.hash160 hash) := by
  cases selected : env.preimageFor (.hash160 hash) <;>
    simp [satisfy, hashCandidates, selected, List.singleton]

@[simp] theorem dissatisfy_zero (env : SatEnv) :
    dissatisfy .zero env = some [] := by
  rfl

@[simp] theorem dissatisfy_pk_k (key : PubKey) (env : SatEnv) :
    dissatisfy (.pk_k key) env = some [falseElement] := by
  rfl

@[simp] theorem dissatisfy_pk_h (key : PubKey) (env : SatEnv) :
    dissatisfy (.pk_h key) env = some [falseElement, key.bytes] := by
  rfl

@[simp] theorem dissatisfy_c_pk_k (key : PubKey) (env : SatEnv) :
    dissatisfy (.c (.pk_k key)) env = some [falseElement] := by
  rfl

@[simp] theorem dissatisfy_c_pk_h (key : PubKey) (env : SatEnv) :
    dissatisfy (.c (.pk_h key)) env = some [falseElement, key.bytes] := by
  rfl

@[simp] theorem dissatisfy_sha256 (hash : Hash256) (env : SatEnv) :
    dissatisfy (.sha256 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_hash256 (hash : Hash256) (env : SatEnv) :
    dissatisfy (.hash256 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_ripemd160 (hash : Hash160) (env : SatEnv) :
    dissatisfy (.ripemd160 hash) env = none := by
  rfl

@[simp] theorem dissatisfy_hash160 (hash : Hash160) (env : SatEnv) :
    dissatisfy (.hash160 hash) env = none := by
  rfl

@[simp] theorem satisfactionCandidates_c (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.c fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_c (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.c fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_c (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.c fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `a` changes execution stack placement, not candidate metadata or
    serialized witness order. -/
@[simp] theorem satisfactionCandidates_a
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.a fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_a (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.a fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_a (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.a fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `s` also preserves the candidate pair. Its singleton-argument
    typing requirement is enforced by semantic proofs rather than this raw-AST
    candidate function. -/
@[simp] theorem satisfactionCandidates_s
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.s fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_s (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.s fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_s (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.s fragment) env = dissatisfy fragment env := by
  rfl

/-- Wrapper `v` preserves the child's satisfaction candidate and removes its
    dissatisfaction candidate. -/
@[simp] theorem satisfactionCandidates_v
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.v fragment) env =
      { sat := (satisfactionCandidates fragment env).sat } := by
  rfl

@[simp] theorem satisfy_v (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.v fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_v (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.v fragment) env = none := by
  rfl

/-- Wrapper `n` preserves candidates; its opcode-level proof separately
    requires the child's exact Script-number result. -/
@[simp] theorem satisfactionCandidates_n
    (fragment : CoreFragment) (env : SatEnv) :
    satisfactionCandidates (.n fragment) env =
      satisfactionCandidates fragment env := by
  rfl

@[simp] theorem satisfy_n (fragment : CoreFragment) (env : SatEnv) :
    satisfy (.n fragment) env = satisfy fragment env := by
  rfl

@[simp] theorem dissatisfy_n (fragment : CoreFragment) (env : SatEnv) :
    dissatisfy (.n fragment) env = dissatisfy fragment env := by
  rfl

-- TODO(theorem): Extend satisfaction and dissatisfaction correctness through
-- wrappers `d`/`j`, connectives, thresholds, `multi`, and `multi_a`.
-- TODO: Analyze non-malleable satisfaction (unique canonical witness)

end LeanMiniscript.Miniscript
