import LeanMiniscript.Miniscript.Witness

/-! Witness candidates, selection metadata and exact-count threshold selection. -/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

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

/-- Append a branch selector in serialized witness order without changing any
    selection metadata. -/
def withSelector (candidate : SatisfactionCandidate)
    (selector : StackElement) : SatisfactionCandidate :=
  { candidate with witness := candidate.witness.withSelector selector }

/-- Mark a possible witness DONTUSE while preserving its witness, HASSIG flag,
    and canonical/non-canonical origin. -/
def markDontUse (candidate : SatisfactionCandidate) : SatisfactionCandidate :=
  { candidate with status := .dontUse }

/-- Record that a witness comes from a non-canonical table row. Its usability
    and HASSIG classification are independent and remain unchanged. -/
def markNonCanonical
    (candidate : SatisfactionCandidate) : SatisfactionCandidate :=
  { candidate with origin := .nonCanonical }

/-- Mark an overcomplete table row. BIP 379 treats such a row as both DONTUSE
    and non-canonical while retaining its concrete witness and HASSIG flag. -/
def markOvercomplete
    (candidate : SatisfactionCandidate) : SatisfactionCandidate :=
  { candidate with status := .dontUse, origin := .nonCanonical }

/-- Choose the lower-cost candidate, retaining the left candidate on a tie. -/
private def cheaperOrLeft
    (left right : SatisfactionCandidate) : SatisfactionCandidate :=
  if left.cost ≤ right.cost then left else right

/-- Binary BIP 379 candidate selection.

    A unique no-HASSIG candidate wins unchanged. Two no-HASSIG candidates make
    the cheaper witness DONTUSE. When both candidates have HASSIG, usable
    candidates take precedence over DONTUSE candidates, followed by witness
    cost. Cost ties retain the left candidate. Candidate origin is descriptive
    metadata and does not itself affect selection. -/
def select (left right : SatisfactionCandidate) : SatisfactionCandidate :=
  match left.hasSig, right.hasSig with
  | false, false => (cheaperOrLeft left right).markDontUse
  | false, true => left
  | true, false => right
  | true, true =>
      match left.status, right.status with
      | .usable, .dontUse => left
      | .dontUse, .usable => right
      | .usable, .usable | .dontUse, .dontUse => cheaperOrLeft left right

/-- Candidate selection has a signature exactly when both competing choices
    have signatures. A lone unsigned choice wins; two unsigned choices remain
    unsigned while becoming `DONTUSE`. -/
@[simp] theorem select_hasSig (left right : SatisfactionCandidate) :
    (left.select right).hasSig = (left.hasSig && right.hasSig) := by
  cases leftHasSig : left.hasSig <;> cases rightHasSig : right.hasSig
  · simp [select, cheaperOrLeft, leftHasSig, rightHasSig]
    split <;> simp_all [markDontUse]
  · simp [select, leftHasSig, rightHasSig]
  · simp [select, leftHasSig, rightHasSig]
  · cases leftStatus : left.status <;> cases rightStatus : right.status <;>
      simp [select, cheaperOrLeft, leftHasSig, rightHasSig,
        leftStatus, rightStatus]
    all_goals split <;> simp_all

@[simp] theorem withSelector_witness
    (candidate : SatisfactionCandidate) (selector : StackElement) :
    (candidate.withSelector selector).witness =
      candidate.witness.withSelector selector := by
  rfl

@[simp] theorem withSelector_hasSig
    (candidate : SatisfactionCandidate) (selector : StackElement) :
    (candidate.withSelector selector).hasSig = candidate.hasSig := by
  rfl

@[simp] theorem withSelector_status
    (candidate : SatisfactionCandidate) (selector : StackElement) :
    (candidate.withSelector selector).status = candidate.status := by
  rfl

@[simp] theorem withSelector_origin
    (candidate : SatisfactionCandidate) (selector : StackElement) :
    (candidate.withSelector selector).origin = candidate.origin := by
  rfl

@[simp] theorem markDontUse_witness (candidate : SatisfactionCandidate) :
    candidate.markDontUse.witness = candidate.witness := by
  rfl

@[simp] theorem markDontUse_hasSig (candidate : SatisfactionCandidate) :
    candidate.markDontUse.hasSig = candidate.hasSig := by
  rfl

@[simp] theorem markDontUse_status (candidate : SatisfactionCandidate) :
    candidate.markDontUse.status = .dontUse := by
  rfl

@[simp] theorem markDontUse_origin (candidate : SatisfactionCandidate) :
    candidate.markDontUse.origin = candidate.origin := by
  rfl

@[simp] theorem markNonCanonical_witness (candidate : SatisfactionCandidate) :
    candidate.markNonCanonical.witness = candidate.witness := by
  rfl

@[simp] theorem markNonCanonical_hasSig (candidate : SatisfactionCandidate) :
    candidate.markNonCanonical.hasSig = candidate.hasSig := by
  rfl

@[simp] theorem markNonCanonical_status (candidate : SatisfactionCandidate) :
    candidate.markNonCanonical.status = candidate.status := by
  rfl

@[simp] theorem markNonCanonical_origin (candidate : SatisfactionCandidate) :
    candidate.markNonCanonical.origin = .nonCanonical := by
  rfl

@[simp] theorem markOvercomplete_witness (candidate : SatisfactionCandidate) :
    candidate.markOvercomplete.witness = candidate.witness := by
  rfl

@[simp] theorem markOvercomplete_hasSig (candidate : SatisfactionCandidate) :
    candidate.markOvercomplete.hasSig = candidate.hasSig := by
  rfl

@[simp] theorem markOvercomplete_status (candidate : SatisfactionCandidate) :
    candidate.markOvercomplete.status = .dontUse := by
  rfl

@[simp] theorem markOvercomplete_origin (candidate : SatisfactionCandidate) :
    candidate.markOvercomplete.origin = .nonCanonical := by
  rfl

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

/-- Add a branch selector to every possible witness. Impossibility and all
    candidate metadata are preserved. -/
def withSelector : CandidateResult → StackElement → CandidateResult
  | .impossible, _ => .impossible
  | .candidate value, selector => .candidate (value.withSelector selector)

/-- Mark every possible result DONTUSE without changing its witness, HASSIG
    flag, or origin. -/
def markDontUse : CandidateResult → CandidateResult
  | .impossible => .impossible
  | .candidate value => .candidate value.markDontUse

/-- Mark every possible result non-canonical without changing its witness,
    HASSIG flag, or status. -/
def markNonCanonical : CandidateResult → CandidateResult
  | .impossible => .impossible
  | .candidate value => .candidate value.markNonCanonical

/-- Mark every possible result as an overcomplete BIP 379 row. The witness and
    HASSIG flag are retained, status becomes DONTUSE, and origin becomes
    non-canonical. -/
def markOvercomplete : CandidateResult → CandidateResult
  | .impossible => .impossible
  | .candidate value => .candidate value.markOvercomplete

/-- Keep a possible candidate only when the first element consumed at runtime
    has nonzero byte length. Witnesses are stored in reverse runtime order, so
    the check is performed after `Witness.toInitialStack`. -/
def requireNonemptyRuntimeTop : CandidateResult → CandidateResult
  | .impossible => .impossible
  | .candidate value =>
      match value.witness.toInitialStack with
      | [] => .impossible
      | top :: _ => if top.size = 0 then .impossible else .candidate value

/-- Select between two BIP 379 alternatives. Impossibility is an identity;
    possible alternatives use `SatisfactionCandidate.select`. -/
def select : CandidateResult → CandidateResult → CandidateResult
  | .impossible, right => right
  | left, .impossible => left
  | .candidate left, .candidate right => .candidate (left.select right)

/-- Extract every concrete witness, including one marked `DONTUSE`. -/
def witness? : CandidateResult → Option Witness
  | .impossible => none
  | .candidate value => some value.witness

/-- Project a witness unless it is marked DONTUSE. This only enforces the
    recursive candidate boundary; top-level HASSIG policy is a later step. -/
def usableWitness? : CandidateResult → Option Witness
  | .impossible => none
  | .candidate value =>
      match value.status with
      | .usable => some value.witness
      | .dontUse => none

/-- Project a final top-level satisfaction witness. BIP 379 requires the
    already-selected candidate to be usable and to contain a signature. This
    check happens after selection and never chooses a different alternative. -/
def finalWitness? : CandidateResult → Option Witness
  | .impossible => none
  | .candidate value =>
      match value.status, value.hasSig with
      | .usable, true => some value.witness
      | _, _ => none

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

@[simp] theorem usable_finalWitness? (witness : Witness) :
    (usable witness true).finalWitness? = some witness := by
  rfl

@[simp] theorem usable_without_sig_finalWitness? (witness : Witness) :
    (usable witness false).finalWitness? = none := by
  rfl

@[simp] theorem dontUse_finalWitness? (witness : Witness) (hasSig : Bool)
    (origin : CandidateOrigin) :
    (dontUse witness hasSig origin).finalWitness? = none := by
  cases hasSig <;> rfl

@[simp] theorem impossible_finalWitness? :
    (impossible : CandidateResult).finalWitness? = none := by
  rfl

/-- A final witness is exactly the witness of the selected usable HASSIG
    candidate. -/
theorem finalWitness?_eq_some_iff (result : CandidateResult)
    (witness : Witness) :
    result.finalWitness? = some witness ↔
      ∃ candidate,
        result = .candidate candidate ∧
        candidate.status = .usable ∧
        candidate.hasSig = true ∧
        candidate.witness = witness := by
  cases result with
  | impossible => simp [finalWitness?]
  | candidate candidate =>
      cases status : candidate.status <;>
        cases hasSig : candidate.hasSig <;>
          simp [finalWitness?, status, hasSig]

/-- Final projection only removes candidates from the ordinary usable
    projection. -/
theorem finalWitness?_some_usableWitness {result : CandidateResult}
    {witness : Witness} (selected : result.finalWitness? = some witness) :
    result.usableWitness? = some witness := by
  rw [finalWitness?_eq_some_iff] at selected
  obtain ⟨candidate, rfl, status, _, rfl⟩ := selected
  simp [usableWitness?, status]

@[simp] theorem impossible_select (right : CandidateResult) :
    select .impossible right = right := by
  rfl

@[simp] theorem select_impossible (left : CandidateResult) :
    select left .impossible = left := by
  cases left <;> rfl

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

namespace CandidatePair

/-- Select satisfaction and dissatisfaction alternatives independently. -/
def select (left right : CandidatePair) : CandidatePair where
  sat := left.sat.select right.sat
  dsat := left.dsat.select right.dsat

@[simp] theorem select_sat (left right : CandidatePair) :
    (select left right).sat = left.sat.select right.sat := by
  rfl

@[simp] theorem select_dsat (left right : CandidatePair) :
    (select left right).dsat = left.dsat.select right.dsat := by
  rfl

/-- Extend an exact-count candidate table by one child. Entry `j` records the
    best candidate that satisfies exactly `j` children processed so far. The
    dissatisfaction transition keeps the count, while the satisfaction
    transition increments it. `CandidateResult.select` applies the BIP 379
    non-malleability rules independently within each count state.

    `previous.combine child` preserves fragment execution order: earlier
    children execute first, while the resulting witness remains in serialized
    (reverse runtime) order. -/
def extendCounts (states : List CandidateResult)
    (child : CandidatePair) : List CandidateResult :=
  List.zipWith CandidateResult.select
    (states.map (fun previous => previous.combine child.dsat) ++ [.impossible])
    (.impossible :: states.map (fun previous => previous.combine child.sat))

/-- Dynamic-programming table whose entry `j` is the selected candidate for
    satisfying exactly `j` children. The empty prefix has one possible state:
    zero satisfactions with the empty witness. -/
def countCandidates (children : List CandidatePair) : List CandidateResult :=
  children.foldl extendCounts [.usable [] false]

/-- Select the candidate satisfying exactly `count` children. An index beyond
    the table is impossible. -/
def selectExactly (count : Nat)
    (children : List CandidatePair) : CandidateResult :=
  (countCandidates children).getD count .impossible

@[simp] theorem extendCounts_length
    (states : List CandidateResult) (child : CandidatePair) :
    (extendCounts states child).length = states.length + 1 := by
  simp [extendCounts]

@[simp] theorem countCandidates_nil :
    countCandidates [] = [.usable [] false] := by
  rfl

@[simp] theorem countCandidates_append
    (children : List CandidatePair) (child : CandidatePair) :
    countCandidates (children ++ [child]) =
      extendCounts (countCandidates children) child := by
  simp [countCandidates, List.foldl_append]

@[simp] theorem countCandidates_length (children : List CandidatePair) :
    (countCandidates children).length = children.length + 1 := by
  unfold countCandidates
  have foldLength : ∀ (remaining : List CandidatePair)
      (states : List CandidateResult),
      (remaining.foldl extendCounts states).length =
        states.length + remaining.length := by
    intro remaining
    induction remaining with
    | nil => intro states; simp
    | cons child remaining ih =>
        intro states
        simp only [List.foldl_cons]
        rw [ih, extendCounts_length]
        simp [Nat.add_comm, Nat.add_left_comm]
  simpa [Nat.add_comm] using foldLength children [.usable [] false]

@[simp] theorem selectExactly_eq_getD
    (count : Nat) (children : List CandidatePair) :
    selectExactly count children =
      (countCandidates children).getD count .impossible := by
  rfl

/-- Within the table bounds, exact-count selection is ordinary indexed
    retrieval. -/
theorem selectExactly_eq_getElem
    (count : Nat) (children : List CandidatePair)
    (inBounds : count < (countCandidates children).length) :
    selectExactly count children = (countCandidates children)[count] := by
  rw [selectExactly, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem inBounds]
  rfl

/-- More requested satisfactions than children is an impossible state. -/
theorem selectExactly_eq_impossible_of_lt
    (count : Nat) (children : List CandidatePair)
    (tooLarge : children.length < count) :
    selectExactly count children = .impossible := by
  rw [selectExactly, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none]
  · rfl
  · rw [countCandidates_length]
    omega

/-- Appending one child performs exactly one table transition before indexed
    retrieval. -/
@[simp] theorem selectExactly_append
    (count : Nat) (children : List CandidatePair) (child : CandidatePair) :
    selectExactly count (children ++ [child]) =
      (extendCounts (countCandidates children) child).getD count .impossible := by
  simp [selectExactly]

@[simp] theorem selectExactly_nil_zero :
    selectExactly 0 [] = .usable [] false := by
  rfl

@[simp] theorem selectExactly_nil_succ (count : Nat) :
    selectExactly (count + 1) [] = .impossible := by
  simp [selectExactly]

@[simp] theorem selectExactly_one_zero (child : CandidatePair) :
    selectExactly 0 [child] = child.dsat := by
  cases child with
  | mk sat dsat =>
      cases dsat with
      | impossible => rfl
      | candidate value =>
          cases value with
          | mk witness hasSig status origin =>
              cases status <;> cases origin <;> simp [selectExactly,
                countCandidates, extendCounts, CandidateResult.combine,
                CandidateResult.usable, SatisfactionCandidate.combine,
                CandidateStatus.combine, CandidateOrigin.combine]

@[simp] theorem selectExactly_one_one (child : CandidatePair) :
    selectExactly 1 [child] = child.sat := by
  cases child with
  | mk sat dsat =>
      cases sat with
      | impossible => rfl
      | candidate value =>
          cases value with
          | mk witness hasSig status origin =>
              cases status <;> cases origin <;> simp [selectExactly,
                countCandidates, extendCounts, CandidateResult.combine,
                CandidateResult.usable, SatisfactionCandidate.combine,
                CandidateStatus.combine, CandidateOrigin.combine]

/-- Select the threshold dissatisfaction from an exact-count table. Count zero
    is the canonical all-dissatisfied row. Every positive count other than the
    satisfying threshold is a possible overcomplete row, so it retains its
    witness and HASSIG flag while becoming DONTUSE and non-canonical. -/
def thresholdDissatisfaction (threshold : Nat)
    (states : List CandidateResult) : CandidateResult :=
  match states with
  | [] => .impossible
  | canonical :: positiveCounts =>
      (positiveCounts.zipIdx 1).foldl
        (fun selected entry =>
          if entry.2 = threshold then selected
          else selected.select entry.1.markOvercomplete)
        canonical

end CandidatePair

end LeanMiniscript.Miniscript
