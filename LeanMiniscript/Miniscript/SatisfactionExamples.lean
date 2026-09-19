import LeanMiniscript.Miniscript.SatisfactionProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def key : PubKey := ⟨⟨#[2, 3]⟩⟩
private def signature : StackElement := ⟨#[48, 1]⟩
private def preimage32 : StackElement :=
  ⟨(List.replicate 32 0x11).toArray⟩
private def nonPreimage32 : StackElement :=
  ⟨(List.replicate 32 0x22).toArray⟩
private def hashTarget : Hash256 :=
  ⟨⟨(List.replicate 32 0xaa).toArray⟩⟩

private def unavailableEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := { version := 2, locktime := 100, sequence := 50, sigHash := ⟨#[]⟩ }

private def signingEnv : SatEnv where
  signatureFor := fun _ => some signature
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def preimageEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => some preimage32
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def completeEnv : SatEnv where
  signatureFor := fun _ => some signature
  preimageFor := fun _ => some preimage32
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def firstWitness : Witness := [⟨#[0x01]⟩, ⟨#[0x02]⟩]
private def secondWitness : Witness := [⟨#[0x03]⟩]
private def alternateTruthy : StackElement := ⟨#[0x02]⟩
private def nonemptyFalsey : StackElement := ⟨#[0x80]⟩

/-- Sequential composition puts the first fragment's arguments on top of the
    runtime stack while retaining Bitcoin's bottom-first wire order. -/
example :
    Witness.toInitialStack (Witness.combine firstWitness secondWitness) =
      Witness.toInitialStack firstWitness ++
        Witness.toInitialStack secondWitness := by
  simp

/-- A branch selector is the next item consumed after wire-order conversion. -/
example :
    Witness.toInitialStack (Witness.withSelector firstWitness trueElement) =
      trueElement :: Witness.toInitialStack firstWitness := by
  simp

/-- Candidate construction records the witness independently of its computed
    cost. -/
example :
    (CandidateResult.usable [falseElement, trueElement] false) =
      .candidate {
        witness := [falseElement, trueElement]
        hasSig := false } := by
  rfl

example :
    ({ witness := [falseElement, trueElement]
       hasSig := false } : SatisfactionCandidate).cost = 3 := by
  native_decide

/-- Full wire size additionally includes the outer witness item-count prefix. -/
example : Witness.wireSize [falseElement, trueElement] = 4 := by
  native_decide

/-- Candidate cost composes additively in fragment execution order. -/
example :
    Witness.candidateCost (Witness.combine firstWitness secondWitness) =
      Witness.candidateCost firstWitness +
        Witness.candidateCost secondWitness := by
  simp

/-- DONTUSE candidates remain available to proof-facing composition, while
    `usableWitness?` removes them independently of later top-level policy. -/
example :
    (CandidateResult.dontUse [falseElement] false .canonical).witness? =
      some [falseElement] ∧
    (CandidateResult.dontUse [falseElement] false .canonical).usableWitness? =
      none := by
  decide

/-- DONTUSE and canonicality are independent classifications. Canonical hash
    dissatisfactions and non-canonical overcomplete paths can both be DONTUSE. -/
example :
    CandidateResult.dontUse [falseElement] false .canonical =
      .candidate {
        witness := [falseElement]
        hasSig := false
        status := .dontUse
        origin := .canonical } ∧
    CandidateResult.dontUse [falseElement] false .nonCanonical =
      .candidate {
        witness := [falseElement]
        hasSig := false
        status := .dontUse
        origin := .nonCanonical } := by
  constructor <;> rfl

/-- Candidate composition propagates signature presence and DONTUSE. -/
example :
    let first : SatisfactionCandidate := {
      witness := firstWitness
      hasSig := true }
    let second : SatisfactionCandidate := {
      witness := secondWitness
      hasSig := false
      status := .dontUse
      origin := .nonCanonical }
    (first.combine second).hasSig = true ∧
      (first.combine second).status = .dontUse ∧
      (first.combine second).origin = .nonCanonical := by
  decide

/-! ## Shared BIP 379 selection algebra -/

/-- Impossibility is an identity on either side of candidate selection. -/
example :
    CandidateResult.select .impossible
        (.usable [falseElement] false) = .usable [falseElement] false ∧
      CandidateResult.select (.usable [falseElement] false)
        .impossible = .usable [falseElement] false := by
  constructor <;> rfl

/-- A unique no-HASSIG candidate wins unchanged, including an existing
    DONTUSE classification. -/
example :
    CandidateResult.select
        (.dontUse [signature] false .canonical)
        (.usable [] true) =
      .dontUse [signature] false .canonical ∧
    CandidateResult.select
        (.usable [] true)
        (.dontUse [signature] false .canonical) =
      .dontUse [signature] false .canonical := by
  constructor <;> rfl

/-- Two no-HASSIG alternatives retain the cheaper witness and its origin, but
    the result becomes DONTUSE. -/
example :
    CandidateResult.select
        (.usable [signature] false)
        (CandidateResult.markNonCanonical
          (CandidateResult.usable [falseElement] false)) =
      .dontUse [falseElement] false .nonCanonical := by
  rfl

/-- Folding two no-HASSIG alternatives first keeps their cheapest witness
    DONTUSE when a HASSIG alternative is considered afterward. -/
example :
    CandidateResult.select
        (CandidateResult.select
          (.usable [signature] false)
          (.usable [falseElement] false))
        (.usable [] true) =
      .dontUse [falseElement] false .canonical := by
  rfl

/-- An interleaved left fold still recognizes both no-HASSIG alternatives. -/
example :
    CandidateResult.select
        (CandidateResult.select
          (.usable [signature] false)
          (.usable [] true))
        (.usable [falseElement] false) =
      .dontUse [falseElement] false .canonical := by
  rfl

/-- One no-HASSIG candidate added after two HASSIG candidates wins unchanged. -/
example :
    CandidateResult.select
        (CandidateResult.select
          (.dontUse [falseElement] true .canonical)
          (.usable [signature] true))
        (.dontUse [alternateTruthy] false .nonCanonical) =
      .dontUse [alternateTruthy] false .nonCanonical := by
  rfl

/-- Among three HASSIG candidates, usable beats cheaper DONTUSE and the
    cheapest usable candidate wins. -/
example :
    CandidateResult.select
        (CandidateResult.select
          (.dontUse [] true .canonical)
          (.usable [signature] true))
        (.usable [falseElement] true) =
      .usable [falseElement] true := by
  rfl

/-- Equal-cost no-HASSIG alternatives retain the left witness and origin. -/
example :
    CandidateResult.select
        (.usable [trueElement] false)
        (CandidateResult.markNonCanonical
          (CandidateResult.usable [alternateTruthy] false)) =
      .dontUse [trueElement] false .canonical := by
  rfl

/-- With two HASSIG alternatives, usability takes precedence over cost. -/
example :
    CandidateResult.select
        (.dontUse [falseElement] true .canonical)
        (CandidateResult.markNonCanonical
          (CandidateResult.usable [signature] true)) =
      CandidateResult.markNonCanonical
        (CandidateResult.usable [signature] true) := by
  rfl

/-- Candidates with equal HASSIG/status classification use cost next. -/
example :
    CandidateResult.select
        (.usable [signature] true)
        (CandidateResult.markNonCanonical
          (CandidateResult.usable [falseElement] true)) =
      CandidateResult.markNonCanonical
        (CandidateResult.usable [falseElement] true) ∧
    CandidateResult.select
        (.dontUse [signature] true .canonical)
        (.dontUse [falseElement] true .nonCanonical) =
      .dontUse [falseElement] true .nonCanonical := by
  constructor <;> rfl

/-- Adding a selector preserves HASSIG, DONTUSE, and origin metadata. -/
example :
    (CandidateResult.dontUse [falseElement] true .nonCanonical).withSelector
        trueElement =
      CandidateResult.dontUse [falseElement, trueElement] true
        .nonCanonical := by
  rfl

/-- Runtime-top filtering observes the last serialized witness item. -/
example :
    CandidateResult.requireNonemptyRuntimeTop
        (CandidateResult.usable [falseElement, trueElement] false) =
      CandidateResult.usable [falseElement, trueElement] false ∧
    CandidateResult.requireNonemptyRuntimeTop
        (CandidateResult.usable [trueElement, falseElement] false) =
      CandidateResult.impossible ∧
    CandidateResult.requireNonemptyRuntimeTop
        (CandidateResult.usable [] false) = CandidateResult.impossible := by
  constructor
  · rfl
  · constructor <;> rfl

/-- Non-canonical and overcomplete transformations remain distinct from a
    canonical DONTUSE such as a hash dissatisfaction. -/
example :
    CandidateResult.markNonCanonical
        (CandidateResult.dontUse [nonPreimage32] false .canonical) =
      CandidateResult.dontUse [nonPreimage32] false .nonCanonical ∧
    (CandidateResult.usable [signature] true).markOvercomplete =
      CandidateResult.dontUse [signature] true .nonCanonical := by
  constructor <;> rfl

/-- Candidate pairs select their two result classes independently. -/
example :
    CandidatePair.select
        { dsat := CandidateResult.usable [falseElement] false }
        { sat := CandidateResult.usable [signature] true } =
      { sat := CandidateResult.usable [signature] true
        dsat := CandidateResult.usable [falseElement] false } := by
  rfl

/-! ## Shared exact-count candidate tables -/

private def countItemA : StackElement := ⟨#[0xa1]⟩
private def countItemB : StackElement := ⟨#[0xb2]⟩
private def countItemC : StackElement := ⟨#[0xc3]⟩

private def uniqueCountA : CandidatePair where
  sat := .usable [countItemA] true
  dsat := .usable [] false

private def uniqueCountB : CandidatePair where
  sat := .usable [countItemB] true
  dsat := .usable [] false

private def uniqueCountC : CandidatePair where
  dsat := .usable [countItemC] false

/-- The seed represents the unique zero-of-zero choice; extending it by one
    child exposes that child's dissatisfaction and satisfaction in order. -/
example : CandidatePair.countCandidates [] = [.usable [] false] := by
  rfl

example : CandidatePair.countCandidates [uniqueCountA] =
    [uniqueCountA.dsat, uniqueCountA.sat] := by
  rfl

/-- Only the first two children can be satisfied, so the two-of-three state is
    their satisfaction followed by the last child's dissatisfaction. -/
example : CandidatePair.selectExactly 2
      [uniqueCountA, uniqueCountB, uniqueCountC] =
    .usable [countItemC, countItemB, countItemA] true := by
  rfl

private def costlyCountA : CandidatePair where
  sat := .usable [signature] true
  dsat := .usable [] false

private def cheapCountB : CandidatePair where
  sat := .usable [countItemB] true
  dsat := .usable [] false

private def cheapestCountC : CandidatePair where
  sat := .usable [falseElement] true
  dsat := .usable [] false

/-- When every two-of-three path is available, additive candidate cost picks
    the two cheapest satisfaction witnesses. -/
example : CandidatePair.selectExactly 2
      [costlyCountA, cheapCountB, cheapestCountC] =
    .usable [falseElement, countItemB] true := by
  rfl

private def tiedCountA : CandidatePair where
  sat := .usable [countItemA] true
  dsat := .usable [] false

private def tiedCountB : CandidatePair where
  sat := .usable [countItemB] true
  dsat := .usable [] false

private def tiedCountC : CandidatePair where
  sat := .usable [countItemC] true
  dsat := .usable [] false

/-- Equal-cost paths retain the existing left state, making the left fold
    deterministic. -/
example : CandidatePair.selectExactly 2
      [tiedCountA, tiedCountB, tiedCountC] =
    .usable [countItemB, countItemA] true := by
  rfl

/-- An exact count with too few possible satisfaction choices is impossible. -/
example : CandidatePair.selectExactly 2 [uniqueCountA, uniqueCountC] =
    .impossible := by
  rfl

/-- Counts beyond the table are impossible independently of child
    availability. -/
example : CandidatePair.selectExactly 4
      [tiedCountA, tiedCountB, tiedCountC] = .impossible := by
  apply CandidatePair.selectExactly_eq_impossible_of_lt
  decide

private def noSigCountA : CandidatePair where
  sat := .usable [countItemA] false
  dsat := .usable [] false

private def noSigCountB : CandidatePair where
  sat := .usable [countItemB] false
  dsat := .usable [] false

/-- Competing no-HASSIG paths use the ordinary selection rule within the
    one-satisfaction state: the equal-cost left path is retained and DONTUSE. -/
example : CandidatePair.selectExactly 1 [noSigCountA, noSigCountB] =
    .dontUse [countItemA] false .canonical := by
  rfl

private def metadataCountA : CandidatePair where
  sat := .usable [countItemA] true

private def metadataCountB : CandidatePair where
  sat := .dontUse [countItemB] false .nonCanonical

/-- Exact-count composition propagates a selected child's DONTUSE and origin
    metadata without changing its witness or HASSIG contribution. -/
example : CandidatePair.selectExactly 2 [metadataCountA, metadataCountB] =
    .dontUse [countItemB, countItemA] true .nonCanonical := by
  rfl

private def orderedCountA : CandidatePair where
  sat := .usable firstWitness true

private def orderedCountB : CandidatePair where
  sat := .usable secondWitness true

/-- Child blocks remain in reverse execution order on the wire and become
    execution order after conversion to the initial runtime stack. -/
example :
    (CandidatePair.selectExactly 2
      [orderedCountA, orderedCountB]).witness? =
        some (Witness.combine firstWitness secondWitness) ∧
      (CandidatePair.selectExactly 2
        [orderedCountA, orderedCountB]).witness?.map Witness.toInitialStack =
        some (Witness.toInitialStack firstWitness ++
          Witness.toInitialStack secondWitness) := by
  constructor <;> rfl

example : (satisfactionCandidates .one unavailableEnv).sat.usableWitness? =
    some [] := by rfl

example : (satisfactionCandidates .zero unavailableEnv).dsat.usableWitness? =
    some [] := by rfl

example : satisfy .one unavailableEnv = some [] := by rfl
example : satisfy .zero unavailableEnv = none := by rfl
example : dissatisfy .zero unavailableEnv = some [] := by rfl
example : dissatisfy .one unavailableEnv = none := by rfl

/-- A signature is emitted as one serialized-order witness item. -/
example : satisfy (.c (.pk_k key)) signingEnv = some [signature] := by rfl

example : satisfy (.pk_k key) signingEnv = some [signature] := by rfl

example : (satisfactionCandidates (.pk_k key) signingEnv).sat =
    CandidateResult.usable [signature] true := by
  rfl

example : satisfy (.c (.pk_k key)) unavailableEnv = none := by rfl

/-- The canonical empty signature is selected without consulting availability. -/
example : dissatisfy (.c (.pk_k key)) unavailableEnv = some [falseElement] := by
  rfl

/-- `pk_h` reveals the key after the signature in serialized witness order,
    which puts the key above the signature on the runtime stack. -/
example : satisfy (.pk_h key) signingEnv = some [signature, key.bytes] := by
  rfl

example :
    Witness.toInitialStack [signature, key.bytes] = [key.bytes, signature] := by
  rfl

example : dissatisfy (.pk_h key) unavailableEnv =
    some [falseElement, key.bytes] := by
  rfl

example : (satisfactionCandidates (.pk_h key) signingEnv).sat =
      CandidateResult.usable [signature, key.bytes] true ∧
    (satisfactionCandidates (.pk_h key) signingEnv).dsat =
      CandidateResult.usable [falseElement, key.bytes] false := by
  constructor <;> rfl

/-- Wrapper `c` preserves the complete child candidate pair, including its
    HASSIG, DONTUSE, and origin metadata. -/
example : satisfactionCandidates (.c (.pk_h key)) signingEnv =
    satisfactionCandidates (.pk_h key) signingEnv := by
  rfl

/-- Available hash preimages are ordinary selectable candidates. -/
example : satisfy (.sha256 hashTarget) preimageEnv = some [preimage32] := by
  rfl

example : satisfy (.sha256 hashTarget) unavailableEnv = none := by
  rfl

/-- Hash dissatisfactions are canonical table rows retained as raw witnesses,
    but DONTUSE prevents their public projection. -/
example :
    (satisfactionCandidates (.sha256 hashTarget) unavailableEnv).dsat =
      CandidateResult.dontUse [nonPreimage32] false .canonical := by
  rfl

example :
    (satisfactionCandidates (.sha256 hashTarget) unavailableEnv).dsat.witness? =
        some [nonPreimage32] ∧
      (satisfactionCandidates (.sha256 hashTarget)
        unavailableEnv).dsat.usableWitness? = none ∧
      dissatisfy (.sha256 hashTarget) unavailableEnv = none := by
  decide

/-- The semantic relation exposes the same 32-byte premise enforced by the
    compiled hashlock prefix. -/
example {preimage : StackElement}
    (matching : (HashLock.sha256 hashTarget).Matches preimage) :
    preimage.size = 32 :=
  matching.1

example : satisfy (.older 40) unavailableEnv = some [] := by native_decide
example : satisfy (.older 60) unavailableEnv = none := by native_decide
example : satisfy (.after 90) unavailableEnv = some [] := by native_decide
example : satisfy (.after 110) unavailableEnv = none := by native_decide

/-- Linear wrappers preserve the child's serialized witness and complete
    satisfaction candidate metadata. -/
example :
    satisfactionCandidates (.a (.sha256 hashTarget)) preimageEnv =
        satisfactionCandidates (.sha256 hashTarget) preimageEnv ∧
      satisfactionCandidates (.s (.sha256 hashTarget)) preimageEnv =
        satisfactionCandidates (.sha256 hashTarget) preimageEnv ∧
      satisfactionCandidates (.n (.sha256 hashTarget)) preimageEnv =
        satisfactionCandidates (.sha256 hashTarget) preimageEnv := by
  exact ⟨rfl, rfl, rfl⟩

/-- Raw hash dissatisfaction remains canonical DONTUSE through `a`, `s`, and
    `n`, while their public dissatisfaction projections remain unavailable. -/
example :
    (satisfactionCandidates (.a (.sha256 hashTarget)) unavailableEnv).dsat =
        CandidateResult.dontUse [nonPreimage32] false .canonical ∧
      (satisfactionCandidates (.s (.sha256 hashTarget)) unavailableEnv).dsat =
        CandidateResult.dontUse [nonPreimage32] false .canonical ∧
      (satisfactionCandidates (.n (.sha256 hashTarget)) unavailableEnv).dsat =
        CandidateResult.dontUse [nonPreimage32] false .canonical ∧
      dissatisfy (.a (.sha256 hashTarget)) unavailableEnv = none ∧
      dissatisfy (.s (.sha256 hashTarget)) unavailableEnv = none ∧
      dissatisfy (.n (.sha256 hashTarget)) unavailableEnv = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Wrapper `v` retains only satisfaction; a child's raw dissatisfaction is
    discarded instead of leaking through either projection. -/
example :
    (satisfactionCandidates (.v (.sha256 hashTarget)) preimageEnv).sat =
        (satisfactionCandidates (.sha256 hashTarget) preimageEnv).sat ∧
      (satisfactionCandidates (.v (.sha256 hashTarget)) unavailableEnv).dsat =
        .impossible ∧
      dissatisfy (.v (.sha256 hashTarget)) unavailableEnv = none := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Straight-line connective candidates -/

/-- `and_v` stores the second child's witness before the first child's witness,
    while runtime reversal restores fragment execution order. Its retained
    dissatisfaction is non-canonical and propagates the hash DONTUSE marker. -/
example :
    satisfactionCandidates
        (.and_v (.v (.c (.pk_k key))) (.sha256 hashTarget)) completeEnv = {
      sat := CandidateResult.usable [preimage32, signature] true
      dsat := CandidateResult.dontUse [nonPreimage32, signature] true
        .nonCanonical } ∧
      Witness.toInitialStack [preimage32, signature] = [signature, preimage32] ∧
      satisfy (.and_v (.v (.c (.pk_k key))) (.sha256 hashTarget)) completeEnv =
        some [preimage32, signature] ∧
      dissatisfy (.and_v (.v (.c (.pk_k key))) (.sha256 hashTarget)) completeEnv =
        none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `and_b` evaluates all three dissatisfaction rows in fixed left-fold order.
    Here the canonical and first overcomplete no-HASSIG rows tie in cost, so the
    canonical hash DONTUSE witness stays selected. -/
example :
    satisfactionCandidates
        (.and_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv = {
      sat := CandidateResult.usable [preimage32, signature] true
      dsat := CandidateResult.dontUse [nonPreimage32, falseElement] false
        .canonical } ∧
      Witness.toInitialStack [preimage32, signature] = [signature, preimage32] ∧
      satisfy (.and_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv =
        some [preimage32, signature] ∧
      dissatisfy (.and_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv =
        none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `or_b` selects its unique no-HASSIG satisfaction and propagates the raw hash
    DONTUSE dissatisfaction. Both witnesses retain second-then-first wire order. -/
example :
    satisfactionCandidates
        (.or_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv = {
      sat := CandidateResult.usable [preimage32, falseElement] false
      dsat := CandidateResult.dontUse [nonPreimage32, falseElement] false
        .canonical } ∧
      Witness.toInitialStack [preimage32, falseElement] =
        [falseElement, preimage32] ∧
      satisfy (.or_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv =
        some [preimage32, falseElement] ∧
      dissatisfy (.or_b (.c (.pk_k key)) (.a (.sha256 hashTarget))) completeEnv =
        none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The three overcomplete rows used by `and_b` and `or_b` retain their exact
    witnesses and HASSIG classification while becoming DONTUSE/non-canonical. -/
example :
    (((satisfactionCandidates (.c (.pk_k key)) completeEnv).dsat.combine
        (satisfactionCandidates (.a (.sha256 hashTarget)) completeEnv).sat)
      |>.markOvercomplete) =
        CandidateResult.dontUse [preimage32, falseElement] false .nonCanonical ∧
    (((satisfactionCandidates (.c (.pk_k key)) completeEnv).sat.combine
        (satisfactionCandidates (.a (.sha256 hashTarget)) completeEnv).dsat)
      |>.markOvercomplete) =
        CandidateResult.dontUse [nonPreimage32, signature] true .nonCanonical ∧
    (((satisfactionCandidates (.c (.pk_k key)) completeEnv).sat.combine
        (satisfactionCandidates (.a (.sha256 hashTarget)) completeEnv).sat)
      |>.markOvercomplete) =
        CandidateResult.dontUse [preimage32, signature] true .nonCanonical := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Conditional connective candidates -/

/-- Canonical selectors have distinct serialized costs. When both `or_i`
    branches satisfy without HASSIG, selection keeps the cheaper false branch
    and marks it DONTUSE. -/
example :
    Witness.candidateCost [trueElement] = 2 ∧
      Witness.candidateCost [falseElement] = 1 ∧
      (satisfactionCandidates (.or_i .one .one) unavailableEnv).sat =
        CandidateResult.dontUse [falseElement] false .canonical ∧
      satisfy (.or_i .one .one) unavailableEnv = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `or_i` appends its selector in wire order, so runtime conversion puts the
    selector above the selected branch arguments. -/
example :
    satisfactionCandidates (.or_i .one .zero) unavailableEnv = {
      sat := CandidateResult.usable [trueElement] false
      dsat := CandidateResult.usable [falseElement] false } ∧
      Witness.toInitialStack [trueElement] = [trueElement] ∧
      satisfy (.or_i .one .zero) unavailableEnv = some [trueElement] ∧
      dissatisfy (.or_i .one .zero) unavailableEnv = some [falseElement] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `or_c` chooses either the direct signature path or a false first-child
    selector followed by the V child. The latter wire witness reverses to put
    the selector above the hash preimage at runtime. -/
example :
    satisfy
        (.or_c (.c (.pk_k key)) (.v (.sha256 hashTarget))) signingEnv =
        some [signature] ∧
      satisfy
        (.or_c (.c (.pk_k key)) (.v (.sha256 hashTarget))) preimageEnv =
        some [preimage32, falseElement] ∧
      Witness.toInitialStack [preimage32, falseElement] =
        [falseElement, preimage32] := by
  exact ⟨rfl, rfl, rfl⟩

/-- A canonical hash DONTUSE candidate remains available through `or_c`
    selection but is removed by the public projection. -/
example :
    (satisfactionCandidates
      (.or_c (.sha256 hashTarget) (.v .one)) unavailableEnv).sat =
        CandidateResult.dontUse [nonPreimage32] false .canonical ∧
      satisfy (.or_c (.sha256 hashTarget) (.v .one)) unavailableEnv = none := by
  exact ⟨rfl, rfl⟩

/-- `or_d` has a direct satisfying path, an alternate satisfying path whose
    arguments precede the false selector on the wire, and a composed canonical
    dissatisfaction. -/
example :
    satisfy (.or_d (.c (.pk_k key)) .zero) signingEnv =
        some [signature] ∧
      satisfy
        (.or_d (.c (.pk_k key)) (.sha256 hashTarget)) preimageEnv =
        some [preimage32, falseElement] ∧
      dissatisfy
        (.or_d (.c (.pk_k key)) (.c (.pk_k key))) unavailableEnv =
        some [falseElement, falseElement] := by
  exact ⟨rfl, rfl, rfl⟩

/-- `andor` stores the selected child before the guard on the wire. The
    alternate dissatisfaction is non-canonical but keeps its inherited usable
    status rather than being marked overcomplete. -/
example :
    satisfy
        (.andor (.c (.pk_k key)) (.sha256 hashTarget) .zero) completeEnv =
        some [preimage32, signature] ∧
      Witness.toInitialStack [preimage32, signature] =
        [signature, preimage32] ∧
      satisfy
        (.andor .zero .zero (.sha256 hashTarget)) preimageEnv =
        some [preimage32] ∧
      (satisfactionCandidates
        (.andor (.c (.pk_k key)) (.c (.pk_k key)) .one) signingEnv).dsat =
        .candidate {
          witness := [falseElement, signature]
          hasSig := true
          origin := .nonCanonical } ∧
      dissatisfy
        (.andor (.c (.pk_k key)) (.c (.pk_k key)) .one) signingEnv =
        some [falseElement, signature] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Wrapper `a` restores the protected element above a hash result. -/
example {preimage : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage) :
    WExecution (.a (.sha256 hashTarget)) [preimage] trueElement
      .savedFirst flags ctx := by
  simpa [HashLock.fragment] using
    (BExecution.a (hash_satisfaction_execution matching))

/-- Wrapper `s` requires one child argument and leaves its result above the
    protected element. -/
example {preimage : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage) :
    WExecution (.s (.sha256 hashTarget)) [preimage] trueElement
      .resultFirst flags ctx := by
  simpa [HashLock.fragment] using
    (BExecution.s (hash_satisfaction_execution matching))

/-- Wrapper `v` consumes the truthy result and leaves the arbitrary suffix
    unchanged. -/
example {flags : ScriptFlags} {ctx : TxContext} :
    VExecution (.v .one) [] flags ctx := by
  exact BExecution.v (one_execution flags ctx) (by native_decide)

/-- Wrapper `n` needs an explicit Script-number decode even when the child
    result's truth value is already known. -/
example :
    BExecutionOutcome (.n .one) [] true ({} : ScriptFlags)
      unavailableEnv.txCtx := by
  apply BExecution.nOutcome (one_execution {} unavailableEnv.txCtx)
      (value := 1)
  · rfl
  · decide

/-- Wrapper `d` appends a canonical true selector to satisfaction and provides
    its canonical false dissatisfaction. -/
example :
    satisfactionCandidates (.d (.v .one)) unavailableEnv =
        { sat := CandidateResult.usable [trueElement] false
          dsat := CandidateResult.usable [falseElement] false } ∧
      satisfy (.d (.v .one)) unavailableEnv = some [trueElement] ∧
      dissatisfy (.d (.v .one)) unavailableEnv = some [falseElement] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The `d(v(1))` satisfaction executes over every surrounding stack. -/
example {flags : ScriptFlags} {ctx : TxContext} :
    BExecution (.d (.v .one)) [trueElement] trueElement flags ctx := by
  exact (BExecution.v (one_execution flags ctx) (by native_decide)).d

example {flags : ScriptFlags} {ctx : TxContext} :
    BExecution (.d (.v .one)) [falseElement] falseElement flags ctx := by
  exact d_dissatisfaction_execution (.v .one) flags ctx

/-- Adding `d`'s selector preserves metadata and charges its serialized item
    to candidate cost. -/
example :
    let candidate : SatisfactionCandidate := {
      witness := [signature]
      hasSig := true
      status := .dontUse
      origin := .nonCanonical }
    let selected := candidate.withSelector trueElement
    selected.witness = [signature, trueElement] ∧
      selected.hasSig = true ∧ selected.status = .dontUse ∧
      selected.origin = .nonCanonical ∧ selected.cost = 5 := by
  native_decide

/-- Wrapper `j` preserves child satisfaction unchanged. -/
example : satisfy (.j (.sha256 hashTarget)) preimageEnv =
    some [preimage32] := by
  rfl

/-- A matching nonempty hash preimage passes through `j`; the exact size
    decoder premise remains visible at the opcode boundary. -/
example {preimage : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (decoded : decodeScriptNum (scriptNat preimage.size) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat preimage.size)) :
    BExecutionOutcome (.j (.sha256 hashTarget)) [preimage] true flags ctx := by
  apply BExecutionOutcome.j
  · exact ⟨trueElement, hash_satisfaction_execution matching, by native_decide⟩
  · rw [matching.1]
    decide
  · exact decoded

/-- The child's empty runtime-top dissatisfaction alternative is filtered, so
    `j` selects its canonical zero item. -/
example :
    (satisfactionCandidates (.j (.c (.pk_k key))) unavailableEnv).dsat =
        CandidateResult.usable [falseElement] false ∧
      dissatisfy (.j (.c (.pk_k key))) unavailableEnv =
        some [falseElement] := by
  constructor <;> rfl

example {flags : ScriptFlags} {ctx : TxContext} :
    BExecution (.j (.c (.pk_k key))) [falseElement] falseElement flags ctx := by
  exact j_dissatisfaction_execution (.c (.pk_k key)) flags ctx

/-- A nonempty no-HASSIG child alternative makes `j`'s selected
    dissatisfaction DONTUSE, even when the cheaper canonical witness wins. -/
example :
    (satisfactionCandidates (.j (.sha256 hashTarget)) unavailableEnv).dsat =
      CandidateResult.dontUse [falseElement] false .canonical := by
  rfl

/-- A nonempty HASSIG alternative loses to the unique canonical no-HASSIG
    candidate without changing that candidate's metadata. -/
example :
    (CandidateResult.usable [falseElement] false).select
        ((CandidateResult.usable [signature] true)
          |>.requireNonemptyRuntimeTop
          |>.markNonCanonical) =
      CandidateResult.usable [falseElement] false := by
  rfl

/-- The filter observes runtime order, so an empty final serialized item makes
    the child alternative impossible. -/
example :
    ((CandidateResult.usable [signature, falseElement] true)
      |>.requireNonemptyRuntimeTop
      |>.markNonCanonical) = CandidateResult.impossible := by
  rfl

/-- Runtime-top filtering checks byte length rather than Script truthiness. -/
example :
    castToBool nonemptyFalsey = false ∧
      (CandidateResult.usable [nonemptyFalsey] false
        |>.requireNonemptyRuntimeTop) =
        CandidateResult.usable [nonemptyFalsey] false := by
  constructor
  · native_decide
  · rfl

/-- `j` retains a raw DONTUSE witness for composition, while the public
    dissatisfaction projection removes it. -/
example :
    (satisfactionCandidates (.j (.sha256 hashTarget))
      unavailableEnv).dsat.witness? =
        some [falseElement] ∧
      (satisfactionCandidates (.j (.sha256 hashTarget))
        unavailableEnv).dsat.usableWitness? = none ∧
      dissatisfy (.j (.sha256 hashTarget)) unavailableEnv = none := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Straight-line connective execution -/

/-- `and_v` preserves each possible result base of its second child. -/
example :
    BExecution (.and_v (.v .one) .zero) [] falseElement
      ({} : ScriptFlags) unavailableEnv.txCtx ∧
    KExecution (.and_v (.v .one) (.pk_k key)) [] key.bytes
      ({} : ScriptFlags) unavailableEnv.txCtx ∧
    VExecution (.and_v (.v .one) (.v .one)) []
      ({} : ScriptFlags) unavailableEnv.txCtx := by
  have first : VExecution (.v .one) [] ({} : ScriptFlags)
      unavailableEnv.txCtx :=
    BExecution.v (one_execution {} unavailableEnv.txCtx) (by native_decide)
  exact ⟨
    first.and_v_b (zero_execution {} unavailableEnv.txCtx),
    first.and_v_k (pk_k_execution key {} unavailableEnv.txCtx),
    first.and_v_v
      (BExecution.v (one_execution {} unavailableEnv.txCtx) (by native_decide))⟩

/-- Canonical Boolean elements satisfy the exact binary decoding premise in
    both W stack orders. A five-byte numeric operand exposes the required
    overflow boundary instead of being accepted from truthiness alone. -/
example :
    WStackOrder.BinaryDecoded .savedFirst ({} : ScriptFlags)
        trueElement falseElement 1 0 ∧
      WStackOrder.BinaryDecoded .resultFirst ({} : ScriptFlags)
        falseElement trueElement 0 1 ∧
      decodeBinaryScriptNums ({} : ScriptFlags)
        ⟨#[1, 0, 0, 0, 0]⟩ falseElement = .error .scriptNumOverflow := by
  exact ⟨rfl, rfl, rfl⟩

/-- Saved-first W output covers all Boolean combinations for `and_b`. -/
example :
    BExecutionOutcome (.and_b .one (.a .one)) [] true
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome (.and_b .one (.a .zero)) [] false
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome (.and_b .zero (.a .one)) [] false
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome (.and_b .zero (.a .zero)) [] false
        ({} : ScriptFlags) unavailableEnv.txCtx := by
  constructor
  · exact BExecution.and_bOutcome
      (one_execution {} unavailableEnv.txCtx)
      (BExecution.a (one_execution {} unavailableEnv.txCtx))
      (firstValue := 1) (secondValue := 1) (by rfl) rfl
  constructor
  · exact BExecution.and_bOutcome
      (one_execution {} unavailableEnv.txCtx)
      (BExecution.a (zero_execution {} unavailableEnv.txCtx))
      (firstValue := 1) (secondValue := 0) (by rfl) rfl
  constructor
  · exact BExecution.and_bOutcome
      (zero_execution {} unavailableEnv.txCtx)
      (BExecution.a (one_execution {} unavailableEnv.txCtx))
      (firstValue := 0) (secondValue := 1) (by rfl) rfl
  · exact BExecution.and_bOutcome
      (zero_execution {} unavailableEnv.txCtx)
      (BExecution.a (zero_execution {} unavailableEnv.txCtx))
      (firstValue := 0) (secondValue := 0) (by rfl) rfl

/-- Hashlocks supply the required Bd/Wd children for a well-typed `or_b` while
    saved-first W output covers all four Boolean combinations. -/
example {firstPreimage firstNonPreimage secondPreimage secondNonPreimage : StackElement}
    (firstMatches : (HashLock.sha256 hashTarget).Matches firstPreimage)
    (firstMismatches : (HashLock.sha256 hashTarget).Mismatches firstNonPreimage)
    (secondMatches : (HashLock.sha256 hashTarget).Matches secondPreimage)
    (secondMismatches : (HashLock.sha256 hashTarget).Mismatches secondNonPreimage) :
    BExecutionOutcome
        (.or_b (HashLock.sha256 hashTarget).fragment
          (.a (HashLock.sha256 hashTarget).fragment))
        [firstPreimage, secondPreimage] true
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome
        (.or_b (HashLock.sha256 hashTarget).fragment
          (.a (HashLock.sha256 hashTarget).fragment))
        [firstPreimage, secondNonPreimage] true
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome
        (.or_b (HashLock.sha256 hashTarget).fragment
          (.a (HashLock.sha256 hashTarget).fragment))
        [firstNonPreimage, secondPreimage] true
        ({} : ScriptFlags) unavailableEnv.txCtx ∧
      BExecutionOutcome
        (.or_b (HashLock.sha256 hashTarget).fragment
          (.a (HashLock.sha256 hashTarget).fragment))
        [firstNonPreimage, secondNonPreimage] false
        ({} : ScriptFlags) unavailableEnv.txCtx := by
  constructor
  · exact BExecution.or_bOutcome
      (hash_satisfaction_execution firstMatches)
      (BExecution.a (hash_satisfaction_execution secondMatches))
      (firstValue := 1) (secondValue := 1) (by rfl) rfl
  constructor
  · exact BExecution.or_bOutcome
      (hash_satisfaction_execution firstMatches)
      (BExecution.a (hash_dissatisfaction_execution secondMismatches))
      (firstValue := 1) (secondValue := 0) (by rfl) rfl
  constructor
  · exact BExecution.or_bOutcome
      (hash_dissatisfaction_execution firstMismatches)
      (BExecution.a (hash_satisfaction_execution secondMatches))
      (firstValue := 0) (secondValue := 1) (by rfl) rfl
  · exact BExecution.or_bOutcome
      (hash_dissatisfaction_execution firstMismatches)
      (BExecution.a (hash_dissatisfaction_execution secondMismatches))
      (firstValue := 0) (secondValue := 0) (by rfl) rfl

/-- Result-first W output feeds the operands to `OP_BOOLAND` in physical stack
    order while the theorem returns its canonical source-child order. -/
example {preimage : StackElement}
    (matching : (HashLock.sha256 hashTarget).Matches preimage) :
    BExecutionOutcome
      (.and_b .one (.s (HashLock.sha256 hashTarget).fragment)) [preimage] true
      ({} : ScriptFlags) unavailableEnv.txCtx := by
  exact BExecution.and_bOutcome
    (one_execution {} unavailableEnv.txCtx)
    (BExecution.s (hash_satisfaction_execution matching))
    (firstValue := 1) (secondValue := 1) (by rfl) rfl

/-- Result-first W output uses the corresponding OR commutativity path with the
    same well-typed Bd/Wd child bases. -/
example {preimage nonPreimage : StackElement}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    BExecutionOutcome
      (.or_b (HashLock.sha256 hashTarget).fragment
        (.s (HashLock.sha256 hashTarget).fragment))
      [preimage, nonPreimage] true
      ({} : ScriptFlags) unavailableEnv.txCtx := by
  exact BExecution.or_bOutcome
    (hash_satisfaction_execution matching)
    (BExecution.s (hash_dissatisfaction_execution mismatches))
    (firstValue := 1) (secondValue := 0) (by rfl) rfl

/-! ## Conditional connective execution -/

/-- A well-typed `or_c` uses a Bd hash guard and a V child. Its truthy path
    skips the child, while its false path executes and consumes the child. -/
example {preimage nonPreimage : StackElement} {flags : ScriptFlags}
    {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    VExecution
        (.or_c (HashLock.sha256 hashTarget).fragment (.v .one))
        [preimage] flags ctx ∧
      VExecution
        (.or_c (HashLock.sha256 hashTarget).fragment (.v .one))
        [nonPreimage] flags ctx := by
  constructor
  · exact (hash_satisfaction_execution matching).or_c_left
      (Or.inr trueElement_minimalIfArg) (by native_decide)
  · exact (hash_dissatisfaction_execution mismatches).or_c_right
      (Or.inr falseElement_minimalIfArg) (by native_decide)
      (BExecution.v (one_execution flags ctx) (by native_decide))

/-- A well-typed `or_d` preserves its truthy Bd selector directly and returns
    the B child's result after a false guard. -/
example {preimage nonPreimage : StackElement} {flags : ScriptFlags}
    {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    BExecution
        (.or_d (HashLock.sha256 hashTarget).fragment .zero)
        [preimage] trueElement flags ctx ∧
      BExecution
        (.or_d (HashLock.sha256 hashTarget).fragment .one)
        [nonPreimage] trueElement flags ctx := by
  constructor
  · exact (hash_satisfaction_execution matching).or_d_left
      (Or.inr trueElement_minimalIfArg) (by native_decide)
  · exact (hash_dissatisfaction_execution mismatches).or_d_right
      (Or.inr falseElement_minimalIfArg) (by native_decide)
      (one_execution flags ctx)

/-- Canonical `or_i` selectors support each result base with the same exact
    selector-above-arguments runtime order. -/
example {flags : ScriptFlags} {ctx : TxContext} :
    BExecution (.or_i .one .zero) [trueElement] trueElement flags ctx ∧
      BExecution (.or_i .one .zero) [falseElement] falseElement flags ctx ∧
      KExecution (.or_i (.pk_k key) (.pk_k key))
        [trueElement] key.bytes flags ctx ∧
      KExecution (.or_i (.pk_k key) (.pk_k key))
        [falseElement] key.bytes flags ctx ∧
      VExecution (.or_i (.v .one) (.v .one)) [trueElement] flags ctx ∧
      VExecution (.or_i (.v .one) (.v .one)) [falseElement] flags ctx := by
  constructor
  · exact BExecution.or_i_left (one_execution flags ctx)
  constructor
  · exact BExecution.or_i_right (zero_execution flags ctx)
  constructor
  · exact KExecution.or_i_left (pk_k_execution key flags ctx)
  constructor
  · exact KExecution.or_i_right (pk_k_execution key flags ctx)
  constructor
  · exact VExecution.or_i_left
      (BExecution.v (one_execution flags ctx) (by native_decide))
  · exact VExecution.or_i_right
      (BExecution.v (one_execution flags ctx) (by native_decide))

/-- The K-frame contract preserves an arbitrary downstream signature suffix
    after the canonical `or_i` selector has chosen a branch. -/
example :
    Eval (compile (.or_i (.pk_k key) (.pk_k key)))
      [trueElement, signature] [] ({} : ScriptFlags) unavailableEnv.txCtx
      (.success [key.bytes, signature] []) := by
  exact (KExecution.or_i_left
    (pk_k_execution key ({} : ScriptFlags) unavailableEnv.txCtx)) [signature] []

/-- A Bd hash guard selects well-typed B branches of `andor`: truth executes Y
    and false executes Z. -/
example {preimage nonPreimage : StackElement} {flags : ScriptFlags}
    {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    BExecution
        (.andor (HashLock.sha256 hashTarget).fragment .one .zero)
        [preimage] trueElement flags ctx ∧
      BExecution
        (.andor (HashLock.sha256 hashTarget).fragment .one .zero)
        [nonPreimage] falseElement flags ctx := by
  constructor
  · exact (hash_satisfaction_execution matching).andor_true
      (Or.inr trueElement_minimalIfArg) (by native_decide)
      (one_execution flags ctx)
  · exact (hash_dissatisfaction_execution mismatches).andor_false
      (Or.inr falseElement_minimalIfArg) (by native_decide)
      (zero_execution flags ctx)

/-- The same `andor` branch map preserves K outputs on both guard paths. -/
example {preimage nonPreimage : StackElement} {flags : ScriptFlags}
    {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    KExecution
        (.andor (HashLock.sha256 hashTarget).fragment
          (.pk_k key) (.pk_k key))
        [preimage] key.bytes flags ctx ∧
      KExecution
        (.andor (HashLock.sha256 hashTarget).fragment
          (.pk_k key) (.pk_k key))
        [nonPreimage] key.bytes flags ctx := by
  constructor
  · exact (hash_satisfaction_execution matching).andor_true
      (Or.inr trueElement_minimalIfArg) (by native_decide)
      (pk_k_execution key flags ctx)
  · exact (hash_dissatisfaction_execution mismatches).andor_false
      (Or.inr falseElement_minimalIfArg) (by native_decide)
      (pk_k_execution key flags ctx)

/-- The same `andor` branch map consumes well-typed V branches on both guard
    paths. -/
example {preimage nonPreimage : StackElement} {flags : ScriptFlags}
    {ctx : TxContext}
    (matching : (HashLock.sha256 hashTarget).Matches preimage)
    (mismatches : (HashLock.sha256 hashTarget).Mismatches nonPreimage) :
    VExecution
        (.andor (HashLock.sha256 hashTarget).fragment (.v .one) (.v .one))
        [preimage] flags ctx ∧
      VExecution
        (.andor (HashLock.sha256 hashTarget).fragment (.v .one) (.v .one))
        [nonPreimage] flags ctx := by
  constructor
  · exact VExecution.andor_true (hash_satisfaction_execution matching)
      (Or.inr trueElement_minimalIfArg) (by native_decide)
      (BExecution.v (one_execution flags ctx) (by native_decide))
  · exact VExecution.andor_false (hash_dissatisfaction_execution mismatches)
      (Or.inr falseElement_minimalIfArg) (by native_decide)
      (BExecution.v (one_execution flags ctx) (by native_decide))

/-! ## Threshold candidates and execution -/

private def signedB : CoreFragment := .c (.pk_k key)
private def signedW : CoreFragment := .a signedB
private def signedThreshold : CoreFragment :=
  .thresh 2 [signedB, signedW, signedW]

/-- The candidate fixture follows the threshold typing boundary: a Bdu first
    child, Wdu tails, and `1 ≤ k ≤ n`. -/
example : wellTyped .p2wsh signedThreshold := by
  refine ⟨_, HasType.thresh (X := signedB) (Xs := [signedW, signedW])
    (restTypes := [
      ⟨.W, { d := true, u := true }⟩,
      ⟨.W, { d := true, u := true }⟩])
    (HasType.c_wrap (HasType.pk_k key)) rfl rfl ?_ ?_ (by decide)
      (by decide)⟩
  · exact HasTypeList.cons
      (HasType.a_wrap (HasType.c_wrap (HasType.pk_k key)))
      (HasTypeList.cons
        (HasType.a_wrap (HasType.c_wrap (HasType.pk_k key)))
        HasTypeList.nil)
  · decide

/-- Equal-cost two-of-three paths retain the left path: the first two
    signatures satisfy while the third child uses its canonical zero. The
    canonical all-zero path is the threshold dissatisfaction. -/
example :
    (satisfactionCandidates signedThreshold signingEnv).sat =
        CandidateResult.usable
          [falseElement, signature, signature] true ∧
      (satisfactionCandidates signedThreshold signingEnv).dsat =
        CandidateResult.usable
          [falseElement, falseElement, falseElement] false ∧
      satisfy signedThreshold signingEnv =
        some [falseElement, signature, signature] ∧
      dissatisfy signedThreshold signingEnv =
        some [falseElement, falseElement, falseElement] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private def keyB : PubKey := ⟨⟨#[2, 4]⟩⟩
private def keyC : PubKey := ⟨⟨#[2, 5]⟩⟩

private def thresholdCostEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == key.bytes then some signature
    else if selectedKey.bytes == keyB.bytes then some countItemB
    else if selectedKey.bytes == keyC.bytes then some falseElement
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def costThreshold : CoreFragment :=
  .thresh 2
    [.c (.pk_k key), .a (.c (.pk_k keyB)), .a (.c (.pk_k keyC))]

/-- With three available two-of-three paths, additive cost selects the short
    signatures from the second and third children. -/
example : (satisfactionCandidates costThreshold thresholdCostEnv).sat =
    CandidateResult.usable [falseElement, countItemB, falseElement] true := by
  rfl

/-- Invalid raw thresholds have no candidates on either side. -/
example :
    satisfactionCandidates (.thresh 0 [signedB]) signingEnv = {} ∧
      satisfactionCandidates (.thresh 2 [signedB]) signingEnv = {} ∧
      satisfactionCandidates (.thresh 1 []) signingEnv = {} := by
  exact ⟨rfl, rfl, rfl⟩

/-- Multiple no-HASSIG one-of-two hash paths select a concrete representative
    but mark it DONTUSE. The inherited canonical origin remains distinct from
    overcomplete non-canonical rows. -/
example :
    (satisfactionCandidates
      (.thresh 1 [.sha256 hashTarget, .a (.sha256 hashTarget)])
      preimageEnv).sat =
        CandidateResult.dontUse [nonPreimage32, preimage32] false .canonical := by
  rfl

/-- If the canonical count-zero state is impossible, a possible wrong positive
    count remains available with overcomplete metadata. -/
example : CandidatePair.thresholdDissatisfaction 1
      [.impossible, .usable [countItemA] true,
        .dontUse [countItemB] true .canonical] =
    .dontUse [countItemB] true .nonCanonical := by
  rfl

/-- Exact-count witness blocks are serialized in reverse child order and turn
    back into source order on the runtime stack. -/
example :
    Witness.toInitialStack [falseElement, signature, signature] =
      Witness.toInitialStack [signature] ++
        Witness.toInitialStack [signature] ++
        Witness.toInitialStack [falseElement] := by
  rfl

/-- One execution fixture exercises saved-first `a`, result-first `s`, both
    explicit `OP_ADD` decodes, and the final byte-equality comparison. -/
example {firstPreimage secondPreimage thirdNonPreimage : StackElement}
    (firstMatches : (HashLock.sha256 hashTarget).Matches firstPreimage)
    (secondMatches : (HashLock.sha256 hashTarget).Matches secondPreimage)
    (thirdMismatches : (HashLock.sha256 hashTarget).Mismatches thirdNonPreimage) :
    BExecutionOutcome
      (.thresh 2 [(.sha256 hashTarget), .a (.sha256 hashTarget),
        .s (.sha256 hashTarget)])
      [firstPreimage, secondPreimage, thirdNonPreimage] true
      ({} : ScriptFlags) unavailableEnv.txCtx := by
  have tail : ThresholdTailExecution ({} : ScriptFlags) unavailableEnv.txCtx 1
      [.a (.sha256 hashTarget), .s (.sha256 hashTarget)]
      [[secondPreimage], [thirdNonPreimage]] 2 := by
    refine ThresholdTailExecution.cons (truth := true) (order := .savedFirst)
      (by simpa [HashLock.fragment, boolToElement] using
        BExecution.a (hash_satisfaction_execution secondMatches))
      (by
        change decodeBinaryScriptNums ({} : ScriptFlags) (scriptNat 1)
          trueElement = .ok (1, 1)
        rfl) ?_
    refine ThresholdTailExecution.cons (truth := false) (order := .resultFirst)
      (by simpa [HashLock.fragment, boolToElement] using
        BExecution.s (hash_dissatisfaction_execution thirdMismatches))
      (by
        change decodeBinaryScriptNums ({} : ScriptFlags) falseElement
          (scriptNat 2) = .ok (0, 2)
        rfl) ?_
    exact ThresholdTailExecution.nil 2
  exact BExecution.threshOutcome
    (threshold := 2) (first := .sha256 hashTarget)
    (fragments := [.a (.sha256 hashTarget), .s (.sha256 hashTarget)])
    (firstArgs := [firstPreimage])
    (argumentFrames := [[secondPreimage], [thirdNonPreimage]])
    (firstTruth := true) (total := 2)
    (by simpa [HashLock.fragment, boolToElement] using
      hash_satisfaction_execution firstMatches)
    tail (by native_decide)

/-- The all-dissatisfied path runs the same accumulator contract to zero and
    exercises the false `OP_EQUAL` branch for a two-of-three threshold. -/
example {firstNonPreimage secondNonPreimage thirdNonPreimage : StackElement}
    (firstMismatches : (HashLock.sha256 hashTarget).Mismatches firstNonPreimage)
    (secondMismatches : (HashLock.sha256 hashTarget).Mismatches secondNonPreimage)
    (thirdMismatches : (HashLock.sha256 hashTarget).Mismatches thirdNonPreimage) :
    BExecutionOutcome
      (.thresh 2 [(.sha256 hashTarget), .a (.sha256 hashTarget),
        .s (.sha256 hashTarget)])
      [firstNonPreimage, secondNonPreimage, thirdNonPreimage] false
      ({} : ScriptFlags) unavailableEnv.txCtx := by
  have tail : ThresholdTailExecution ({} : ScriptFlags) unavailableEnv.txCtx 0
      [.a (.sha256 hashTarget), .s (.sha256 hashTarget)]
      [[secondNonPreimage], [thirdNonPreimage]] 0 := by
    refine ThresholdTailExecution.cons (truth := false) (order := .savedFirst)
      (by simpa [HashLock.fragment, boolToElement] using
        BExecution.a (hash_dissatisfaction_execution secondMismatches))
      (by
        change decodeBinaryScriptNums ({} : ScriptFlags) (scriptNat 0)
          falseElement = .ok (0, 0)
        rfl) ?_
    refine ThresholdTailExecution.cons (truth := false) (order := .resultFirst)
      (by simpa [HashLock.fragment, boolToElement] using
        BExecution.s (hash_dissatisfaction_execution thirdMismatches))
      (by
        change decodeBinaryScriptNums ({} : ScriptFlags) falseElement
          (scriptNat 0) = .ok (0, 0)
        rfl) ?_
    exact ThresholdTailExecution.nil 0
  exact BExecution.threshOutcome
    (threshold := 2) (first := .sha256 hashTarget)
    (fragments := [.a (.sha256 hashTarget), .s (.sha256 hashTarget)])
    (firstArgs := [firstNonPreimage])
    (argumentFrames := [[secondNonPreimage], [thirdNonPreimage]])
    (firstTruth := false) (total := 0)
    (by simpa [HashLock.fragment, boolToElement] using
      hash_dissatisfaction_execution firstMismatches)
    tail (by native_decide)

/-! ## Legacy multisignature candidates and execution -/

private def multiKeyA : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0xa1).toArray⟩
private def multiKeyB : PubKey :=
  PubKey.ofBytes ⟨#[0x03] ++ (List.replicate 32 0xb2).toArray⟩
private def multiKeyC : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0xc3).toArray⟩

private def multiSigA : StackElement := ⟨#[0x31]⟩
private def multiSigB : StackElement := ⟨#[0x32]⟩
private def multiSigC : StackElement := ⟨#[0x33]⟩
private def costlyMultiSigA : StackElement := ⟨#[0x31, 0x32, 0x33]⟩

private def multiKeys : List PubKey := [multiKeyA, multiKeyB, multiKeyC]
private def twoOfThreeMulti : CoreFragment := .multi 2 multiKeys

private def multiACEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == multiKeyA.bytes then some multiSigA
    else if selectedKey.bytes == multiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def multiAllEqualEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == multiKeyA.bytes then some multiSigA
    else if selectedKey.bytes == multiKeyB.bytes then some multiSigB
    else if selectedKey.bytes == multiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def multiCostEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == multiKeyA.bytes then some costlyMultiSigA
    else if selectedKey.bytes == multiKeyB.bytes then some multiSigB
    else if selectedKey.bytes == multiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def multiAOnlyEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == multiKeyA.bytes then some multiSigA else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

/-- Exact-count selection runs in source key order, then legacy finalization
    prepends the CHECKMULTISIG dummy and writes selected signatures in source
    order. Runtime conversion puts signatures in decoder order above the dummy. -/
example :
    (satisfactionCandidates twoOfThreeMulti multiACEnv).sat =
        .usable [falseElement, multiSigA, multiSigC] true ∧
      satisfy twoOfThreeMulti multiACEnv =
        some [falseElement, multiSigA, multiSigC] ∧
      Witness.toInitialStack [falseElement, multiSigA, multiSigC] =
        [multiSigC, multiSigA, falseElement] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal-cost alternatives retain the earlier source keys. -/
example : (satisfactionCandidates twoOfThreeMulti multiAllEqualEnv).sat =
    .usable [falseElement, multiSigA, multiSigB] true := by
  rfl

/-- Candidate cost selects the two shorter signatures when all three keys are
    available, while the common dummy contributes equally to every path. -/
example : (satisfactionCandidates twoOfThreeMulti multiCostEnv).sat =
    .usable [falseElement, multiSigB, multiSigC] true := by
  rfl

/-- Fewer than `k` available signatures makes satisfaction impossible. The
    canonical dissatisfaction always supplies `k` empty signatures and the
    historical dummy. -/
example :
    (satisfactionCandidates twoOfThreeMulti multiAOnlyEnv).sat = .impossible ∧
      (satisfactionCandidates twoOfThreeMulti multiAOnlyEnv).dsat =
        .usable [falseElement, falseElement, falseElement] false ∧
      dissatisfy twoOfThreeMulti multiAOnlyEnv =
        some [falseElement, falseElement, falseElement] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Raw invalid legacy multisig forms expose no candidate on either side. -/
example :
    satisfactionCandidates (.multi 0 multiKeys) multiAllEqualEnv = {} ∧
      satisfactionCandidates (.multi 4 multiKeys) multiAllEqualEnv = {} ∧
      satisfactionCandidates
        (.multi 1 (List.replicate 21 multiKeyA)) multiAllEqualEnv = {} := by
  exact ⟨rfl, rfl, rfl⟩

/-- Legacy multisig is structurally valid with compressed P2WSH keys and is
    rejected at the Tapscript well-formedness boundary. -/
example :
    twoOfThreeMulti.WellFormed .p2wsh ∧
      ¬ twoOfThreeMulti.WellFormed .tapscript := by
  native_decide

private def multiFlags : ScriptFlags where
  strictEncoding := false

private def multiFalseFlags : ScriptFlags where
  strictEncoding := false
  nullFail := false

private def multiCtx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩
  sigVersion := .witnessV0

/-- The exact decoder helper fixes public keys, signatures, dummy, and the
    untouched suffix in their top-first runtime order. -/
example :
    decodeCheckMultiSigOperandsFor multiFlags multiCtx
      (scriptNat 3 :: [multiKeyC.bytes, multiKeyB.bytes, multiKeyA.bytes] ++
        scriptNat 2 :: [multiSigC, multiSigA, falseElement, countItemA]) =
      .ok {
        pubkeys := [multiKeyC.bytes, multiKeyB.bytes, multiKeyA.bytes]
        signatures := [multiSigC, multiSigA]
        dummy := some falseElement
        rest := [countItemA] } := by
  simpa [multiKeys] using
    (decodeCheckMultiSigOperandsFor_multi
      (threshold := 2) (keys := multiKeys)
      (signatures := [multiSigC, multiSigA]) (rest := [countItemA])
      (flags := multiFlags) (ctx := multiCtx)
      (by decide) (by decide) (by decide) rfl)

/-- Successful local execution uses the decoder's top-first signature order.
    Cryptographic verification remains an explicit premise. -/
example
    (verified : checkMultiSigFor checkSig multiFlags multiCtx
      [multiSigC, multiSigA]
      [multiKeyC.bytes, multiKeyB.bytes, multiKeyA.bytes] = .ok true) :
    BExecution twoOfThreeMulti
      [multiSigC, multiSigA, falseElement] trueElement multiFlags multiCtx := by
  simpa [twoOfThreeMulti, multiKeys, boolToElement] using
    BExecution.multi (threshold := 2) (keys := multiKeys)
      (signatures := [multiSigC, multiSigA]) (by decide) (by decide)
      (by decide) rfl verified (Or.inl rfl)

/-- With NULLFAIL disabled, a modeled failed check returns canonical false
    while preserving the same exact stack frame. -/
example
    (rejected : checkMultiSigFor checkSig multiFalseFlags multiCtx
      [multiSigC, multiSigA]
      [multiKeyC.bytes, multiKeyB.bytes, multiKeyA.bytes] = .ok false) :
    BExecution twoOfThreeMulti
      [multiSigC, multiSigA, falseElement] falseElement
      multiFalseFlags multiCtx := by
  apply BExecution.multiFalse (threshold := 2) (keys := multiKeys)
    (signatures := [multiSigC, multiSigA]) (by decide) (by decide)
    (by decide) rfl
  · simpa [multiKeys] using rejected
  · simp [nullFailSatisfied, multiFalseFlags]

/-- The canonical all-empty dissatisfaction discharges NULLFAIL even when the
    flag is active. -/
example
    (rejected : checkMultiSigFor checkSig multiFlags multiCtx
      [falseElement, falseElement]
      [multiKeyC.bytes, multiKeyB.bytes, multiKeyA.bytes] = .ok false) :
    BExecution twoOfThreeMulti
      [falseElement, falseElement, falseElement] falseElement
      multiFlags multiCtx := by
  apply multi_dissatisfaction_execution (threshold := 2) (keys := multiKeys)
    (by decide) (by decide) (by decide)
  simpa [multiKeys] using rejected

/-- Nonempty failed signatures violate NULLFAIL when enabled, and a nonempty
    historical dummy violates NULLDUMMY. -/
example :
    ¬ nullFailSatisfied multiFlags [multiSigC, multiSigA] ∧
      checkMultiSigDummy multiFlags (some trueElement) = .error .nullDummy := by
  constructor
  · intro satisfied
    rcases satisfied with disabled | empty
    · simp [multiFlags] at disabled
    · have zero := empty multiSigC (by simp)
      have nonzero : multiSigC.size ≠ 0 := by native_decide
      exact nonzero zero
  · simp [checkMultiSigDummy, nullDummySatisfied, multiFlags, stackElementEq,
      trueElement, falseElement]

/-! ## Tapscript multisignature candidates and execution -/

private def tapMultiKeyA : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0xa1).toArray⟩
private def tapMultiKeyB : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0xb2).toArray⟩
private def tapMultiKeyC : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0xc3).toArray⟩

private def tapMultiKeys : List PubKey :=
  [tapMultiKeyA, tapMultiKeyB, tapMultiKeyC]
private def twoOfThreeMultiA : CoreFragment := .multi_a 2 tapMultiKeys

private def tapMultiACEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == tapMultiKeyA.bytes then some multiSigA
    else if selectedKey.bytes == tapMultiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def tapMultiAllEqualEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == tapMultiKeyA.bytes then some multiSigA
    else if selectedKey.bytes == tapMultiKeyB.bytes then some multiSigB
    else if selectedKey.bytes == tapMultiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def tapMultiCostEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == tapMultiKeyA.bytes then some costlyMultiSigA
    else if selectedKey.bytes == tapMultiKeyB.bytes then some multiSigB
    else if selectedKey.bytes == tapMultiKeyC.bytes then some multiSigC
    else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

private def tapMultiAOnlyEnv : SatEnv where
  signatureFor := fun selectedKey =>
    if selectedKey.bytes == tapMultiKeyA.bytes then some multiSigA else none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => nonPreimage32
  txCtx := unavailableEnv.txCtx

/-- `multi_a` exact-count blocks need no legacy finalizer. Their reverse wire
    order becomes source execution order after the single witness reversal. -/
example :
    (satisfactionCandidates twoOfThreeMultiA tapMultiACEnv).sat =
        .usable [multiSigC, falseElement, multiSigA] true ∧
      satisfy twoOfThreeMultiA tapMultiACEnv =
        some [multiSigC, falseElement, multiSigA] ∧
      Witness.toInitialStack [multiSigC, falseElement, multiSigA] =
        [multiSigA, falseElement, multiSigC] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal-cost exact-count paths prefer earlier source keys. -/
example : (satisfactionCandidates twoOfThreeMultiA tapMultiAllEqualEnv).sat =
    .usable [falseElement, multiSigB, multiSigA] true := by
  rfl

/-- Additive cost selects the shorter second and third signatures. -/
example : (satisfactionCandidates twoOfThreeMultiA tapMultiCostEnv).sat =
    .usable [multiSigC, multiSigB, falseElement] true := by
  rfl

/-- Per-key and aggregate candidates keep the HASSIG distinction explicit;
    fewer than `k` available signatures makes only satisfaction impossible. -/
example :
    (multiAKeyChoice tapMultiKeyA tapMultiACEnv).sat =
        .usable [multiSigA] true ∧
      (multiAKeyChoice tapMultiKeyB tapMultiACEnv).dsat =
        .usable [falseElement] false ∧
      (satisfactionCandidates twoOfThreeMultiA tapMultiAOnlyEnv).sat =
        .impossible ∧
      (satisfactionCandidates twoOfThreeMultiA tapMultiAOnlyEnv).dsat =
        .usable [falseElement, falseElement, falseElement] false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Only the threshold relation is rejected. A 21-key raw `multi_a` remains
    candidate-valid because Tapscript has no legacy 20-key limit. -/
example :
    satisfactionCandidates (.multi_a 0 tapMultiKeys) tapMultiAllEqualEnv = {} ∧
      satisfactionCandidates (.multi_a 4 tapMultiKeys) tapMultiAllEqualEnv = {} ∧
      (satisfactionCandidates
          (.multi_a 1 (List.replicate 21 tapMultiKeyA))
          tapMultiAllEqualEnv).sat =
        .usable (List.replicate 20 falseElement ++ [multiSigA]) true ∧
      (satisfactionCandidates
          (.multi_a 1 (List.replicate 21 tapMultiKeyA))
          tapMultiAllEqualEnv).dsat =
        .usable (List.replicate 21 falseElement) false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- X-only keys make `multi_a` well formed in Tapscript, while the opcode
    encoding is rejected at the P2WSH well-formedness boundary. -/
example :
    twoOfThreeMultiA.WellFormed .tapscript ∧
      ¬ twoOfThreeMultiA.WellFormed .p2wsh := by
  native_decide

private def tapMultiFlags : ScriptFlags := {}

private def tapMultiCtx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩
  sigVersion := .tapscript

/-- Two true checks and one canonical empty signature execute to total two.
    The B frame quantifies over every main-stack suffix and alternate stack. -/
example {firstSignature thirdSignature : StackElement}
    (firstChecked : checkSigWithEncoding checkSig checkSchnorrSig tapMultiFlags
      tapMultiCtx firstSignature tapMultiKeyA.bytes = .ok true)
    (thirdChecked : checkSigWithEncoding checkSig checkSchnorrSig tapMultiFlags
      tapMultiCtx thirdSignature tapMultiKeyC.bytes = .ok true) :
    BExecution twoOfThreeMultiA
      [firstSignature, falseElement, thirdSignature]
      trueElement tapMultiFlags tapMultiCtx := by
  have tail : CheckSigAddTailExecution tapMultiFlags tapMultiCtx 1
      [tapMultiKeyB, tapMultiKeyC] [falseElement, thirdSignature] 2 := by
    refine CheckSigAddTailExecution.cons (truth := false) (by rfl) (by rfl) ?_
    refine CheckSigAddTailExecution.cons (truth := true) (by rfl)
      thirdChecked ?_
    exact CheckSigAddTailExecution.nil 2
  exact BExecution.multiATrue (threshold := 2) (firstKey := tapMultiKeyA)
    (keys := [tapMultiKeyB, tapMultiKeyC]) rfl firstChecked tail
    (by rfl) (by rfl)

/-- One true and two false checks exercise the false final NUMEQUAL branch. -/
example {firstSignature : StackElement}
    (firstChecked : checkSigWithEncoding checkSig checkSchnorrSig tapMultiFlags
      tapMultiCtx firstSignature tapMultiKeyA.bytes = .ok true) :
    BExecution twoOfThreeMultiA
      [firstSignature, falseElement, falseElement]
      falseElement tapMultiFlags tapMultiCtx := by
  have tail : CheckSigAddTailExecution tapMultiFlags tapMultiCtx 1
      [tapMultiKeyB, tapMultiKeyC] [falseElement, falseElement] 1 := by
    refine CheckSigAddTailExecution.cons (truth := false) (by rfl) (by rfl) ?_
    refine CheckSigAddTailExecution.cons (truth := false) (by rfl) (by rfl) ?_
    exact CheckSigAddTailExecution.nil 1
  exact BExecution.multiAFalse (threshold := 2) (firstKey := tapMultiKeyA)
    (keys := [tapMultiKeyB, tapMultiKeyC]) rfl firstChecked tail
    (by rfl) (by rfl)

/-- The canonical all-empty dissatisfaction remains at total zero and returns
    false for the positive threshold. -/
example :
    BExecution twoOfThreeMultiA
      [falseElement, falseElement, falseElement]
      falseElement tapMultiFlags tapMultiCtx := by
  apply multiA_dissatisfaction_execution (threshold := 2)
    (firstKey := tapMultiKeyA) (keys := [tapMultiKeyB, tapMultiKeyC])
    (flags := tapMultiFlags) (ctx := tapMultiCtx) rfl (by decide) (by rfl)
  · intro selectedKey member
    simp at member
    rcases member with rfl | rfl <;> rfl
  · rfl

private def nonTapMultiCtx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩
  sigVersion := .witnessV0

private def nonTapMultiFlags : ScriptFlags where
  strictEncoding := false

/-- Once the first CHECKSIG completes, the first CHECKSIGADD rejects a
    non-Tapscript execution before inspecting its operands. -/
example {firstSignature secondSignature : StackElement}
    (firstChecked : checkSigWithEncoding checkSig checkSchnorrSig
      nonTapMultiFlags nonTapMultiCtx firstSignature tapMultiKeyA.bytes =
        .ok false) :
    Eval (compile (.multi_a 1 [tapMultiKeyA, tapMultiKeyB]))
      [firstSignature, secondSignature] [] nonTapMultiFlags nonTapMultiCtx
      (.failure .badOpcode) := by
  simp only [compile, compileWithKeyHash, compileCheckSigAdd,
    compileCheckSigAddTail]
  apply Eval.pushData
  apply Eval.checksig_failure
  · exact firstChecked
  apply Eval.pushData
  exact Eval.checksigadd_unavailable _ _ _ _ _ (by decide)

private def invalidSchnorrSignature : StackElement := ⟨#[0x01]⟩

/-- Tapscript rejects a malformed nonempty Schnorr signature as an encoding
    error, while the canonical empty signature is an ordinary false result. -/
example :
    checkSigWithEncoding checkSig checkSchnorrSig tapMultiFlags tapMultiCtx
        invalidSchnorrSignature tapMultiKeyA.bytes = .error .schnorrSigSize ∧
      checkSigWithEncoding checkSig checkSchnorrSig tapMultiFlags tapMultiCtx
        falseElement tapMultiKeyA.bytes = .ok false := by
  constructor <;> rfl

/-- Truthiness alone does not discharge a child-produced selector's MINIMALIF
    premise when the flag is active. -/
example :
    castToBool nonMinimalTruthyElement = true ∧
      ¬ minimalIfSatisfied ({ minimalIf := true } : ScriptFlags)
        nonMinimalTruthyElement := by
  exact ⟨nonMinimalTruthyElement_truthy, by native_decide⟩

end LeanMiniscript.Miniscript
