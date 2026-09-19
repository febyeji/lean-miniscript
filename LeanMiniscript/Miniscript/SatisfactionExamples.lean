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

/-- Connectives remain outside this slice. -/
example : dissatisfy (.or_i .zero .one) unavailableEnv = none := by rfl

end LeanMiniscript.Miniscript
