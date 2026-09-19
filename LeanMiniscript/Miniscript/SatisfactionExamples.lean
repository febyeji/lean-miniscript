import LeanMiniscript.Miniscript.SatisfactionProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def key : PubKey := ⟨⟨#[2, 3]⟩⟩
private def signature : StackElement := ⟨#[48, 1]⟩

private def unavailableEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  txCtx := { version := 2, locktime := 100, sequence := 50, sigHash := ⟨#[]⟩ }

private def signingEnv : SatEnv where
  signatureFor := fun _ => some signature
  preimageFor := fun _ => none
  txCtx := unavailableEnv.txCtx

private def firstWitness : Witness := [⟨#[0x01]⟩, ⟨#[0x02]⟩]
private def secondWitness : Witness := [⟨#[0x03]⟩]

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

example : satisfy (.c (.pk_k key)) unavailableEnv = none := by rfl

/-- The canonical empty signature is selected without consulting availability. -/
example : dissatisfy (.c (.pk_k key)) unavailableEnv = some [falseElement] := by
  rfl

example : satisfy (.older 40) unavailableEnv = some [] := by native_decide
example : satisfy (.older 60) unavailableEnv = none := by native_decide
example : satisfy (.after 90) unavailableEnv = some [] := by native_decide
example : satisfy (.after 110) unavailableEnv = none := by native_decide

/-- Basic scope does not silently claim support for wrappers or connectives. -/
example : satisfy (.n .one) unavailableEnv = none := by rfl
example : dissatisfy (.or_i .zero .one) unavailableEnv = none := by rfl

end LeanMiniscript.Miniscript
