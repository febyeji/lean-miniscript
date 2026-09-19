import LeanMiniscript.Miniscript.SatisfactionCandidateProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def firstChoice : CandidatePair where
  sat := .usable [trueElement] true
  dsat := .usable [] false

private def secondChoice : CandidatePair where
  dsat := .usable [falseElement] false

/-- Exact-count provenance retains the source child order even though the wire
    witness stores the later child's block first. -/
example : ∃ frames,
    CandidatePair.ChoiceTrace [firstChoice, secondChoice] 1 frames
      [falseElement, trueElement] := by
  apply CandidatePair.selectExactly_choiceTrace
  rfl

/-- The same trace exposes the source-order satisfaction bits, whose sum is
    the selected exact count. -/
example : ∃ truths frames,
    CandidatePair.ChoiceFrames [firstChoice, secondChoice] truths frames ∧
      (truths.map Bool.toNat).sum = 1 := by
  obtain ⟨frames, trace⟩ := CandidatePair.selectExactly_choiceTrace
    (children := [firstChoice, secondChoice]) (count := 1)
    (witness := [falseElement, trueElement]) (by rfl)
  obtain ⟨truths, choices, countEq⟩ := trace.toChoiceFrames
  exact ⟨truths, frames, choices, countEq⟩

/-- A retained overcomplete threshold row remains inspectable through `witness?`
    but cannot cross the public usable-witness boundary. -/
example :
    (CandidatePair.thresholdDissatisfaction 2
      [.impossible, .usable [trueElement] true]).witness? =
        some [trueElement] ∧
      (CandidatePair.thresholdDissatisfaction 2
        [.impossible, .usable [trueElement] true]).usableWitness? = none := by
  exact ⟨rfl, rfl⟩

/-- Marking the only positive-count row overcomplete cannot manufacture a
    usable witness when the canonical count-zero head is impossible. -/
example {witness : Witness}
    (selected :
      (CandidatePair.thresholdDissatisfaction 2
        [.impossible, .usable [trueElement] true]).usableWitness? =
          some witness) : False := by
  have source :=
    CandidatePair.thresholdDissatisfaction_usableWitness_source selected
  simp at source

end LeanMiniscript.Miniscript
