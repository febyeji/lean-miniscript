import LeanMiniscript.Miniscript.Malleability
import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Validation
import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

theorem boolAnd3_eq_true (a b c : Bool) :
    (a && b && c) = true ↔ a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem boolAnd4_eq_true (a b c d : Bool) :
    (a && b && c && d) = true ↔
      a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem boolAnd5_eq_true (a b c d e : Bool) :
    (a && b && c && d && e) = true ↔
      a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem boolOr3_eq_true (a b c : Bool) :
    (a || b || c) = true ↔ a = true ∨ b = true ∨ c = true := by
  cases a <;> cases b <;> cases c <;> decide

/-!
# Candidate semantics for BIP 379 malleability modifiers

These predicates expose the candidate metadata used by the non-malleable
satisfaction algorithm. They deliberately speak about raw candidates, before
the public witness projections erase `HASSIG`, `DONTUSE`, and origin data.
-/

namespace CandidateResult

/-- Every raw candidate carried by the result contains a signature. -/
def Signed (result : CandidateResult) : Prop :=
  ∀ candidate, result = .candidate candidate → candidate.hasSig = true

/-- Every candidate which survives the `DONTUSE` filter came from a canonical
    BIP 379 table row. -/
def CanonicalWhenUsable (result : CandidateResult) : Prop :=
  ∀ candidate,
    result = .candidate candidate →
    candidate.status = .usable →
    candidate.origin = .canonical

/-- A unique unconditional candidate: it is signature-free, and whenever it
    survives `DONTUSE` selection it has canonical provenance. Keeping the
    status abstract is essential: competing unsigned rows may make the unique
    result `DONTUSE` while preserving the fact that no non-canonical row can
    become a usable output. -/
def Unconditional (result : CandidateResult) : Prop :=
  ∃ candidate,
    result = .candidate candidate ∧
    candidate.hasSig = false ∧
    result.CanonicalWhenUsable

theorem signed_impossible : (impossible : CandidateResult).Signed := by
  intro candidate impossible
  contradiction

theorem canonicalWhenUsable_impossible :
    (impossible : CandidateResult).CanonicalWhenUsable := by
  intro candidate impossible
  contradiction

theorem signed_usable (witness : Witness) :
    (usable witness true).Signed := by
  intro candidate equal
  cases equal
  rfl

theorem canonicalWhenUsable_usable (witness : Witness) (hasSig : Bool) :
    (usable witness hasSig).CanonicalWhenUsable := by
  intro candidate equal _
  cases equal
  rfl

theorem signed_dontUse (witness : Witness) (origin : CandidateOrigin) :
    (dontUse witness true origin).Signed := by
  intro candidate equal
  cases equal
  rfl

theorem canonicalWhenUsable_dontUse (witness : Witness) (hasSig : Bool)
    (origin : CandidateOrigin) :
    (dontUse witness hasSig origin).CanonicalWhenUsable := by
  intro candidate equal usable
  cases equal
  contradiction

theorem unconditional_usable (witness : Witness) :
    (usable witness false).Unconditional := by
  exact ⟨{ witness, hasSig := false }, rfl, rfl,
    canonicalWhenUsable_usable witness false⟩

theorem unconditional_dontUse (witness : Witness)
    (origin : CandidateOrigin) :
    (dontUse witness false origin).Unconditional := by
  exact ⟨{ witness, hasSig := false, status := .dontUse, origin }, rfl, rfl,
    canonicalWhenUsable_dontUse witness false origin⟩

theorem unconditional_of_dontUse (candidate : SatisfactionCandidate)
    (status : candidate.status = .dontUse)
    (hasSig : candidate.hasSig = false) :
    (CandidateResult.candidate candidate).Unconditional := by
  refine ⟨candidate, rfl, hasSig, ?_⟩
  intro selected equal usable
  cases equal
  rw [status] at usable
  contradiction

theorem Unconditional.canonicalWhenUsable {result : CandidateResult}
    (unconditional : result.Unconditional) : result.CanonicalWhenUsable := by
  obtain ⟨_, _, _, canonical⟩ := unconditional
  exact canonical

theorem Unconditional.notSigned {result : CandidateResult}
    (unconditional : result.Unconditional) : ¬ result.Signed := by
  intro signed
  obtain ⟨candidate, equal, noSignature, _⟩ := unconditional
  have hasSignature := signed candidate equal
  simp [noSignature] at hasSignature

theorem Signed.withSelector {result : CandidateResult}
    (signed : result.Signed) (selector : StackElement) :
    (result.withSelector selector).Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      intro candidate equal
      simp [CandidateResult.withSelector] at equal
      cases equal
      exact signed source rfl

theorem CanonicalWhenUsable.withSelector {result : CandidateResult}
    (canonical : result.CanonicalWhenUsable) (selector : StackElement) :
    (result.withSelector selector).CanonicalWhenUsable := by
  cases result with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate source =>
      intro candidate equal usable
      simp [CandidateResult.withSelector] at equal
      cases equal
      exact canonical source rfl usable

theorem Unconditional.withSelector {result : CandidateResult}
    (unconditional : result.Unconditional) (selector : StackElement) :
    (result.withSelector selector).Unconditional := by
  obtain ⟨candidate, rfl, hasSig, canonical⟩ := unconditional
  exact ⟨candidate.withSelector selector, rfl, by simpa using hasSig,
    canonical.withSelector selector⟩

theorem Signed.markNonCanonical {result : CandidateResult}
    (signed : result.Signed) : result.markNonCanonical.Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      intro candidate equal
      simp [CandidateResult.markNonCanonical] at equal
      cases equal
      exact signed source rfl

theorem Signed.markDontUse {result : CandidateResult}
    (signed : result.Signed) : result.markDontUse.Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      intro candidate equal
      simp [CandidateResult.markDontUse] at equal
      cases equal
      exact signed source rfl

theorem canonicalWhenUsable_markDontUse (result : CandidateResult) :
    result.markDontUse.CanonicalWhenUsable := by
  cases result with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate source =>
      intro candidate equal usable
      simp [CandidateResult.markDontUse] at equal
      cases equal
      simp at usable

theorem Signed.markOvercomplete {result : CandidateResult}
    (signed : result.Signed) : result.markOvercomplete.Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      intro candidate equal
      simp [CandidateResult.markOvercomplete] at equal
      cases equal
      exact signed source rfl

theorem Signed.requireNonemptyRuntimeTop {result : CandidateResult}
    (signed : result.Signed) : result.requireNonemptyRuntimeTop.Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      rcases source with ⟨witness, hasSig, status, origin⟩
      cases stackEq : witness.toInitialStack with
      | nil =>
          simpa [CandidateResult.requireNonemptyRuntimeTop, stackEq] using
            signed_impossible
      | cons top rest =>
          by_cases empty : top.size = 0
          · simpa [CandidateResult.requireNonemptyRuntimeTop, stackEq,
              empty] using signed_impossible
          · intro candidate equal
            simp [CandidateResult.requireNonemptyRuntimeTop, stackEq, empty] at equal
            cases equal
            exact signed _ rfl

theorem CanonicalWhenUsable.requireNonemptyRuntimeTop
    {result : CandidateResult} (canonical : result.CanonicalWhenUsable) :
    result.requireNonemptyRuntimeTop.CanonicalWhenUsable := by
  cases result with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate source =>
      rcases source with ⟨witness, hasSig, status, origin⟩
      cases stackEq : witness.toInitialStack with
      | nil =>
          simpa [CandidateResult.requireNonemptyRuntimeTop, stackEq] using
            canonicalWhenUsable_impossible
      | cons top rest =>
          by_cases empty : top.size = 0
          · simpa [CandidateResult.requireNonemptyRuntimeTop, stackEq,
              empty] using canonicalWhenUsable_impossible
          · intro candidate equal usable
            simp [CandidateResult.requireNonemptyRuntimeTop, stackEq, empty] at equal
            cases equal
            exact canonical _ rfl usable

theorem canonicalWhenUsable_markOvercomplete (result : CandidateResult) :
    result.markOvercomplete.CanonicalWhenUsable := by
  cases result with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate source =>
      intro candidate equal usable
      simp [CandidateResult.markOvercomplete] at equal
      cases equal
      simp at usable

theorem Signed.combine_left {left right : CandidateResult}
    (signed : left.Signed) : (left.combine right).Signed := by
  cases left with
  | impossible => exact signed_impossible
  | candidate leftCandidate =>
      cases right with
      | impossible => exact signed_impossible
      | candidate rightCandidate =>
          intro candidate equal
          simp [CandidateResult.combine] at equal
          cases equal
          simp [SatisfactionCandidate.combine, signed leftCandidate rfl]

theorem Signed.combine_right {left right : CandidateResult}
    (signed : right.Signed) : (left.combine right).Signed := by
  cases left with
  | impossible => exact signed_impossible
  | candidate leftCandidate =>
      cases right with
      | impossible => exact signed_impossible
      | candidate rightCandidate =>
          intro candidate equal
          simp [CandidateResult.combine] at equal
          cases equal
          simp [SatisfactionCandidate.combine, signed rightCandidate rfl]

theorem CanonicalWhenUsable.combine {left right : CandidateResult}
    (leftCanonical : left.CanonicalWhenUsable)
    (rightCanonical : right.CanonicalWhenUsable) :
    (left.combine right).CanonicalWhenUsable := by
  cases left with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate leftCandidate =>
      cases right with
      | impossible => exact canonicalWhenUsable_impossible
      | candidate rightCandidate =>
          intro candidate equal usable
          simp [CandidateResult.combine] at equal
          cases equal
          have statuses :=
            SatisfactionCandidate.combine_status_eq_usable_iff
              leftCandidate rightCandidate |>.mp usable
          exact (SatisfactionCandidate.combine_origin_eq_canonical_iff
            leftCandidate rightCandidate).mpr
              ⟨leftCanonical leftCandidate rfl statuses.1,
                rightCanonical rightCandidate rfl statuses.2⟩

theorem Unconditional.combine {left right : CandidateResult}
    (leftUnconditional : left.Unconditional)
    (rightUnconditional : right.Unconditional) :
    (left.combine right).Unconditional := by
  obtain ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩ :=
    leftUnconditional
  obtain ⟨rightCandidate, rfl, rightHasSig, rightCanonical⟩ :=
    rightUnconditional
  refine ⟨leftCandidate.combine rightCandidate, rfl, ?_,
    leftCanonical.combine rightCanonical⟩
  simp [SatisfactionCandidate.combine, leftHasSig, rightHasSig]

theorem Signed.select {left right : CandidateResult}
    (leftSigned : left.Signed) (rightSigned : right.Signed) :
    (left.select right).Signed := by
  cases left with
  | impossible => exact rightSigned
  | candidate leftCandidate =>
      cases right with
      | impossible => exact leftSigned
      | candidate rightCandidate =>
          intro candidate equal
          simp [CandidateResult.select] at equal
          cases leftHasSig : leftCandidate.hasSig
          case false =>
            simpa [leftHasSig] using leftSigned leftCandidate rfl
          case true =>
            cases rightHasSig : rightCandidate.hasSig
            case false =>
              simpa [rightHasSig] using rightSigned rightCandidate rfl
            case true =>
              rw [← equal]
              cases leftStatus : leftCandidate.status <;>
                cases rightStatus : rightCandidate.status <;>
                simp [SatisfactionCandidate.select, leftHasSig, rightHasSig,
                  leftStatus, rightStatus]
              all_goals
                change (if leftCandidate.cost ≤ rightCandidate.cost then
                  leftCandidate else rightCandidate).hasSig = true
                split <;> simp_all

theorem CanonicalWhenUsable.select {left right : CandidateResult}
    (leftCanonical : left.CanonicalWhenUsable)
    (rightCanonical : right.CanonicalWhenUsable) :
    (left.select right).CanonicalWhenUsable := by
  intro candidate equal usable
  cases left with
  | impossible => exact rightCanonical candidate equal usable
  | candidate leftCandidate =>
      cases right with
      | impossible => exact leftCanonical candidate equal usable
      | candidate rightCandidate =>
          simp [CandidateResult.select] at equal
          have source := SatisfactionCandidate.select_usable_source
            leftCandidate rightCandidate (by simpa [equal] using usable)
          rcases source with ⟨chosen, sourceUsable⟩ | ⟨chosen, sourceUsable⟩
          · rw [← equal, chosen]
            exact leftCanonical leftCandidate rfl sourceUsable
          · rw [← equal, chosen]
            exact rightCanonical rightCandidate rfl sourceUsable

theorem Unconditional.select_signed {left right : CandidateResult}
    (leftUnconditional : left.Unconditional) (rightSigned : right.Signed) :
    (left.select right).Unconditional := by
  obtain ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩ :=
    leftUnconditional
  cases right with
  | impossible =>
      exact ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩
  | candidate rightCandidate =>
      have rightHasSig := rightSigned rightCandidate rfl
      refine ⟨leftCandidate, ?_, leftHasSig, ?_⟩
      simp [CandidateResult.select, SatisfactionCandidate.select,
        leftHasSig, rightHasSig]
      simpa [CandidateResult.select, SatisfactionCandidate.select,
        leftHasSig, rightHasSig] using leftCanonical

theorem Signed.select_unconditional {left right : CandidateResult}
    (leftSigned : left.Signed) (rightUnconditional : right.Unconditional) :
    (left.select right).Unconditional := by
  obtain ⟨rightCandidate, rfl, rightHasSig, rightCanonical⟩ :=
    rightUnconditional
  cases left with
  | impossible =>
      exact ⟨rightCandidate, rfl, rightHasSig, rightCanonical⟩
  | candidate leftCandidate =>
      have leftHasSig := leftSigned leftCandidate rfl
      refine ⟨rightCandidate, ?_, rightHasSig, ?_⟩
      simp [CandidateResult.select, SatisfactionCandidate.select,
        leftHasSig, rightHasSig]
      simpa [CandidateResult.select, SatisfactionCandidate.select,
        leftHasSig, rightHasSig] using rightCanonical

/-- Scanning an overcomplete row preserves an unsigned result whose usable
    provenance is canonical. A competing unsigned row makes the result
    `DONTUSE`; a signed row loses to the unsigned result. -/
theorem Unconditional.select_markOvercomplete {left right : CandidateResult}
    (leftUnconditional : left.Unconditional) :
    (left.select right.markOvercomplete).Unconditional := by
  obtain ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩ :=
    leftUnconditional
  cases right with
  | impossible => exact ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩
  | candidate rightCandidate =>
      change (CandidateResult.candidate
        (leftCandidate.select rightCandidate.markOvercomplete)).Unconditional
      cases rightHasSig : rightCandidate.hasSig
      · let selected := leftCandidate.select rightCandidate.markOvercomplete
        have selectedStatus : selected.status = .dontUse := by
          simp [selected, SatisfactionCandidate.select, leftHasSig,
            rightHasSig, SatisfactionCandidate.markOvercomplete]
        have selectedHasSig : selected.hasSig = false := by
          simp [selected, leftHasSig, rightHasSig,
            SatisfactionCandidate.markOvercomplete]
        exact unconditional_of_dontUse selected selectedStatus selectedHasSig
      · have selectedEq :
            leftCandidate.select rightCandidate.markOvercomplete =
              leftCandidate := by
          simp [SatisfactionCandidate.select, leftHasSig, rightHasSig,
            SatisfactionCandidate.markOvercomplete]
        rw [selectedEq]
        exact ⟨leftCandidate, rfl, leftHasSig, leftCanonical⟩

theorem Signed.finalizeLegacyMulti {result : CandidateResult}
    (signed : result.Signed) : (finalizeLegacyMulti result).Signed := by
  cases result with
  | impossible => exact signed_impossible
  | candidate source =>
      intro candidate equal
      cases equal
      exact signed source rfl

theorem CanonicalWhenUsable.finalizeLegacyMulti {result : CandidateResult}
    (canonical : result.CanonicalWhenUsable) :
    (finalizeLegacyMulti result).CanonicalWhenUsable := by
  cases result with
  | impossible => exact canonicalWhenUsable_impossible
  | candidate source =>
      intro candidate equal usable
      cases equal
      exact canonical source rfl usable

end CandidateResult

/-! ## Exact-count candidate security -/

namespace CandidatePair

/-- Security facts contributed by one child of an exact-count candidate table.
    `signed` records the child's BIP 379 `s` modifier. -/
structure ChoiceSecurity (pair : CandidatePair) (signed : Bool) : Prop where
  satCanonical : pair.sat.CanonicalWhenUsable
  satSigned : signed = true → pair.sat.Signed
  dsatUnconditional : pair.dsat.Unconditional

/-- The portion of child security needed to interpret the `s` modifier. -/
structure SignatureSecurity (pair : CandidatePair) (signed : Bool) : Prop where
  satSigned : signed = true → pair.sat.Signed

/-- Pointwise security facts for an exact-count child list. -/
inductive ChoiceSecurityList : List CandidatePair → List Bool → Prop where
  | nil : ChoiceSecurityList [] []
  | cons {pair : CandidatePair} {signed : Bool} {pairs : List CandidatePair}
      {signedFlags : List Bool} :
      ChoiceSecurity pair signed →
      ChoiceSecurityList pairs signedFlags →
      ChoiceSecurityList (pair :: pairs) (signed :: signedFlags)

/-- Pointwise signature requirements for an exact-count child list. -/
inductive SignatureSecurityList : List CandidatePair → List Bool → Prop where
  | nil : SignatureSecurityList [] []
  | cons {pair : CandidatePair} {signed : Bool}
      {pairs : List CandidatePair} {signedFlags : List Bool} :
      SignatureSecurity pair signed →
      SignatureSecurityList pairs signedFlags →
      SignatureSecurityList (pair :: pairs) (signed :: signedFlags)

namespace ChoiceSecurityList

theorem reverse {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : ChoiceSecurityList pairs signedFlags) :
    ChoiceSecurityList pairs.reverse signedFlags.reverse := by
  induction security with
  | nil => exact .nil
  | @cons pair signed pairs signedFlags head tail ih =>
      simpa using append ih (.cons head .nil)
where
  append {leftPairs rightPairs : List CandidatePair}
      {leftFlags rightFlags : List Bool}
      (left : ChoiceSecurityList leftPairs leftFlags)
      (right : ChoiceSecurityList rightPairs rightFlags) :
      ChoiceSecurityList (leftPairs ++ rightPairs)
        (leftFlags ++ rightFlags) := by
    induction left with
    | nil => simpa using right
    | cons head tail ih => exact .cons head ih

end ChoiceSecurityList

namespace SignatureSecurityList

theorem reverse {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : SignatureSecurityList pairs signedFlags) :
    SignatureSecurityList pairs.reverse signedFlags.reverse := by
  induction security with
  | nil => exact .nil
  | @cons pair signed pairs signedFlags head tail ih =>
      simpa using append ih (.cons head .nil)
where
  append {leftPairs rightPairs : List CandidatePair}
      {leftFlags rightFlags : List Bool}
      (left : SignatureSecurityList leftPairs leftFlags)
      (right : SignatureSecurityList rightPairs rightFlags) :
      SignatureSecurityList (leftPairs ++ rightPairs)
        (leftFlags ++ rightFlags) := by
    induction left with
    | nil => simpa using right
    | cons head tail ih => exact .cons head ih

end SignatureSecurityList

/-- Count children whose satisfactions are not guaranteed to contain a
    signature. -/
def countUnsigned : List Bool → Nat
  | [] => 0
  | signed :: rest => (if signed then 0 else 1) + countUnsigned rest

@[simp] theorem countUnsigned_append (left right : List Bool) :
    countUnsigned (left ++ right) = countUnsigned left + countUnsigned right := by
  induction left with
  | nil => simp [countUnsigned]
  | cons signed rest ih => simp [countUnsigned, ih, Nat.add_assoc]

@[simp] theorem countUnsigned_reverse (flags : List Bool) :
    countUnsigned flags.reverse = countUnsigned flags := by
  induction flags with
  | nil => rfl
  | cons signed rest ih => simp [countUnsigned, ih, Nat.add_comm]

/-- Exact-count selection cannot expose a usable non-canonical candidate when
    every child satisfaction and unconditional dissatisfaction has canonical
    usable provenance. -/
theorem selectExactly_canonicalWhenUsable
    {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : ChoiceSecurityList pairs signedFlags) (count : Nat) :
    (selectExactly count pairs).CanonicalWhenUsable := by
  have reversed := security.reverse
  have helper : ∀ {revPairs : List CandidatePair} {revFlags : List Bool},
      ChoiceSecurityList revPairs revFlags →
      ∀ count,
        (selectExactly count revPairs.reverse).CanonicalWhenUsable := by
    intro revPairs revFlags reversedSecurity
    induction reversedSecurity with
    | nil =>
        intro count
        cases count with
        | zero => exact CandidateResult.canonicalWhenUsable_usable [] false
        | succ count => exact CandidateResult.canonicalWhenUsable_impossible
    | @cons pair signed revPairs revFlags head tail ih =>
        intro count
        simp only [List.reverse_cons]
        cases count with
        | zero =>
            rw [selectExactly_append, extendCounts_getD_zero]
            exact CandidateResult.CanonicalWhenUsable.combine (ih 0)
              head.dsatUnconditional.canonicalWhenUsable
        | succ count =>
            rw [selectExactly_append, extendCounts_getD_succ]
            exact CandidateResult.CanonicalWhenUsable.select
              (CandidateResult.CanonicalWhenUsable.combine (ih (count + 1))
                head.dsatUnconditional.canonicalWhenUsable)
              (CandidateResult.CanonicalWhenUsable.combine (ih count)
                head.satCanonical)
  simpa using helper reversed count

/-- The zero-satisfaction exact-count row is the composition of the children's
    unique unconditional dissatisfactions. -/
theorem selectExactly_zero_unconditional
    {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : ChoiceSecurityList pairs signedFlags) :
    (selectExactly 0 pairs).Unconditional := by
  have reversed := security.reverse
  have helper : ∀ {revPairs : List CandidatePair} {revFlags : List Bool},
      ChoiceSecurityList revPairs revFlags →
      (selectExactly 0 revPairs.reverse).Unconditional := by
    intro revPairs revFlags reversedSecurity
    induction reversedSecurity with
    | nil => exact CandidateResult.unconditional_usable []
    | @cons pair signed revPairs revFlags head tail ih =>
        simp only [List.reverse_cons]
        rw [selectExactly_append, extendCounts_getD_zero]
        exact ih.combine head.dsatUnconditional
  simpa using helper reversed

private theorem thresholdFold_unconditional
    (threshold : Nat) (entries : List (CandidateResult × Nat))
    (selected : CandidateResult) (unconditional : selected.Unconditional) :
    (entries.foldl
      (fun current entry =>
        if entry.2 = threshold then current
        else current.select entry.1.markOvercomplete)
      selected).Unconditional := by
  induction entries generalizing selected with
  | nil => exact unconditional
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      apply ih
      by_cases skipped : entry.2 = threshold
      · simpa [skipped] using unconditional
      · simpa [skipped] using unconditional.select_markOvercomplete

/-- Threshold dissatisfaction starts from the all-dissatisfied exact-count row.
    Scanning the retained overcomplete rows cannot turn a non-canonical row
    into a usable output. -/
theorem thresholdDissatisfaction_unconditional
    {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : ChoiceSecurityList pairs signedFlags) (threshold : Nat) :
    (thresholdDissatisfaction threshold (countCandidates pairs)).Unconditional := by
  have zero := selectExactly_zero_unconditional security
  cases statesEq : countCandidates pairs with
  | nil =>
      simp [selectExactly, statesEq, CandidateResult.Unconditional] at zero
  | cons canonical positive =>
      have canonicalUnconditional : canonical.Unconditional := by
        simpa [selectExactly, statesEq] using zero
      simp only [thresholdDissatisfaction]
      exact thresholdFold_unconditional threshold (positive.zipIdx 1)
        canonical canonicalUnconditional

/-- If fewer than `count` children may be unsigned, every raw candidate in the
    exact-count state contains a signature. This includes candidates already
    marked `DONTUSE`, which is required by subsequent selection steps. -/
theorem selectExactly_signed_of_countUnsigned_lt
    {pairs : List CandidatePair} {signedFlags : List Bool}
    (security : SignatureSecurityList pairs signedFlags) {count : Nat}
    (fewer : countUnsigned signedFlags < count) :
    (selectExactly count pairs).Signed := by
  have reversed := security.reverse
  have helper : ∀ {revPairs : List CandidatePair} {revFlags : List Bool},
      SignatureSecurityList revPairs revFlags →
      ∀ {count : Nat}, countUnsigned revFlags < count →
        (selectExactly count revPairs.reverse).Signed := by
    intro revPairs revFlags reversedSecurity
    induction reversedSecurity with
    | nil =>
        intro count fewer
        simp [countUnsigned] at fewer
        cases count with
        | zero => omega
        | succ count => exact CandidateResult.signed_impossible
    | @cons pair signed revPairs revFlags head tail ih =>
        intro count fewer
        simp only [List.reverse_cons] at ⊢
        cases count with
        | zero => omega
        | succ count =>
            rw [selectExactly_append, extendCounts_getD_succ]
            have leftSigned :
                ((selectExactly (count + 1) revPairs.reverse).combine
                  pair.dsat).Signed := by
              apply CandidateResult.Signed.combine_left
              apply ih
              cases signed <;> simp [countUnsigned] at fewer ⊢ <;> omega
            have rightSigned :
                ((selectExactly count revPairs.reverse).combine pair.sat).Signed := by
              cases signed with
              | false =>
                  apply CandidateResult.Signed.combine_left
                  apply ih
                  simp [countUnsigned] at fewer ⊢
                  omega
              | true =>
                  apply CandidateResult.Signed.combine_right
                  exact head.satSigned rfl
            exact leftSigned.select rightSigned
  have result := helper reversed (count := count) (by simpa using fewer)
  simpa using result

/-- Every legacy multisig key choice has a canonical satisfaction, a signature
    whenever it is satisfiable, and the empty unconditional dissatisfaction. -/
theorem legacyMultiChoiceSecurity (keys : List PubKey) (env : SatEnv) :
    ChoiceSecurityList (keys.map (fun key => legacyMultiKeyChoice key env))
      (List.replicate keys.length true) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      apply ChoiceSecurityList.cons
      · refine {
          satCanonical := ?_
          satSigned := ?_
          dsatUnconditional := CandidateResult.unconditional_usable [] }
        · cases selected : env.signatureFor key with
          | none => simpa [legacyMultiKeyChoice, selected] using
              CandidateResult.canonicalWhenUsable_impossible
          | some signature => simpa [legacyMultiKeyChoice, selected] using
              CandidateResult.canonicalWhenUsable_usable [signature] true
        · intro _
          cases selected : env.signatureFor key with
          | none => simpa [legacyMultiKeyChoice, selected] using
              CandidateResult.signed_impossible
          | some signature => simpa [legacyMultiKeyChoice, selected] using
              CandidateResult.signed_usable [signature]
      · simpa using ih

/-- Signature-only projection of legacy key-choice security. -/
theorem legacyMultiSignatureSecurity (keys : List PubKey) (env : SatEnv) :
    SignatureSecurityList (keys.map (fun key => legacyMultiKeyChoice key env))
      (List.replicate keys.length true) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      apply SignatureSecurityList.cons
      · refine ⟨?_⟩
        intro _
        cases selected : env.signatureFor key with
        | none => simpa [legacyMultiKeyChoice, selected] using
            CandidateResult.signed_impossible
        | some signature => simpa [legacyMultiKeyChoice, selected] using
            CandidateResult.signed_usable [signature]
      · simpa using ih

/-- Every Tapscript multisig key choice has the same security summary, with a
    canonical empty-signature dissatisfaction. -/
theorem multiAChoiceSecurity (keys : List PubKey) (env : SatEnv) :
    ChoiceSecurityList (keys.map (fun key => multiAKeyChoice key env))
      (List.replicate keys.length true) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      apply ChoiceSecurityList.cons
      · refine {
          satCanonical := ?_
          satSigned := ?_
          dsatUnconditional :=
            CandidateResult.unconditional_usable [falseElement] }
        · cases selected : env.signatureFor key with
          | none => simpa [multiAKeyChoice, selected] using
              CandidateResult.canonicalWhenUsable_impossible
          | some signature => simpa [multiAKeyChoice, selected] using
              CandidateResult.canonicalWhenUsable_usable [signature] true
        · intro _
          cases selected : env.signatureFor key with
          | none => simpa [multiAKeyChoice, selected] using
              CandidateResult.signed_impossible
          | some signature => simpa [multiAKeyChoice, selected] using
              CandidateResult.signed_usable [signature]
      · simpa using ih

/-- Signature-only projection of Tapscript key-choice security. -/
theorem multiASignatureSecurity (keys : List PubKey) (env : SatEnv) :
    SignatureSecurityList (keys.map (fun key => multiAKeyChoice key env))
      (List.replicate keys.length true) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      apply SignatureSecurityList.cons
      · refine ⟨?_⟩
        intro _
        cases selected : env.signatureFor key with
        | none => simpa [multiAKeyChoice, selected] using
            CandidateResult.signed_impossible
        | some signature => simpa [multiAKeyChoice, selected] using
            CandidateResult.signed_usable [signature]
      · simpa using ih

@[simp] theorem countUnsigned_replicate_true (count : Nat) :
    countUnsigned (List.replicate count true) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [List.replicate_succ, countUnsigned] using ih

end CandidatePair

/-! ## Sound interpretation of malleability modifiers -/

/-- Candidate-level meaning of the BIP 379 malleability modifiers for one
    well-typed fragment and material environment. The `e` obligation is only
    needed together with the recursive non-malleability requirement, exactly
    where parent rules consume it. -/
structure MalleabilityCandidateSound
    (fragment : CoreFragment) (ty : MiniType)
    (mods : MalleabilityModifiers) (env : SatEnv) : Prop where
  signedSat : mods.s = true →
    (satisfactionCandidates fragment env).sat.Signed
  forcedDsat : mods.f = true →
    (satisfactionCandidates fragment env).dsat.Signed
  canonicalSat : mods.nonMalleable = true →
    (satisfactionCandidates fragment env).sat.CanonicalWhenUsable
  expressiveDsat : mods.nonMalleable = true → mods.e = true →
    (satisfactionCandidates fragment env).dsat.Unconditional
  keySat : ty.base = .K →
    (satisfactionCandidates fragment env).sat.Signed

/-- Pointwise candidate semantics for a typed/malleability-typed fragment
    list, used by threshold proofs. -/
inductive MalleabilityCandidateSoundList (env : SatEnv) :
    List CoreFragment → List MiniType → List MalleabilityModifiers → Prop where
  | nil : MalleabilityCandidateSoundList env [] [] []
  | cons {fragment : CoreFragment} {ty : MiniType}
      {mods : MalleabilityModifiers} {fragments : List CoreFragment}
      {types : List MiniType} {rest : List MalleabilityModifiers} :
      MalleabilityCandidateSound fragment ty mods env →
      MalleabilityCandidateSoundList env fragments types rest →
      MalleabilityCandidateSoundList env (fragment :: fragments)
        (ty :: types) (mods :: rest)

/-- Extract the `s` bits in source order for exact-count reasoning. -/
def malleabilitySignedFlags : List MalleabilityModifiers → List Bool
  | [] => []
  | mods :: rest => mods.s :: malleabilitySignedFlags rest

@[simp] theorem countUnsigned_malleabilitySignedFlags
    (mods : List MalleabilityModifiers) :
    CandidatePair.countUnsigned (malleabilitySignedFlags mods) =
      MalleabilityModifiers.countNonS mods := by
  induction mods with
  | nil => rfl
  | cons mods rest ih =>
      simp [malleabilitySignedFlags, CandidatePair.countUnsigned,
        MalleabilityModifiers.countNonS, ih]

namespace MalleabilityCandidateSoundList

/-- Every typed child list interprets the `s` bits needed by exact-count
    selection, independently of whether the list is non-malleable. -/
theorem signatureSecurity
    {env : SatEnv} {fragments : List CoreFragment} {types : List MiniType}
    {mods : List MalleabilityModifiers}
    (sound : MalleabilityCandidateSoundList env fragments types mods) :
    CandidatePair.SignatureSecurityList
      (satisfactionCandidatesList fragments env)
      (malleabilitySignedFlags mods) := by
  induction sound with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons ⟨head.signedSat⟩ ih

/-- Recursively non-malleable, expressive children supply the canonical
    satisfaction and unconditional dissatisfaction facts used by threshold
    selection. -/
theorem choiceSecurity
    {env : SatEnv} {fragments : List CoreFragment} {types : List MiniType}
    {mods : List MalleabilityModifiers}
    (sound : MalleabilityCandidateSoundList env fragments types mods)
    (allNonMalleable : MalleabilityModifiers.allNonMalleable mods = true)
    (allExpressive : MalleabilityModifiers.allE mods = true) :
    CandidatePair.ChoiceSecurityList
      (satisfactionCandidatesList fragments env)
      (malleabilitySignedFlags mods) := by
  induction sound with
  | nil => exact .nil
  | @cons fragment ty mods fragments types rest head tail ih =>
      change (mods.nonMalleable &&
        MalleabilityModifiers.allNonMalleable rest) = true at allNonMalleable
      change (mods.e && MalleabilityModifiers.allE rest) = true at allExpressive
      rw [Bool.and_eq_true] at allNonMalleable allExpressive
      exact .cons {
        satCanonical := head.canonicalSat allNonMalleable.1
        satSigned := head.signedSat
        dsatUnconditional := head.expressiveDsat
          allNonMalleable.1 allExpressive.1
      } (ih allNonMalleable.2 allExpressive.2)

end MalleabilityCandidateSoundList

/- Correctness typing and structural well-formedness make every BIP 379
   malleability modifier sound for the concrete satisfaction candidates. -/
mutual
theorem malleabilityCandidateSound {ctx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {mods : MalleabilityModifiers} (env : SatEnv)
    (wellFormed : fragment.WellFormed ctx)
    (typed : HasType ctx fragment ty)
    (mal : HasMalleability ctx fragment mods) :
    MalleabilityCandidateSound fragment ty mods env := by
  cases typed with
  | zero =>
      cases mal
      exact {
        signedSat := fun _ => CandidateResult.signed_impossible
        forcedDsat := by simp
        canonicalSat := fun _ => CandidateResult.canonicalWhenUsable_impossible
        expressiveDsat := fun _ _ => CandidateResult.unconditional_usable []
        keySat := by simp }
  | one =>
      cases mal
      exact {
        signedSat := by simp
        forcedDsat := fun _ => CandidateResult.signed_impossible
        canonicalSat := fun _ => CandidateResult.canonicalWhenUsable_usable [] false
        expressiveDsat := by simp
        keySat := by simp }
  | pk_k key =>
      cases mal
      cases selected : env.signatureFor key with
      | none =>
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using CandidateResult.signed_impossible
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.canonicalWhenUsable_impossible
            expressiveDsat := fun _ _ => CandidateResult.unconditional_usable [falseElement]
            keySat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using CandidateResult.signed_impossible }
      | some signature =>
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.signed_usable [signature]
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.canonicalWhenUsable_usable [signature] true
            expressiveDsat := fun _ _ => CandidateResult.unconditional_usable [falseElement]
            keySat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.signed_usable [signature] }
  | pk_h key =>
      cases mal
      cases selected : env.signatureFor key with
      | none =>
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using CandidateResult.signed_impossible
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.canonicalWhenUsable_impossible
            expressiveDsat := fun _ _ => CandidateResult.unconditional_usable [falseElement, key.bytes]
            keySat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using CandidateResult.signed_impossible }
      | some signature =>
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.signed_usable [signature, key.bytes]
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                (CandidateResult.canonicalWhenUsable_usable
                  [signature, key.bytes] true)
            expressiveDsat := fun _ _ => CandidateResult.unconditional_usable [falseElement, key.bytes]
            keySat := fun _ => by simpa [satisfactionCandidates,
              keyCandidates, selected] using
                CandidateResult.signed_usable [signature, key.bytes] }
  | older n =>
      cases mal
      by_cases available : sequenceSatisfied n env.txCtx
      · exact {
          signedSat := by simp
          forcedDsat := fun _ => CandidateResult.signed_impossible
          canonicalSat := fun _ => by simpa [satisfactionCandidates,
            available] using CandidateResult.canonicalWhenUsable_usable [] false
          expressiveDsat := by simp
          keySat := by simp }
      · exact {
          signedSat := by simp
          forcedDsat := fun _ => CandidateResult.signed_impossible
          canonicalSat := fun _ => by simpa [satisfactionCandidates,
            available] using CandidateResult.canonicalWhenUsable_impossible
          expressiveDsat := by simp
          keySat := by simp }
  | after n =>
      cases mal
      by_cases available : locktimeSatisfied n env.txCtx
      · exact {
          signedSat := by simp
          forcedDsat := fun _ => CandidateResult.signed_impossible
          canonicalSat := fun _ => by simpa [satisfactionCandidates,
            available] using CandidateResult.canonicalWhenUsable_usable [] false
          expressiveDsat := by simp
          keySat := by simp }
      · exact {
          signedSat := by simp
          forcedDsat := fun _ => CandidateResult.signed_impossible
          canonicalSat := fun _ => by simpa [satisfactionCandidates,
            available] using CandidateResult.canonicalWhenUsable_impossible
          expressiveDsat := by simp
          keySat := by simp }
  | sha256 hash | hash256 hash | ripemd160 hash | hash160 hash =>
      cases mal
      exact {
        signedSat := by simp
        forcedDsat := by simp
        canonicalSat := fun _ => by
          change (match env.preimageFor _ with
            | none => CandidateResult.impossible
            | some preimage => CandidateResult.usable [preimage] false
            ).CanonicalWhenUsable
          split
          · exact CandidateResult.canonicalWhenUsable_impossible
          · exact CandidateResult.canonicalWhenUsable_usable _ false
        expressiveDsat := by simp
        keySat := by simp }
  | and_v typedX typedY branch =>
      cases mal with
      | and_v malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2.1 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := ?_
            canonicalSat := ?_
            expressiveDsat := by simp
            keySat := ?_ }
          · intro signed
            change ((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).sat).Signed
            simp only [Bool.or_eq_true] at signed
            rcases signed with signedX | signedY
            · exact (soundX.signedSat signedX).combine_left
            · exact (soundY.signedSat signedY).combine_right
          · intro forced
            change (((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).dsat).markNonCanonical).Signed
            simp only [Bool.or_eq_true] at forced
            apply CandidateResult.Signed.markNonCanonical
            rcases forced with signedX | forcedY
            · exact (soundX.signedSat signedX).combine_left
            · exact (soundY.forcedDsat forcedY).combine_right
          · intro nonMalleable
            change ((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).sat).CanonicalWhenUsable
            simp only [Bool.and_eq_true] at nonMalleable
            exact (soundX.canonicalSat nonMalleable.1).combine
              (soundY.canonicalSat nonMalleable.2)
          · intro keyBase
            change ((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).sat).Signed
            exact (soundY.keySat keyBase).combine_right
  | and_b typedX typedY =>
      cases mal with
      | and_b malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2.1 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := ?_
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := by simp }
          · intro signed
            change ((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).sat).Signed
            simp only [Bool.or_eq_true] at signed
            rcases signed with signedX | signedY
            · exact (soundX.signedSat signedX).combine_left
            · exact (soundY.signedSat signedY).combine_right
          · intro forced
            change (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).dsat).select
              (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat).markOvercomplete) |>.select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).markOvercomplete)).Signed
            rcases (boolOr3_eq_true _ _ _).mp forced with
              bothForced | signedForcedX | signedForcedY
            all_goals try simp only [Bool.and_eq_true] at *
            · apply CandidateResult.Signed.select
                (CandidateResult.Signed.select
                  (soundX.forcedDsat bothForced.1 |>.combine_left)
                  (soundX.forcedDsat bothForced.1 |>.combine_left
                    |>.markOvercomplete))
              exact soundY.forcedDsat bothForced.2 |>.combine_right
                |>.markOvercomplete
            · apply CandidateResult.Signed.select
                (CandidateResult.Signed.select
                  (soundX.forcedDsat signedForcedX.2 |>.combine_left)
                  (soundX.forcedDsat signedForcedX.2 |>.combine_left
                    |>.markOvercomplete))
              exact soundX.signedSat signedForcedX.1 |>.combine_left
                |>.markOvercomplete
            · apply CandidateResult.Signed.select
                (CandidateResult.Signed.select
                  (soundY.forcedDsat signedForcedY.2 |>.combine_right)
                  (soundY.signedSat signedForcedY.1 |>.combine_right
                    |>.markOvercomplete))
              exact soundY.forcedDsat signedForcedY.2 |>.combine_right
                |>.markOvercomplete
          · intro nonMalleable
            change ((satisfactionCandidates _ env).sat.combine
              (satisfactionCandidates _ env).sat).CanonicalWhenUsable
            simp only [Bool.and_eq_true] at nonMalleable
            exact (soundX.canonicalSat nonMalleable.1).combine
              (soundY.canonicalSat nonMalleable.2)
          · intro nonMalleable expressive
            change (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).dsat).select
              (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat).markOvercomplete) |>.select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).markOvercomplete)).Unconditional
            rw [Bool.and_eq_true] at nonMalleable
            obtain ⟨expressiveX, expressiveY, signedX, signedY⟩ :=
              (boolAnd4_eq_true _ _ _ _).mp expressive
            have canonical :=
              (soundX.expressiveDsat nonMalleable.1 expressiveX).combine
                (soundY.expressiveDsat nonMalleable.2 expressiveY)
            exact canonical.select_markOvercomplete.select_markOvercomplete
  | or_b typedX dx typedY dy =>
      cases mal with
      | or_b malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := by simp
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := by simp }
          · intro signed
            change ((((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).sat).markOvercomplete)).Signed
            simp only [Bool.and_eq_true] at signed
            exact ((soundX.signedSat signed.1).combine_left |>.select
              ((soundY.signedSat signed.2).combine_right)) |>.select
              ((soundX.signedSat signed.1).combine_left.markOvercomplete)
          · intro nonMalleable
            change ((((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).sat).markOvercomplete)).CanonicalWhenUsable
            obtain ⟨nmX, nmY, expressiveX, expressiveY, signedChoice⟩ :=
              (boolAnd5_eq_true _ _ _ _ _).mp nonMalleable
            exact (((soundX.canonicalSat nmX).combine
                (soundY.expressiveDsat nmY expressiveY).canonicalWhenUsable).select
              ((soundX.expressiveDsat nmX expressiveX).canonicalWhenUsable.combine
                (soundY.canonicalSat nmY))).select
              (CandidateResult.canonicalWhenUsable_markOvercomplete _)
          · intro nonMalleable _
            change ((satisfactionCandidates _ env).dsat.combine
              (satisfactionCandidates _ env).dsat).Unconditional
            obtain ⟨nmX, nmY, expressiveX, expressiveY, signedChoice⟩ :=
              (boolAnd5_eq_true _ _ _ _ _).mp nonMalleable
            exact (soundX.expressiveDsat nmX expressiveX).combine
              (soundY.expressiveDsat nmY expressiveY)
  | or_c typedX dx ux typedY =>
      cases mal with
      | or_c malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := fun _ => CandidateResult.signed_impossible
            canonicalSat := ?_
            expressiveDsat := by simp
            keySat := by simp }
          · intro signed
            change ((satisfactionCandidates _ env).sat.select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).Signed
            simp only [Bool.and_eq_true] at signed
            exact (soundX.signedSat signed.1).select
              ((soundY.signedSat signed.2).combine_right)
          · intro nonMalleable
            change ((satisfactionCandidates _ env).sat.select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).CanonicalWhenUsable
            obtain ⟨nmX, nmY, expressiveX, signedChoice⟩ :=
              (boolAnd4_eq_true _ _ _ _).mp nonMalleable
            exact (soundX.canonicalSat nmX).select
              ((soundX.expressiveDsat nmX expressiveX).canonicalWhenUsable.combine
                (soundY.canonicalSat nmY))
  | or_d typedX dx ux typedY =>
      cases mal with
      | or_d malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := ?_
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := by simp }
          · intro signed
            change ((satisfactionCandidates _ env).sat.select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).Signed
            simp only [Bool.and_eq_true] at signed
            exact (soundX.signedSat signed.1).select
              ((soundY.signedSat signed.2).combine_right)
          · intro forced
            change ((satisfactionCandidates _ env).dsat.combine
              (satisfactionCandidates _ env).dsat).Signed
            exact (soundY.forcedDsat forced).combine_right
          · intro nonMalleable
            change ((satisfactionCandidates _ env).sat.select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).CanonicalWhenUsable
            obtain ⟨nmX, nmY, expressiveX, signedChoice⟩ :=
              (boolAnd4_eq_true _ _ _ _).mp nonMalleable
            exact (soundX.canonicalSat nmX).select
              ((soundX.expressiveDsat nmX expressiveX).canonicalWhenUsable.combine
                (soundY.canonicalSat nmY))
          · intro nonMalleable expressive
            change ((satisfactionCandidates _ env).dsat.combine
              (satisfactionCandidates _ env).dsat).Unconditional
            obtain ⟨nmX, nmY, expressiveX, signedChoice⟩ :=
              (boolAnd4_eq_true _ _ _ _).mp nonMalleable
            exact (soundX.expressiveDsat nmX expressiveX).combine
              (soundY.expressiveDsat nmY expressive)
  | or_i typedX typedY branch bases =>
      cases mal with
      | or_i malX malY =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2 typedY malY
          refine {
            signedSat := ?_
            forcedDsat := ?_
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := ?_ }
          · intro signed
            change ((satisfactionCandidates _ env).sat.withSelector trueElement |>.select
              ((satisfactionCandidates _ env).sat.withSelector falseElement)).Signed
            simp only [Bool.and_eq_true] at signed
            exact (soundX.signedSat signed.1 |>.withSelector _).select
              (soundY.signedSat signed.2 |>.withSelector _)
          · intro forced
            change ((satisfactionCandidates _ env).dsat.withSelector trueElement |>.select
              ((satisfactionCandidates _ env).dsat.withSelector falseElement)).Signed
            simp only [Bool.and_eq_true] at forced
            exact (soundX.forcedDsat forced.1 |>.withSelector _).select
              (soundY.forcedDsat forced.2 |>.withSelector _)
          · intro nonMalleable
            change ((satisfactionCandidates _ env).sat.withSelector trueElement |>.select
              ((satisfactionCandidates _ env).sat.withSelector falseElement)).CanonicalWhenUsable
            obtain ⟨nmX, nmY, signedChoice⟩ :=
              (boolAnd3_eq_true _ _ _).mp nonMalleable
            exact (soundX.canonicalSat nmX |>.withSelector _).select
              (soundY.canonicalSat nmY |>.withSelector _)
          · intro nonMalleable expressive
            change ((satisfactionCandidates _ env).dsat.withSelector trueElement |>.select
              ((satisfactionCandidates _ env).dsat.withSelector falseElement)).Unconditional
            obtain ⟨nmX, nmY, signedChoice⟩ :=
              (boolAnd3_eq_true _ _ _).mp nonMalleable
            rw [Bool.or_eq_true] at expressive
            rcases expressive with expressiveX | expressiveY
            all_goals try simp only [Bool.and_eq_true] at *
            · exact (soundX.expressiveDsat nmX expressiveX.1 |>.withSelector _).select_signed
                (soundY.forcedDsat expressiveX.2 |>.withSelector _)
            · exact (soundX.forcedDsat expressiveY.2 |>.withSelector _).select_unconditional
                (soundY.expressiveDsat nmY expressiveY.1 |>.withSelector _)
          · intro keyBase
            change ((satisfactionCandidates _ env).sat.withSelector trueElement |>.select
              ((satisfactionCandidates _ env).sat.withSelector falseElement)).Signed
            exact (soundX.keySat keyBase |>.withSelector _).select
              (soundY.keySat (bases.symm.trans keyBase) |>.withSelector _)
  | andor typedX dx ux typedY typedZ branch bases =>
      cases mal with
      | andor malX malY malZ =>
          have soundX := malleabilityCandidateSound env wellFormed.1 typedX malX
          have soundY := malleabilityCandidateSound env wellFormed.2.1 typedY malY
          have soundZ := malleabilityCandidateSound env wellFormed.2.2.1 typedZ malZ
          refine {
            signedSat := ?_
            forcedDsat := ?_
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := ?_ }
          · intro signed
            change (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).sat).select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).Signed
            rw [Bool.and_eq_true, Bool.or_eq_true] at signed
            rcases signed.2 with signedX | signedY
            · exact ((soundX.signedSat signedX).combine_left).select
                ((soundZ.signedSat signed.1).combine_right)
            · exact ((soundY.signedSat signedY).combine_right).select
                ((soundZ.signedSat signed.1).combine_right)
          · intro forced
            change (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).dsat).select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).markNonCanonical)).Signed
            rw [Bool.and_eq_true, Bool.or_eq_true] at forced
            rcases forced.2 with signedX | forcedY
            · exact ((soundZ.forcedDsat forced.1).combine_right).select
                ((soundX.signedSat signedX).combine_left.markNonCanonical)
            · exact ((soundZ.forcedDsat forced.1).combine_right).select
                ((soundY.forcedDsat forcedY).combine_right.markNonCanonical)
          · intro nonMalleable
            change (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).sat).select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).CanonicalWhenUsable
            obtain ⟨nmX, nmY, nmZ, expressiveX, signedChoice⟩ :=
              (boolAnd5_eq_true _ _ _ _ _).mp nonMalleable
            exact ((soundX.canonicalSat nmX).combine
              (soundY.canonicalSat nmY)).select
              ((soundX.expressiveDsat nmX expressiveX).canonicalWhenUsable.combine
                (soundZ.canonicalSat nmZ))
          · intro nonMalleable expressive
            change (((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).dsat).select
              (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).dsat).markNonCanonical)).Unconditional
            obtain ⟨nmX, nmY, nmZ, expressiveX, signedChoice⟩ :=
              (boolAnd5_eq_true _ _ _ _ _).mp nonMalleable
            rw [Bool.and_eq_true, Bool.or_eq_true] at expressive
            have canonical := (soundX.expressiveDsat nmX expressiveX).combine
              (soundZ.expressiveDsat nmZ expressive.1)
            rcases expressive.2 with signedX | forcedY
            · exact canonical.select_signed
                ((soundX.signedSat signedX).combine_left.markNonCanonical)
            · exact canonical.select_signed
                ((soundY.forcedDsat forcedY).combine_right.markNonCanonical)
          · intro keyBase
            change (((satisfactionCandidates _ env).sat.combine
                (satisfactionCandidates _ env).sat).select
              ((satisfactionCandidates _ env).dsat.combine
                (satisfactionCandidates _ env).sat)).Signed
            exact (soundY.keySat keyBase |>.combine_right).select
              (soundZ.keySat (bases.symm.trans keyBase) |>.combine_right)
  | @c_wrap X modsX typedX =>
      cases mal with
      | c malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := fun _ => soundX.keySat rfl
            forcedDsat := soundX.forcedDsat
            canonicalSat := soundX.canonicalSat
            expressiveDsat := soundX.expressiveDsat
            keySat := by simp }
  | @v_wrap X modsX typedX =>
      cases mal with
      | v malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := soundX.signedSat
            forcedDsat := fun _ => CandidateResult.signed_impossible
            canonicalSat := soundX.canonicalSat
            expressiveDsat := by simp
            keySat := by simp }
  | @a_wrap X modsX typedX =>
      cases mal with
      | a malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := soundX.signedSat
            forcedDsat := soundX.forcedDsat
            canonicalSat := soundX.canonicalSat
            expressiveDsat := soundX.expressiveDsat
            keySat := by simp }
  | @s_wrap X modsX typedX one =>
      cases mal with
      | s malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := soundX.signedSat
            forcedDsat := soundX.forcedDsat
            canonicalSat := soundX.canonicalSat
            expressiveDsat := soundX.expressiveDsat
            keySat := by simp }
  | @d_wrap X modsX typedX zero =>
      cases mal with
      | d malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := fun signed => soundX.signedSat signed |>.withSelector _
            forcedDsat := by simp
            canonicalSat := fun nonMalleable =>
              soundX.canonicalSat nonMalleable |>.withSelector _
            expressiveDsat := fun _ _ =>
              CandidateResult.unconditional_usable [falseElement]
            keySat := by simp }
  | @j_wrap X modsX typedX nonzero =>
      cases mal with
      | j malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          refine {
            signedSat := soundX.signedSat
            forcedDsat := by simp
            canonicalSat := soundX.canonicalSat
            expressiveDsat := ?_
            keySat := by simp }
          intro nonMalleable expressive
          change ((CandidateResult.usable [falseElement] false).select
            ((satisfactionCandidates _ env).dsat.requireNonemptyRuntimeTop
              |>.markNonCanonical)).Unconditional
          exact (CandidateResult.unconditional_usable [falseElement]).select_signed
            (soundX.forcedDsat expressive |>.requireNonemptyRuntimeTop
              |>.markNonCanonical)
  | @n_wrap X modsX typedX =>
      cases mal with
      | n malX =>
          have childWellFormed : X.WellFormed ctx := wellFormed
          have soundX := malleabilityCandidateSound env childWellFormed typedX malX
          exact {
            signedSat := soundX.signedSat
            forcedDsat := soundX.forcedDsat
            canonicalSat := soundX.canonicalSat
            expressiveDsat := soundX.expressiveDsat
            keySat := by simp }
  | @thresh k X Xs modsX restTypes typedX dx ux typedRest restShape positive bounded =>
      cases mal with
      | @thresh _ _ malMods malAll =>
          have childrenWellFormed : CoreFragment.allWellFormed ctx (X :: Xs) :=
            wellFormed.2.1
          have typedAll : HasTypeList ctx (X :: Xs)
              (⟨.B, modsX⟩ :: restTypes) :=
            .cons typedX typedRest
          have soundAll := malleabilityCandidateSoundList env childrenWellFormed typedAll malAll
          have signatureSecurity := soundAll.signatureSecurity
          have safe : ArithmeticScriptNatSafe k :=
            ArithmeticScriptNatSafe.of_lt (by
              simpa [MAX_BIP_ARITHMETIC_VALUE, MAX_BIP_LOCK_VALUE,
                maxArithmeticScriptNatExclusive] using wellFormed.2.2.2)
          have valid : candidateThresholdValid k (X :: Xs).length :=
            ⟨by omega, bounded, safe⟩
          refine {
            signedSat := ?_
            forcedDsat := by simp
            canonicalSat := ?_
            expressiveDsat := ?_
            keySat := by simp }
          · intro signed
            rw [satisfactionCandidates_thresh_sat k (X :: Xs) env valid]
            have signatureSecurity' : CandidatePair.SignatureSecurityList
                ((X :: Xs).map (fun fragment =>
                  satisfactionCandidates fragment env))
                (malleabilitySignedFlags malMods) := by
              simpa [satisfactionCandidatesList_eq_map] using signatureSecurity
            apply CandidatePair.selectExactly_signed_of_countUnsigned_lt
              signatureSecurity'
            have fewer : MalleabilityModifiers.countNonS malMods < k := by
              simpa [MalleabilityModifiers.fewerThanNonS] using signed
            simpa using fewer
          · intro nonMalleable
            obtain ⟨allNonMalleable, allExpressive, atMost⟩ :=
              (boolAnd3_eq_true _ _ _).mp nonMalleable
            have security := soundAll.choiceSecurity
              allNonMalleable allExpressive
            rw [satisfactionCandidates_thresh_sat k (X :: Xs) env valid]
            simpa [satisfactionCandidatesList_eq_map] using
              CandidatePair.selectExactly_canonicalWhenUsable security k
          · intro nonMalleable expressive
            obtain ⟨allNonMalleable, allExpressive, atMost⟩ :=
              (boolAnd3_eq_true _ _ _).mp nonMalleable
            have security := soundAll.choiceSecurity
              allNonMalleable allExpressive
            rw [satisfactionCandidates_thresh_dsat k (X :: Xs) env valid]
            simpa [satisfactionCandidatesList_eq_map] using
              CandidatePair.thresholdDissatisfaction_unconditional security k
  | multi k keys positive bounded =>
      cases mal with
      | multi _ _ permits =>
          simp only [CoreFragment.WellFormed] at wellFormed
          have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
            simpa [validLegacyMultiKeyCount, maxPubKeysPerMultiSig] using
              wellFormed.2.2.1
          have guard : ¬ (k = 0 ∨ keys.length < k ∨
              maxPubKeysPerMultiSig < keys.length) := by
            simp only [not_or]
            exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBound⟩
          have signatureSecurity :=
            CandidatePair.legacyMultiSignatureSecurity keys env
          have choiceSecurity := CandidatePair.legacyMultiChoiceSecurity keys env
          have fewer : CandidatePair.countUnsigned
              (List.replicate keys.length true) < k := by
            simp only [CandidatePair.countUnsigned_replicate_true]
            omega
          have satSigned :=
            (CandidatePair.selectExactly_signed_of_countUnsigned_lt
              signatureSecurity fewer).finalizeLegacyMulti
          have satCanonical :=
            (CandidatePair.selectExactly_canonicalWhenUsable choiceSecurity k
              |>.finalizeLegacyMulti)
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              legacyMultiCandidates, guard] using satSigned
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              legacyMultiCandidates, guard] using satCanonical
            expressiveDsat := fun _ _ => by
              simpa [satisfactionCandidates, legacyMultiCandidates, guard] using
                CandidateResult.unconditional_usable
                  (List.replicate (k + 1) falseElement)
            keySat := by simp }
  | multi_a k keys positive bounded =>
      cases mal with
      | multi_a _ _ permits =>
          simp only [CoreFragment.WellFormed] at wellFormed
          have keyBound : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A :=
            wellFormed.2.2.1
          have safe : ArithmeticScriptNatSafe k :=
            ArithmeticScriptNatSafe.of_lt (by
              change k < 2147483648
              have : k ≤ 999 := by
                simpa [MAX_PUBKEYS_PER_MULTI_A] using
                  Nat.le_trans bounded keyBound
              omega)
          have valid : candidateThresholdValid k keys.length :=
            ⟨by omega, bounded, safe⟩
          have signatureSecurity := CandidatePair.multiASignatureSecurity keys env
          have choiceSecurity := CandidatePair.multiAChoiceSecurity keys env
          have fewer : CandidatePair.countUnsigned
              (List.replicate keys.length true) < k := by
            simp only [CandidatePair.countUnsigned_replicate_true]
            omega
          have satSigned :=
            CandidatePair.selectExactly_signed_of_countUnsigned_lt
              signatureSecurity fewer
          have satCanonical :=
            CandidatePair.selectExactly_canonicalWhenUsable choiceSecurity k
          exact {
            signedSat := fun _ => by simpa [satisfactionCandidates,
              multiACandidates, valid] using satSigned
            forcedDsat := by simp
            canonicalSat := fun _ => by simpa [satisfactionCandidates,
              multiACandidates, valid] using satCanonical
            expressiveDsat := fun _ _ => by
              simpa [satisfactionCandidates, multiACandidates, valid] using
                CandidateResult.unconditional_usable
                  (List.replicate keys.length falseElement)
            keySat := by simp }

/-- Pointwise soundness for threshold child lists. -/
theorem malleabilityCandidateSoundList {ctx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType} {mods : List MalleabilityModifiers} (env : SatEnv)
    (wellFormed : CoreFragment.allWellFormed ctx fragments)
    (typed : HasTypeList ctx fragments types)
    (mal : HasMalleabilityList ctx fragments mods) :
    MalleabilityCandidateSoundList env fragments types mods := by
  cases typed with
  | nil => cases mal; exact .nil
  | cons typedHead typedTail =>
      cases mal with
      | cons malHead malTail =>
          exact .cons (malleabilityCandidateSound env wellFormed.1 typedHead malHead)
            (malleabilityCandidateSoundList env wellFormed.2 typedTail malTail)
end


end LeanMiniscript.Miniscript
