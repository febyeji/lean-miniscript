import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Satisfaction candidate provenance

The executable candidate representation intentionally stores only the selected
candidate.  This module recovers enough proof-only provenance from usable
outputs to compose the later generated-witness execution proof.
-/

namespace SatisfactionCandidate

/-- A usable result of binary candidate selection is one of the original
    usable candidates. The two-no-HASSIG case is absent because selection marks
    it DONTUSE. -/
theorem select_usable_source (left right : SatisfactionCandidate)
    (usable : (left.select right).status = .usable) :
    (left.select right = left ∧ left.status = .usable) ∨
      (left.select right = right ∧ right.status = .usable) := by
  cases leftHasSig : left.hasSig <;> cases rightHasSig : right.hasSig
  · have marked : (left.select right).status = .dontUse := by
      simp [SatisfactionCandidate.select, leftHasSig, rightHasSig]
    rw [marked] at usable
    contradiction
  · left
    have selected : left.select right = left := by
      simp [SatisfactionCandidate.select, leftHasSig, rightHasSig]
    exact ⟨selected, by simpa [selected] using usable⟩
  · right
    have selected : left.select right = right := by
      simp [SatisfactionCandidate.select, leftHasSig, rightHasSig]
    exact ⟨selected, by simpa [selected] using usable⟩
  · cases leftStatus : left.status <;> cases rightStatus : right.status
    · by_cases cheaper : left.cost ≤ right.cost
      · left
        have selected : left.select right = left := by
          rw [SatisfactionCandidate.select]
          simp only [leftHasSig, rightHasSig, leftStatus, rightStatus]
          change (if left.cost ≤ right.cost then left else right) = left
          simp [cheaper]
        exact ⟨selected, rfl⟩
      · right
        have selected : left.select right = right := by
          rw [SatisfactionCandidate.select]
          simp only [leftHasSig, rightHasSig, leftStatus, rightStatus]
          change (if left.cost ≤ right.cost then left else right) = right
          simp [cheaper]
        exact ⟨selected, rfl⟩
    · left
      exact ⟨by simp [SatisfactionCandidate.select, leftHasSig, rightHasSig,
        leftStatus, rightStatus], rfl⟩
    · right
      exact ⟨by simp [SatisfactionCandidate.select, leftHasSig, rightHasSig,
        leftStatus, rightStatus], rfl⟩
    · by_cases cheaper : left.cost ≤ right.cost
      · have selected : left.select right = left := by
          rw [SatisfactionCandidate.select]
          simp only [leftHasSig, rightHasSig, leftStatus, rightStatus]
          change (if left.cost ≤ right.cost then left else right) = left
          simp [cheaper]
        rw [selected, leftStatus] at usable
        contradiction
      · have selected : left.select right = right := by
          rw [SatisfactionCandidate.select]
          simp only [leftHasSig, rightHasSig, leftStatus, rightStatus]
          change (if left.cost ≤ right.cost then left else right) = right
          simp [cheaper]
        rw [selected, rightStatus] at usable
        contradiction

end SatisfactionCandidate

namespace CandidateResult

/-- Every usable witness projected from `result` satisfies `predicate`. -/
def Supports (result : CandidateResult) (predicate : Witness → Prop) : Prop :=
  ∀ witness, result.usableWitness? = some witness → predicate witness

/-- Apply a support invariant to a projected usable witness. -/
theorem Supports.of_usableWitness {result : CandidateResult}
    {predicate : Witness → Prop} (supported : result.Supports predicate)
    {witness : Witness}
    (selected : result.usableWitness? = some witness) : predicate witness :=
  supported witness selected

/-- An impossible result supports every usable-witness invariant. -/
theorem supports_impossible (predicate : Witness → Prop) :
    (CandidateResult.impossible : CandidateResult).Supports predicate := by
  intro witness selected
  simp at selected

/-- Strengthen or re-express the invariant carried by every usable witness. -/
theorem Supports.mono {result : CandidateResult}
    {source target : Witness → Prop}
    (supported : result.Supports source)
    (implication : ∀ witness, source witness → target witness) :
    result.Supports target := by
  intro witness selected
  exact implication witness (supported witness selected)

/-- A freshly usable candidate supports a predicate exactly when its witness
    does. -/
theorem supports_usable {predicate : Witness → Prop} {witness : Witness}
    {hasSig : Bool} (supported : predicate witness) :
    (CandidateResult.usable witness hasSig).Supports predicate := by
  intro selectedWitness selected
  simp only [usable_witness?, Option.some.injEq] at selected
  subst selectedWitness
  exact supported

/-- Selecting a usable witness never invents it: it came unchanged from one of
    the two alternatives. -/
theorem select_usableWitness_cases {left right : CandidateResult}
    {witness : Witness}
    (selected : (left.select right).usableWitness? = some witness) :
    left.usableWitness? = some witness ∨ right.usableWitness? = some witness := by
  cases left with
  | impossible => exact Or.inr selected
  | candidate left =>
      cases right with
      | impossible => exact Or.inl selected
      | candidate right =>
          cases status : (left.select right).status with
          | dontUse =>
              simp [CandidateResult.select, CandidateResult.usableWitness?,
                status] at selected
          | usable =>
              have source := SatisfactionCandidate.select_usable_source
                left right status
              rcases source with ⟨chosen, leftUsable⟩ | ⟨chosen, rightUsable⟩
              · left
                simpa [CandidateResult.select, CandidateResult.usableWitness?,
                  status, chosen, leftUsable] using selected
              · right
                simpa [CandidateResult.select, CandidateResult.usableWitness?,
                  status, chosen, rightUsable] using selected

/-- Support is closed under BIP candidate selection. -/
theorem Supports.select {left right : CandidateResult}
    {predicate : Witness → Prop}
    (leftSupported : left.Supports predicate)
    (rightSupported : right.Supports predicate) :
    (left.select right).Supports predicate := by
  intro witness selected
  rcases select_usableWitness_cases selected with fromLeft | fromRight
  · exact leftSupported witness fromLeft
  · exact rightSupported witness fromRight

/-- When the canonical empty `j` dissatisfaction is the left selection input,
    every usable selected witness is that exact singleton. A no-HASSIG right
    alternative either loses to it or makes the two-no-HASSIG row DONTUSE. -/
theorem usable_false_select_witness {other : CandidateResult}
    {witness : Witness}
    (selected : CandidateResult.usableWitness?
      ((CandidateResult.usable [falseElement] false).select other) =
        some witness) :
    witness = [falseElement] := by
  cases other with
  | impossible =>
      have equal : [falseElement] = witness := by simpa using selected
      exact equal.symm
  | candidate other =>
      rcases other with ⟨otherWitness, otherHasSig, otherStatus, otherOrigin⟩
      cases otherHasSig <;> cases otherStatus <;>
        simp [CandidateResult.usable, CandidateResult.select,
          CandidateResult.usableWitness?, SatisfactionCandidate.select] at selected
      all_goals exact selected.symm

/-- A usable combined witness decomposes into usable component witnesses in
    fragment execution order. -/
theorem combine_usableWitness_iff {left right : CandidateResult}
    {witness : Witness} :
    (left.combine right).usableWitness? = some witness ↔
      ∃ leftWitness rightWitness,
        left.usableWitness? = some leftWitness ∧
        right.usableWitness? = some rightWitness ∧
        witness = Witness.combine leftWitness rightWitness := by
  cases left with
  | impossible => simp [CandidateResult.combine]
  | candidate left =>
      cases right with
      | impossible => simp [CandidateResult.combine]
      | candidate right =>
          rcases left with ⟨leftWitness, leftHasSig, leftStatus, leftOrigin⟩
          rcases right with ⟨rightWitness, rightHasSig, rightStatus, rightOrigin⟩
          cases leftStatus <;> cases rightStatus <;>
            simp [CandidateResult.combine, CandidateResult.usableWitness?,
              SatisfactionCandidate.combine, CandidateStatus.combine, eq_comm]

/-- Support through candidate composition records the two source witnesses and
    their exact serialized-order combination. -/
theorem Supports.combine {left right : CandidateResult}
    {leftPredicate rightPredicate : Witness → Prop}
    (leftSupported : left.Supports leftPredicate)
    (rightSupported : right.Supports rightPredicate) :
    (left.combine right).Supports fun witness =>
      ∃ leftWitness rightWitness,
        witness = Witness.combine leftWitness rightWitness ∧
        leftPredicate leftWitness ∧ rightPredicate rightWitness := by
  intro witness selected
  rw [combine_usableWitness_iff] at selected
  obtain ⟨leftWitness, rightWitness, leftSelected, rightSelected, rfl⟩ := selected
  exact ⟨leftWitness, rightWitness, rfl,
    leftSupported leftWitness leftSelected,
    rightSupported rightWitness rightSelected⟩

/-- Selector insertion preserves the inner usable witness provenance. -/
theorem withSelector_usableWitness_iff {result : CandidateResult}
    {selector : StackElement} {witness : Witness} :
    (result.withSelector selector).usableWitness? = some witness ↔
      ∃ inner,
        result.usableWitness? = some inner ∧
        witness = inner.withSelector selector := by
  cases result with
  | impossible => simp [CandidateResult.withSelector]
  | candidate candidate =>
      rcases candidate with ⟨inner, hasSig, status, origin⟩
      cases status <;>
        simp [CandidateResult.withSelector, CandidateResult.usableWitness?,
          SatisfactionCandidate.withSelector, eq_comm]

theorem Supports.withSelector {result : CandidateResult}
    {predicate : Witness → Prop} (supported : result.Supports predicate)
    (selector : StackElement) :
    (result.withSelector selector).Supports fun witness =>
      ∃ inner, witness = inner.withSelector selector ∧ predicate inner := by
  intro witness selected
  rw [withSelector_usableWitness_iff] at selected
  obtain ⟨inner, innerSelected, rfl⟩ := selected
  exact ⟨inner, rfl, supported inner innerSelected⟩

/-- Non-canonical marking changes no usable witness. -/
theorem markNonCanonical_usableWitness_iff {result : CandidateResult}
    {witness : Witness} :
    result.markNonCanonical.usableWitness? = some witness ↔
      result.usableWitness? = some witness := by
  cases result with
  | impossible => simp [CandidateResult.markNonCanonical]
  | candidate candidate =>
      rcases candidate with ⟨inner, hasSig, status, origin⟩
      cases status <;>
        simp [CandidateResult.markNonCanonical, CandidateResult.usableWitness?,
          SatisfactionCandidate.markNonCanonical]

theorem Supports.markNonCanonical {result : CandidateResult}
    {predicate : Witness → Prop} (supported : result.Supports predicate) :
    result.markNonCanonical.Supports predicate := by
  intro witness selected
  exact supported witness (markNonCanonical_usableWitness_iff.mp selected)

/-- Explicit DONTUSE transforms have no usable output. -/
theorem supports_markDontUse (result : CandidateResult)
    (predicate : Witness → Prop) : result.markDontUse.Supports predicate := by
  intro witness selected
  cases result with
  | impossible => simp [CandidateResult.markDontUse] at selected
  | candidate candidate =>
      simp [CandidateResult.markDontUse, CandidateResult.usableWitness?,
        SatisfactionCandidate.markDontUse] at selected

/-- Overcomplete rows likewise have no usable output. -/
theorem supports_markOvercomplete (result : CandidateResult)
    (predicate : Witness → Prop) : result.markOvercomplete.Supports predicate := by
  intro witness selected
  cases result with
  | impossible => simp [CandidateResult.markOvercomplete] at selected
  | candidate candidate =>
      simp [CandidateResult.markOvercomplete, CandidateResult.usableWitness?,
        SatisfactionCandidate.markOvercomplete] at selected

/-- The runtime-top filter preserves the original witness and exposes its exact
    nonempty top-first stack decomposition. -/
theorem Supports.requireNonemptyRuntimeTop {result : CandidateResult}
    {predicate : Witness → Prop} (supported : result.Supports predicate) :
    result.requireNonemptyRuntimeTop.Supports fun witness =>
      predicate witness ∧
        ∃ top rest,
          witness.toInitialStack = top :: rest ∧ top.size ≠ 0 := by
  intro witness selected
  cases result with
  | impossible => simp [CandidateResult.requireNonemptyRuntimeTop] at selected
  | candidate candidate =>
      rcases candidate with ⟨inner, hasSig, status, origin⟩
      cases stack : inner.toInitialStack with
      | nil =>
          simp [CandidateResult.requireNonemptyRuntimeTop, stack] at selected
      | cons top rest =>
          by_cases empty : top.size = 0
          · simp [CandidateResult.requireNonemptyRuntimeTop, stack, empty] at selected
          · cases status with
            | dontUse =>
                simp [CandidateResult.requireNonemptyRuntimeTop, stack, empty,
                  CandidateResult.usableWitness?] at selected
            | usable =>
                simp [CandidateResult.requireNonemptyRuntimeTop, stack, empty,
                  CandidateResult.usableWitness?] at selected
                subst witness
                exact ⟨supported inner rfl, top, rest, stack, empty⟩

/-- Legacy multisignature finalization preserves usability while prepending the
    historical dummy and reversing the selected signature blocks. -/
theorem finalizeLegacyMulti_usableWitness_iff {result : CandidateResult}
    {witness : Witness} :
    (finalizeLegacyMulti result).usableWitness? = some witness ↔
      ∃ inner,
        result.usableWitness? = some inner ∧
        witness = falseElement :: inner.reverse := by
  cases result with
  | impossible => simp [finalizeLegacyMulti]
  | candidate candidate =>
      rcases candidate with ⟨inner, hasSig, status, origin⟩
      cases status <;>
        simp [finalizeLegacyMulti, CandidateResult.usableWitness?, eq_comm]

/-- Support through legacy multisignature finalization exposes the exact inner
    witness transformation. -/
theorem Supports.finalizeLegacyMulti {result : CandidateResult}
    {predicate : Witness → Prop} (supported : result.Supports predicate) :
    (finalizeLegacyMulti result).Supports fun witness =>
      ∃ inner,
        witness = falseElement :: inner.reverse ∧ predicate inner := by
  intro witness selected
  rw [finalizeLegacyMulti_usableWitness_iff] at selected
  obtain ⟨inner, innerSelected, rfl⟩ := selected
  exact ⟨inner, rfl, supported inner innerSelected⟩

end CandidateResult

namespace CandidatePair

/-- Local snoc induction avoids converting the candidate DP's source-order
    fold into a head-recursive presentation. -/
private theorem listSnocInduction {α : Type} {motive : List α → Prop}
    (nil : motive [])
    (snoc : ∀ (items : List α) (item : α),
      motive items → motive (items ++ [item])) :
    ∀ items, motive items := by
  intro items
  have reversed : motive items.reverse.reverse := by
    have aux : ∀ reversedItems : List α, motive reversedItems.reverse := by
      intro reversedItems
      induction reversedItems with
      | nil => simpa using nil
      | cons item reversedItems ih =>
          simpa using snoc reversedItems.reverse item ih
    exact aux items.reverse
  simpa using reversed

/-- A source-order explanation of an exact-count witness. `frames` records one
    selected child witness per child, while `witness` is their left-folded
    `Witness.combine` result. -/
inductive ChoiceTrace : List CandidatePair → Nat → List Witness → Witness → Prop
  | nil : ChoiceTrace [] 0 [] []
  | sat {children : List CandidatePair} {count : Nat}
      {frames : List Witness} {witness : Witness} {child : CandidatePair}
      {childWitness : Witness}
      (trace : ChoiceTrace children count frames witness)
      (selected : child.sat.usableWitness? = some childWitness) :
      ChoiceTrace (children ++ [child]) (count + 1)
        (frames ++ [childWitness]) (Witness.combine witness childWitness)
  | dsat {children : List CandidatePair} {count : Nat}
      {frames : List Witness} {witness : Witness} {child : CandidatePair}
      {childWitness : Witness}
      (trace : ChoiceTrace children count frames witness)
      (selected : child.dsat.usableWitness? = some childWitness) :
      ChoiceTrace (children ++ [child]) count
        (frames ++ [childWitness]) (Witness.combine witness childWitness)

/-- Source-order child choices, separated from the accumulated witness used by
    `ChoiceTrace`. The Boolean row records whether each child satisfaction or
    dissatisfaction supplied the corresponding witness frame. -/
inductive ChoiceFrames : List CandidatePair → List Bool → List Witness → Prop
  | nil : ChoiceFrames [] [] []
  | snocSat {children : List CandidatePair} {truths : List Bool}
      {frames : List Witness} {child : CandidatePair} {childWitness : Witness}
      (prior : ChoiceFrames children truths frames)
      (selected : child.sat.usableWitness? = some childWitness) :
      ChoiceFrames (children ++ [child]) (truths ++ [true])
        (frames ++ [childWitness])
  | snocDsat {children : List CandidatePair} {truths : List Bool}
      {frames : List Witness} {child : CandidatePair} {childWitness : Witness}
      (prior : ChoiceFrames children truths frames)
      (selected : child.dsat.usableWitness? = some childWitness) :
      ChoiceFrames (children ++ [child]) (truths ++ [false])
        (frames ++ [childWitness])

/-- A source-choice frame list has one truth bit and one witness frame per
    child. -/
theorem ChoiceFrames.lengths {children : List CandidatePair}
    {truths : List Bool} {frames : List Witness}
    (choices : ChoiceFrames children truths frames) :
    truths.length = children.length ∧ frames.length = children.length := by
  induction choices <;> simp_all

/-- Exact-count provenance exposes the individual source choices, and the
    number of satisfying rows is exactly the DP state index. -/
theorem ChoiceTrace.toChoiceFrames {children : List CandidatePair} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : ChoiceTrace children count frames witness) :
    ∃ truths, ChoiceFrames children truths frames ∧
      (truths.map Bool.toNat).sum = count := by
  induction trace with
  | nil => exact ⟨[], .nil, rfl⟩
  | sat trace selected ih =>
      obtain ⟨truths, choices, countEq⟩ := ih
      refine ⟨truths ++ [true], .snocSat choices selected, ?_⟩
      simp [countEq]
  | dsat trace selected ih =>
      obtain ⟨truths, choices, countEq⟩ := ih
      refine ⟨truths ++ [false], .snocDsat choices selected, ?_⟩
      simp [countEq]

private theorem replicateFalse_snoc (count : Nat) :
    List.replicate count false ++ [false] =
      List.replicate (count + 1) false := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (false :: ·) ih

/-- A zero-count source-choice trace consists entirely of dissatisfaction
    rows. -/
theorem ChoiceFrames.allFalse_of_sum_eq_zero
    {children : List CandidatePair} {truths : List Bool}
    {frames : List Witness} (choices : ChoiceFrames children truths frames)
    (sumEq : (truths.map Bool.toNat).sum = 0) :
    truths = List.replicate truths.length false := by
  induction choices with
  | nil => rfl
  | snocSat prior selected ih => simp at sumEq
  | @snocDsat children truths frames child childWitness prior selected ih =>
      simp only [List.map_append, List.map_cons, Bool.toNat_false,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero] at sumEq
      rw [ih sumEq]
      simpa using replicateFalse_snoc truths.length

/-- A trace has one argument frame for every source child. -/
theorem ChoiceTrace.frames_length {children : List CandidatePair} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : ChoiceTrace children count frames witness) :
    frames.length = children.length := by
  induction trace <;> simp_all

/-- The traced exact count cannot exceed the number of children. -/
theorem ChoiceTrace.count_le_length {children : List CandidatePair} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : ChoiceTrace children count frames witness) :
    count ≤ children.length := by
  induction trace <;> simp_all <;> omega

/-- Reversing the combined serialized witness yields the concatenation of the
    source-order top-first child frames. -/
theorem ChoiceTrace.toInitialStack {children : List CandidatePair} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : ChoiceTrace children count frames witness) :
    witness.toInitialStack =
      (frames.map Witness.toInitialStack).flatten := by
  induction trace with
  | nil => rfl
  | sat trace selected ih =>
      simp [Witness.toInitialStack_combine, ih]
  | dsat trace selected ih =>
      simp [Witness.toInitialStack_combine, ih]

/-- Bounded source frames imply that the combined exact-count witness is
    bounded as well. -/
theorem ChoiceTrace.itemsBounded {children : List CandidatePair} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : ChoiceTrace children count frames witness)
    (bounded : ∀ frame ∈ frames, frame.ItemsBounded) :
    witness.ItemsBounded := by
  induction trace with
  | nil => exact Witness.ItemsBounded.nil
  | sat trace selected ih =>
      apply Witness.ItemsBounded.combine
      · exact ih (fun frame member => bounded frame (by simp [member]))
      · exact bounded _ (by simp)
  | dsat trace selected ih =>
      apply Witness.ItemsBounded.combine
      · exact ih (fun frame member => bounded frame (by simp [member]))
      · exact bounded _ (by simp)

/-! ## Exact-count table provenance -/

/-- The zero-count entry of one DP extension keeps the previous zero-count
    state and composes the new child's dissatisfaction. -/
theorem extendCounts_getD_zero (states : List CandidateResult)
    (child : CandidatePair) :
    (extendCounts states child).getD 0 .impossible =
      (states.getD 0 .impossible).combine child.dsat := by
  cases states with
  | nil => simp [extendCounts, CandidateResult.combine]
  | cons head tail => simp [extendCounts]

/-- Every positive entry of one DP extension selects between retaining its
    count with the child's dissatisfaction and incrementing the previous count
    with the child's satisfaction. The order matches the executable left-tie
    rule. -/
theorem extendCounts_getD_succ (states : List CandidateResult)
    (child : CandidatePair) (count : Nat) :
    (extendCounts states child).getD (count + 1) .impossible =
      ((states.getD (count + 1) .impossible).combine child.dsat).select
        ((states.getD count .impossible).combine child.sat) := by
  rw [List.getD_eq_getElem?_getD]
  unfold extendCounts
  rw [List.getElem?_zipWith, List.getElem?_append, List.getElem?_cons_succ]
  simp only [List.length_map, List.getElem?_map]
  by_cases inBounds : count < states.length
  · by_cases nextInBounds : count + 1 < states.length
    · simp [inBounds, nextInBounds, List.getD_eq_getElem?_getD]
    · have nextPast : states.length ≤ count + 1 := by omega
      have atEnd : count + 1 - states.length = 0 := by omega
      simp [inBounds, nextInBounds, atEnd, List.getD_eq_getElem?_getD,
        CandidateResult.combine]
  · have past : states.length ≤ count := by omega
    have nextPast : states.length ≤ count + 1 := by omega
    simp [inBounds, nextPast, List.getD_eq_getElem?_getD,
      CandidateResult.combine, CandidateResult.select]

/-- A usable exact-count output has a source-order trace selecting exactly that
    many child satisfactions. -/
theorem selectExactly_choiceTrace {children : List CandidatePair} {count : Nat}
    {witness : Witness}
    (selected : (selectExactly count children).usableWitness? = some witness) :
    ∃ frames, ChoiceTrace children count frames witness := by
  induction children using listSnocInduction generalizing count witness with
  | nil =>
      cases count with
      | zero =>
          simp [selectExactly] at selected
          subst witness
          exact ⟨[], .nil⟩
      | succ count => simp [selectExactly] at selected
  | snoc children child ih =>
      cases count with
      | zero =>
          rw [selectExactly_append, extendCounts_getD_zero] at selected
          change ((selectExactly 0 children).combine child.dsat).usableWitness? =
            some witness at selected
          rw [CandidateResult.combine_usableWitness_iff] at selected
          obtain ⟨prefixWitness, childWitness, prefixSelected, childSelected,
            rfl⟩ := selected
          obtain ⟨frames, trace⟩ := ih prefixSelected
          exact ⟨frames ++ [childWitness], .dsat trace childSelected⟩
      | succ count =>
          rw [selectExactly_append, extendCounts_getD_succ] at selected
          change (((selectExactly (count + 1) children).combine child.dsat).select
            ((selectExactly count children).combine child.sat)).usableWitness? =
              some witness at selected
          rcases CandidateResult.select_usableWitness_cases selected with
            kept | incremented
          · rw [CandidateResult.combine_usableWitness_iff] at kept
            obtain ⟨prefixWitness, childWitness, prefixSelected, childSelected,
              rfl⟩ := kept
            obtain ⟨frames, trace⟩ := ih prefixSelected
            exact ⟨frames ++ [childWitness], .dsat trace childSelected⟩
          · rw [CandidateResult.combine_usableWitness_iff] at incremented
            obtain ⟨prefixWitness, childWitness, prefixSelected, childSelected,
              rfl⟩ := incremented
            obtain ⟨frames, trace⟩ := ih prefixSelected
            exact ⟨frames ++ [childWitness], .sat trace childSelected⟩

/-! ## Threshold dissatisfaction provenance -/

/-- Folding over positive threshold counts can preserve a usable witness only
    from the accumulator. Every newly offered row is first marked
    overcomplete, and therefore has no usable projection. -/
private theorem thresholdFold_usable_source
    (threshold : Nat) (entries : List (CandidateResult × Nat))
    (canonical : CandidateResult) {witness : Witness}
    (selected :
      (entries.foldl
        (fun current entry =>
          if entry.2 = threshold then current
          else current.select entry.1.markOvercomplete)
        canonical).usableWitness? = some witness) :
    canonical.usableWitness? = some witness := by
  induction entries generalizing canonical with
  | nil => exact selected
  | cons entry entries ih =>
      simp only [List.foldl_cons] at selected
      have fromStep := ih _ selected
      by_cases skipped : entry.2 = threshold
      · simpa [skipped] using fromStep
      · simp only [skipped, ↓reduceIte] at fromStep
        rcases CandidateResult.select_usableWitness_cases fromStep with
          fromCanonical | fromOvercomplete
        · exact fromCanonical
        · exact False.elim
            ((CandidateResult.supports_markOvercomplete entry.1
              (fun _ => False)).of_usableWitness fromOvercomplete)

/-- A usable threshold dissatisfaction comes unchanged from the canonical
    count-zero head state. This is intentionally one-way: arbitrary retained
    overcomplete witnesses are possible but cannot be projected as usable. -/
theorem thresholdDissatisfaction_usableWitness_source
    {threshold : Nat} {states : List CandidateResult} {witness : Witness}
    (selected :
      (thresholdDissatisfaction threshold states).usableWitness? = some witness) :
    (states.getD 0 .impossible).usableWitness? = some witness := by
  cases states with
  | nil => simp [thresholdDissatisfaction] at selected
  | cons canonical positiveCounts =>
      simpa using thresholdFold_usable_source threshold
        (positiveCounts.zipIdx 1) canonical selected

/-- A usable threshold dissatisfaction over an exact-count table traces to
    zero satisfied children. -/
theorem thresholdDissatisfaction_choiceTrace
    {threshold : Nat} {children : List CandidatePair} {witness : Witness}
    (selected :
      (thresholdDissatisfaction threshold (countCandidates children)).usableWitness? =
        some witness) :
    ∃ frames, ChoiceTrace children 0 frames witness := by
  have canonical := thresholdDissatisfaction_usableWitness_source selected
  exact selectExactly_choiceTrace (by simpa [selectExactly] using canonical)

end CandidatePair

end LeanMiniscript.Miniscript
