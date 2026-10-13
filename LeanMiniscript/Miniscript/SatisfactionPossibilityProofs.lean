import LeanMiniscript.Miniscript.AtomMaterial
import LeanMiniscript.Miniscript.SatisfactionAvailability
import LeanMiniscript.Miniscript.TypeSoundnessProofs

/-!
# Satisfaction possibility

The concrete satisfier's raw candidate existence is compositional. For every
context-valid, well-typed Core Miniscript, a raw satisfaction candidate exists
in an environment exactly when the fragment is structurally satisfiable
(`CoreFragment.isSatisfiableWith`) under the atom material induced by that
environment.

Raw possibility includes candidates marked `DONTUSE`; the BIP 379 selection
and HASSIG policies applied by `satisfy` and `satisfyFinal` are a separate,
stricter projection.
-/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

namespace CandidateResult

/-- Executable form of `Possible`. -/
def isPossible : CandidateResult → Bool
  | .impossible => false
  | .candidate _ => true

@[simp] theorem isPossible_eq_true_iff (result : CandidateResult) :
    result.isPossible = true ↔ result.Possible := by
  cases result <;> simp [isPossible, Possible]

@[simp] theorem impossible_not_possible :
    ¬ (CandidateResult.impossible).Possible := by
  simp [Possible]

@[simp] theorem candidate_possible (candidate : SatisfactionCandidate) :
    (CandidateResult.candidate candidate).Possible := by
  simp [Possible]

@[simp] theorem usable_possible (witness : Witness) (hasSig : Bool) :
    (CandidateResult.usable witness hasSig).Possible :=
  Possible.usable witness hasSig

@[simp] theorem combine_possible_iff (left right : CandidateResult) :
    (left.combine right).Possible ↔ left.Possible ∧ right.Possible := by
  cases left <;> cases right <;> simp [combine, Possible]

@[simp] theorem select_possible_iff (left right : CandidateResult) :
    (left.select right).Possible ↔ left.Possible ∨ right.Possible := by
  cases left <;> cases right <;> simp [select, Possible]

@[simp] theorem withSelector_possible_iff (result : CandidateResult)
    (selector : StackElement) :
    (result.withSelector selector).Possible ↔ result.Possible := by
  cases result <;> simp [withSelector, Possible]

@[simp] theorem markNonCanonical_possible_iff (result : CandidateResult) :
    result.markNonCanonical.Possible ↔ result.Possible := by
  cases result <;> simp [markNonCanonical, Possible]

@[simp] theorem markOvercomplete_possible_iff (result : CandidateResult) :
    result.markOvercomplete.Possible ↔ result.Possible := by
  cases result <;> simp [markOvercomplete, Possible]

@[simp] theorem finalizeLegacyMulti_possible_iff (result : CandidateResult) :
    (finalizeLegacyMulti result).Possible ↔ result.Possible := by
  cases result <;> simp [finalizeLegacyMulti, Possible]

end CandidateResult

namespace CandidatePair

/-- Number of children with a possible raw satisfaction. -/
def satCount : List CandidatePair → Nat
  | [] => 0
  | child :: children =>
      (if child.sat.isPossible then 1 else 0) + satCount children

@[simp] theorem satCount_append (children : List CandidatePair)
    (child : CandidatePair) :
    satCount (children ++ [child]) =
      satCount children + (if child.sat.isPossible then 1 else 0) := by
  induction children with
  | nil => simp [satCount]
  | cons head tail ih => simp [satCount, ih]; omega

theorem satCount_le_length (children : List CandidatePair) :
    satCount children ≤ children.length := by
  induction children with
  | nil => simp [satCount]
  | cons head tail ih => simp only [satCount, List.length_cons]; split <;> omega

/-- Entry `j` of an extended exact-count table either keeps count `j` by
    dissatisfying the new child or reaches it from count `j - 1` by satisfying
    the new child. Out-of-range entries are impossible on both sides. -/
theorem extendCounts_getD (states : List CandidateResult)
    (child : CandidatePair) (j : Nat) :
    (extendCounts states child).getD j .impossible =
      ((states.getD j .impossible).combine child.dsat).select
        (match j with
          | 0 => .impossible
          | i + 1 => (states.getD i .impossible).combine child.sat) := by
  unfold extendCounts
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases j with
  | zero =>
      cases states with
      | nil => simp [CandidateResult.combine]
      | cons head tail => simp
  | succ i =>
      simp only [List.getElem?_cons_succ, List.getElem?_map]
      by_cases hi : i + 1 < states.length
      · have hi' : i < states.length := by omega
        rw [List.getElem?_append_left (by simpa using hi)]
        simp [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', List.getD_eq_getElem?_getD]
      · by_cases hEq : i + 1 = states.length
        · have hi' : i < states.length := by omega
          rw [List.getElem?_append_right (by simp; omega)]
          simp [List.getElem?_eq_getElem hi', List.getD_eq_getElem?_getD,
            hEq, CandidateResult.combine]
        · have hNone : states[i]? = none := List.getElem?_eq_none (by omega)
          have hNone' : states[i + 1]? = none :=
            List.getElem?_eq_none (by omega)
          rw [List.getElem?_append_right (by simp; omega)]
          simp [hNone, hNone', List.getD_eq_getElem?_getD,
            CandidateResult.combine]

/-- One table transition over a child with a possible dissatisfaction adds
    the child's satisfaction possibility to the reachable count bound. -/
theorem extendCounts_getD_possible_iff (states : List CandidateResult)
    (child : CandidatePair) (bound : Nat)
    (statesPossible : ∀ j, (states.getD j .impossible).Possible ↔ j ≤ bound)
    (childDsat : child.dsat.Possible) (j : Nat) :
    ((extendCounts states child).getD j .impossible).Possible ↔
      j ≤ bound + (if child.sat.isPossible then 1 else 0) := by
  rw [extendCounts_getD]
  cases j with
  | zero =>
      have := (statesPossible 0).mpr (Nat.zero_le _)
      simp only [CandidateResult.select_possible_iff,
        CandidateResult.combine_possible_iff, this, childDsat]
      simp
  | succ i =>
      simp only [CandidateResult.select_possible_iff,
        CandidateResult.combine_possible_iff, statesPossible, childDsat,
        and_true]
      by_cases hSat : child.sat.Possible
      · have hSat' : child.sat.isPossible = true := by simpa using hSat
        simp only [hSat, hSat', and_true, if_true]
        omega
      · have hSat' : child.sat.isPossible = false := by
          cases h : child.sat.isPossible
          · rfl
          · exact absurd ((CandidateResult.isPossible_eq_true_iff _).mp h) hSat
        simp only [hSat, hSat', and_false, or_false]
        simp

/-- Folding table transitions preserves the reachable-count characterization. -/
theorem foldl_extendCounts_getD_possible_iff (children : List CandidatePair)
    (childrenDsat : ∀ child, child ∈ children → child.dsat.Possible) :
    ∀ (states : List CandidateResult) (bound : Nat),
      (∀ j, (states.getD j .impossible).Possible ↔ j ≤ bound) →
      ∀ j, ((children.foldl extendCounts states).getD j .impossible).Possible ↔
        j ≤ bound + satCount children := by
  induction children with
  | nil => intro states bound h j; simpa [satCount] using h j
  | cons child children ih =>
      intro states bound h j
      simp only [List.foldl_cons]
      have hChild : child.dsat.Possible := childrenDsat child (by simp)
      have hRest : ∀ c, c ∈ children → c.dsat.Possible :=
        fun c member => childrenDsat c (by simp [member])
      rw [ih hRest (extendCounts states child)
        (bound + (if child.sat.isPossible then 1 else 0))
        (extendCounts_getD_possible_iff states child bound h hChild) j]
      simp only [satCount]
      omega

/-- When every child has a possible raw dissatisfaction, exactly `j` children
    can be satisfied precisely when `j` does not exceed the number of children
    with a possible raw satisfaction. -/
theorem countCandidates_getD_possible_iff (children : List CandidatePair)
    (childrenDsat : ∀ child, child ∈ children → child.dsat.Possible)
    (j : Nat) :
    ((countCandidates children).getD j .impossible).Possible ↔
      j ≤ satCount children := by
  have base : ∀ j, (([CandidateResult.usable [] false] : List CandidateResult).getD
      j .impossible).Possible ↔ j ≤ 0 := by
    intro j
    cases j <;> simp [CandidateResult.usable]
  have := foldl_extendCounts_getD_possible_iff children childrenDsat _ 0 base j
  simpa [countCandidates] using this

/-- Exact-count selection is possible precisely when enough children have
    possible raw satisfactions, provided every child can be dissatisfied. -/
theorem selectExactly_possible_iff (count : Nat) (children : List CandidatePair)
    (childrenDsat : ∀ child, child ∈ children → child.dsat.Possible) :
    (selectExactly count children).Possible ↔ count ≤ satCount children := by
  rw [selectExactly_eq_getD]
  exact countCandidates_getD_possible_iff children childrenDsat count

end CandidatePair

namespace SatisfactionPossibility

/-- Legacy multisignature key choices are satisfiable exactly for keys with a
    returned signature. -/
theorem satCount_legacyMultiKeyChoices (keys : List PubKey) (env : SatEnv) :
    CandidatePair.satCount (keys.map (fun key => legacyMultiKeyChoice key env)) =
      env.material.signerCount keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.map_cons, CandidatePair.satCount, Material.signerCount, ih]
      cases h : env.signatureFor key <;>
        simp [legacyMultiKeyChoice, SatEnv.material, h,
          CandidateResult.isPossible, CandidateResult.usable]

/-- `multi_a` key choices are satisfiable exactly for keys with a returned
    signature. -/
theorem satCount_multiAKeyChoices (keys : List PubKey) (env : SatEnv) :
    CandidatePair.satCount (keys.map (fun key => multiAKeyChoice key env)) =
      env.material.signerCount keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.map_cons, CandidatePair.satCount, Material.signerCount, ih]
      cases h : env.signatureFor key <;>
        simp [multiAKeyChoice, SatEnv.material, h,
          CandidateResult.isPossible, CandidateResult.usable]

theorem legacyMultiKeyChoices_dsat (keys : List PubKey) (env : SatEnv) :
    ∀ child, child ∈ keys.map (fun key => legacyMultiKeyChoice key env) →
      child.dsat.Possible := by
  intro child member
  simp only [List.mem_map] at member
  obtain ⟨key, _, rfl⟩ := member
  simp [legacyMultiKeyChoice]

theorem multiAKeyChoices_dsat (keys : List PubKey) (env : SatEnv) :
    ∀ child, child ∈ keys.map (fun key => multiAKeyChoice key env) →
      child.dsat.Possible := by
  intro child member
  simp only [List.mem_map] at member
  obtain ⟨key, _, rfl⟩ := member
  simp [multiAKeyChoice]

end SatisfactionPossibility

open SatisfactionPossibility in
mutual

/-- Raw satisfaction candidates are exactly structural satisfiability under
    the environment's atom material, for every context-valid typed fragment.

    The forward direction says the satisfier never invents a satisfaction
    that structural satisfiability rules out; the backward direction says it
    finds a raw candidate (possibly `DONTUSE`) whenever the available
    signatures, preimages, and timelocks admit one. -/
theorem satisfactionPossible_iff_isSatisfiableWith
    {ctx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType ctx fragment ty)
    (wellFormed : fragment.WellFormed ctx) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat.Possible ↔
      fragment.isSatisfiableWith env.material.atom = true := by
  cases typed with
  | zero => simp [CoreFragment.isSatisfiableWith]
  | one => simp [CoreFragment.isSatisfiableWith]
  | pk_k key =>
      cases h : env.signatureFor key <;>
        simp [keyCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | pk_h key =>
      cases h : env.signatureFor key <;>
        simp [keyCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | older n =>
      by_cases h : sequenceSatisfied n env.txCtx <;>
        simp [h, CoreFragment.isSatisfiableWith, Material.atom, SatEnv.material]
  | after n =>
      by_cases h : locktimeSatisfied n env.txCtx <;>
        simp [h, CoreFragment.isSatisfiableWith, Material.atom, SatEnv.material]
  | sha256 hash =>
      cases h : env.preimageFor (.sha256 hash) <;>
        simp [hashCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | hash256 hash =>
      cases h : env.preimageFor (.hash256 hash) <;>
        simp [hashCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | ripemd160 hash =>
      cases h : env.preimageFor (.ripemd160 hash) <;>
        simp [hashCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | hash160 hash =>
      cases h : env.preimageFor (.hash160 hash) <;>
        simp [hashCandidates, h, CoreFragment.isSatisfiableWith,
          Material.atom, SatEnv.material]
  | @and_v first second _ _ firstTyped secondTyped _ =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2.1 env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond]
  | @and_b first second _ _ firstTyped secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2.1 env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond]
  | @or_b first second _ _ firstTyped firstD secondTyped secondD =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2 env
      have firstDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        firstTyped wellFormed.1 firstD env
      have secondDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        secondTyped wellFormed.2 secondD env
      simp only [satisfactionCandidates, CandidateResult.select_possible_iff,
        CandidateResult.combine_possible_iff,
        CandidateResult.markOvercomplete_possible_iff, firstDsat, secondDsat,
        and_true, true_and, CoreFragment.isSatisfiableWith, Bool.or_eq_true,
        ← ihFirst, ← ihSecond]
      constructor
      · rintro ((h | h) | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
  | @or_c first second _ _ firstTyped firstD _ secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2 env
      have firstDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        firstTyped wellFormed.1 firstD env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond, firstDsat]
  | @or_d first second _ _ firstTyped firstD _ secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2 env
      have firstDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        firstTyped wellFormed.1 firstD env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond, firstDsat]
  | @or_i first second _ _ firstTyped secondTyped _ _ =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2 env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond]
  | @andor first second third _ _ _ firstTyped firstD _ secondTyped thirdTyped _ _ =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped wellFormed.1 env
      have ihSecond := satisfactionPossible_iff_isSatisfiableWith
        secondTyped wellFormed.2.1 env
      have ihThird := satisfactionPossible_iff_isSatisfiableWith
        thirdTyped wellFormed.2.2.1 env
      have firstDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        firstTyped wellFormed.1 firstD env
      simp [CoreFragment.isSatisfiableWith, ihFirst, ihSecond, ihThird, firstDsat]
  | @c_wrap child _ childTyped =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @v_wrap child _ childTyped =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @a_wrap child _ childTyped =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @s_wrap child _ childTyped _ =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @d_wrap child _ childTyped _ =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @j_wrap child _ childTyped _ =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @n_wrap child _ childTyped =>
      have ih := satisfactionPossible_iff_isSatisfiableWith childTyped wellFormed env
      simpa [CoreFragment.isSatisfiableWith] using ih
  | @thresh threshold first rest firstMods restTypes firstTyped firstD firstUnit
      restTyped restShape positive atMost =>
      have childrenWellFormed := wellFormed.2.1
      simp only [CoreFragment.allWellFormed] at childrenWellFormed
      have safe : ArithmeticScriptNatSafe threshold :=
        ArithmeticScriptNatSafe.of_lt (by
          simpa [MAX_BIP_ARITHMETIC_VALUE, MAX_BIP_LOCK_VALUE,
            maxArithmeticScriptNatExclusive] using
            wellFormed.2.2.2)
      have valid : candidateThresholdValid threshold (first :: rest).length :=
        ⟨by omega, atMost, safe⟩
      have firstDsat := dissatisfactionCandidatePossible_of_wellFormed_hasType
        firstTyped childrenWellFormed.1 firstD env
      have restDsat :=
        dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
          restTyped childrenWellFormed.2 restShape env
      have childrenDsat : ∀ pair, pair ∈
          (first :: rest).map (fun fragment => satisfactionCandidates fragment env) →
          pair.dsat.Possible := by
        intro pair member
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact firstDsat
        · apply AllDissatisfactionCandidatesPossible.of_mem
          · simpa [satisfactionCandidatesList_eq_map] using restDsat
          · exact member
      have ihFirst := satisfactionPossible_iff_isSatisfiableWith
        firstTyped childrenWellFormed.1 env
      have ihRest := satCount_satisfactionCandidates
        restTyped childrenWellFormed.2 env
      rw [satisfactionCandidates_thresh_sat threshold (first :: rest) env valid,
        CandidatePair.selectExactly_possible_iff _ _ childrenDsat]
      have hFirst : (satisfactionCandidates first env).sat.isPossible =
          first.isSatisfiableWith env.material.atom := by
        apply Bool.eq_iff_iff.mpr
        simpa using ihFirst
      simp only [CoreFragment.isSatisfiableWith, CoreFragment.countSatisfiableWith,
        List.map_cons, CandidatePair.satCount, ihRest, hFirst, decide_eq_true_eq]
  | multi threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
        simpa [validLegacyMultiKeyCount, maxPubKeysPerMultiSig] using
          wellFormed.2.2.1
      have guard : ¬ (threshold = 0 ∨ keys.length < threshold ∨
          maxPubKeysPerMultiSig < keys.length) := by
        simp only [not_or]
        exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBound⟩
      simp only [satisfactionCandidates, legacyMultiCandidates, guard,
        if_false, CandidateResult.finalizeLegacyMulti_possible_iff]
      rw [CandidatePair.selectExactly_possible_iff _ _
        (legacyMultiKeyChoices_dsat keys env),
        satCount_legacyMultiKeyChoices]
      simp [CoreFragment.isSatisfiableWith, Material.atom]
  | multi_a threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A :=
        wellFormed.2.2.1
      have safe : ArithmeticScriptNatSafe threshold :=
        ArithmeticScriptNatSafe.of_lt (by
          change threshold < 2147483648
          have : threshold ≤ 999 := by
            simpa [MAX_PUBKEYS_PER_MULTI_A] using Nat.le_trans atMost keyBound
          omega)
      have valid : candidateThresholdValid threshold keys.length :=
        ⟨by omega, atMost, safe⟩
      simp only [satisfactionCandidates, multiACandidates, valid, if_true]
      rw [CandidatePair.selectExactly_possible_iff _ _
        (multiAKeyChoices_dsat keys env), satCount_multiAKeyChoices]
      simp [CoreFragment.isSatisfiableWith, Material.atom]

/-- Pointwise list counterpart: the number of threshold children with a raw
    satisfaction candidate is their structural satisfiable count. -/
theorem satCount_satisfactionCandidates
    {ctx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType}
    (typed : HasTypeList ctx fragments types)
    (wellFormed : CoreFragment.allWellFormed ctx fragments) (env : SatEnv) :
    CandidatePair.satCount
        (fragments.map (fun fragment => satisfactionCandidates fragment env)) =
      CoreFragment.countSatisfiableWith env.material.atom fragments := by
  cases typed with
  | nil => rfl
  | @cons fragment _ fragments _ headTyped tailTyped =>
      simp only [CoreFragment.allWellFormed] at wellFormed
      have ihHead := satisfactionPossible_iff_isSatisfiableWith
        headTyped wellFormed.1 env
      have ihTail := satCount_satisfactionCandidates tailTyped wellFormed.2 env
      have hHead : (satisfactionCandidates fragment env).sat.isPossible =
          fragment.isSatisfiableWith env.material.atom := by
        apply Bool.eq_iff_iff.mpr
        simpa using ihHead
      simp only [List.map_cons, CandidatePair.satCount,
        CoreFragment.countSatisfiableWith, hHead, ihTail]

end

end LeanMiniscript.Miniscript
