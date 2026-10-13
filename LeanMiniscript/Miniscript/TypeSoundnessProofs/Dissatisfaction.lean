import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type soundness: unconditional dissatisfaction

Every well-formed fragment whose type carries `d` has a possible
dissatisfaction candidate for every satisfaction environment.
-/

/-! ## Unconditional dissatisfaction completeness -/

/-- Every candidate pair in a list carries a possible raw dissatisfaction. -/
def AllDissatisfactionCandidatesPossible : List CandidatePair → Prop
  | [] => True
  | pair :: pairs =>
      pair.dsat.Possible ∧ AllDissatisfactionCandidatesPossible pairs

namespace AllDissatisfactionCandidatesPossible

/-- Project raw dissatisfaction possibility for one member of the list. -/
theorem of_mem {pairs : List CandidatePair}
    (all : AllDissatisfactionCandidatesPossible pairs)
    {pair : CandidatePair} (member : pair ∈ pairs) : pair.dsat.Possible := by
  induction pairs with
  | nil => simp at member
  | cons head tail ih =>
      simp only [AllDissatisfactionCandidatesPossible] at all
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact all.1
      · exact ih all.2 member

end AllDissatisfactionCandidatesPossible

mutual

/-- A well-formed typed fragment whose type carries `d` has a possible raw
    dissatisfaction candidate in every material environment. -/
theorem dissatisfactionCandidatePossible_of_wellFormed_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx)
    (dissatisfiable : ty.mods.d = true) :
    ∀ env, (satisfactionCandidates fragment env).dsat.Possible := by
  cases typed with
  | zero =>
      intro env
      exact CandidateResult.Possible.usable [] false
  | one => simp at dissatisfiable
  | pk_k key =>
      intro env
      simpa [satisfactionCandidates, keyCandidates] using
        (CandidateResult.Possible.usable [falseElement] false)
  | pk_h key =>
      intro env
      simpa [satisfactionCandidates, keyCandidates] using
        (CandidateResult.Possible.usable [falseElement, key.bytes] false)
  | older n => simp at dissatisfiable
  | after n => simp at dissatisfiable
  | sha256 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.sha256 hash)] false .canonical)
  | hash256 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.hash256 hash)] false .canonical)
  | ripemd160 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.ripemd160 hash)] false .canonical)
  | hash160 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.hash160 hash)] false .canonical)
  | and_v => simp at dissatisfiable
  | @and_b first second firstMods secondMods firstTyped secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have childD : firstMods.d = true ∧ secondMods.d = true := by
        simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 childD.1 env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2.1 childD.2 env
      have canonical := firstPossible.combine secondPossible
      simpa [satisfactionCandidates] using canonical.selectLeft.selectLeft
  | @or_b first second firstMods secondMods firstTyped firstD secondTyped secondD =>
      simp only [CoreFragment.WellFormed] at wellFormed
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2 secondD env
      simpa [satisfactionCandidates] using firstPossible.combine secondPossible
  | or_c => simp at dissatisfiable
  | @or_d first second firstMods secondMods firstTyped firstD firstUnit secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have secondD : secondMods.d = true := by simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2 secondD env
      simpa [satisfactionCandidates] using firstPossible.combine secondPossible
  | @or_i first second firstType secondType firstTyped secondTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have childD : firstType.mods.d = true ∨ secondType.mods.d = true :=
        by simpa using dissatisfiable
      intro env
      rcases childD with firstD | secondD
      · have possible :=
          dissatisfactionCandidatePossible_of_wellFormed_hasType
            firstTyped wellFormed.1 firstD env
        simpa [satisfactionCandidates] using
          (possible.withSelector trueElement).selectLeft
      · have possible :=
          dissatisfactionCandidatePossible_of_wellFormed_hasType
            secondTyped wellFormed.2 secondD env
        simpa [satisfactionCandidates] using
          (possible.withSelector falseElement).selectRight
  | @andor first second third firstMods secondType thirdType firstTyped firstD
      firstUnit secondTyped thirdTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have thirdD : thirdType.mods.d = true := by simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have thirdPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          thirdTyped wellFormed.2.2.1 thirdD env
      have canonical := firstPossible.combine thirdPossible
      simpa [satisfactionCandidates] using canonical.selectLeft
  | @c_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | v_wrap => simp at dissatisfiable
  | @a_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @s_wrap child mods childTyped oneArg =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @d_wrap child mods childTyped zeroArg =>
      intro env
      simpa [satisfactionCandidates] using
        (CandidateResult.Possible.usable [falseElement] false)
  | @j_wrap child mods childTyped nonzero =>
      intro env
      have canonical := CandidateResult.Possible.usable [falseElement] false
      simpa [satisfactionCandidates] using canonical.selectLeft
  | @n_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @thresh threshold first rest firstMods restTypes firstTyped firstD firstUnit
      restTyped restShape positive atMost =>
      have childrenWellFormed := wellFormed.2.1
      simp only [CoreFragment.allWellFormed] at childrenWellFormed
      have safe : ArithmeticScriptNatSafe threshold :=
        ArithmeticScriptNatSafe.of_lt (by
          simpa [MAX_BIP_ARITHMETIC_VALUE, MAX_BIP_LOCK_VALUE,
            maxArithmeticScriptNatExclusive] using
            wellFormed.2.2.2)
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped childrenWellFormed.1 firstD env
      have restPossible :=
        dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
          restTyped childrenWellFormed.2 restShape env
      have valid : candidateThresholdValid threshold (first :: rest).length :=
        ⟨by omega, atMost, safe⟩
      rw [satisfactionCandidates_thresh_valid threshold (first :: rest) env valid]
      apply CandidatePair.thresholdDissatisfaction_possible_of_children
      intro pair member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact firstPossible
      · apply AllDissatisfactionCandidatesPossible.of_mem
        · simpa [satisfactionCandidatesList_eq_map] using restPossible
        · exact member
  | multi threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
        simpa [validLegacyMultiKeyCount, maxPubKeysPerMultiSig] using
          wellFormed.2.2.1
      have guard : ¬ (threshold = 0 ∨ keys.length < threshold ∨
          maxPubKeysPerMultiSig < keys.length) := by
        simp only [not_or]
        exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBound⟩
      intro env
      simpa [satisfactionCandidates, legacyMultiCandidates, guard] using
        (CandidateResult.Possible.usable
          (List.replicate (threshold + 1) falseElement) false)
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
      intro env
      simpa [satisfactionCandidates, multiACandidates, valid] using
        (CandidateResult.Possible.usable
          (List.replicate keys.length falseElement) false)

/-- Pointwise list counterpart used by threshold completeness. -/
theorem dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
    {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType}
    (typed : HasTypeList scriptCtx fragments types)
    (wellFormed : CoreFragment.allWellFormed scriptCtx fragments)
    (restTypes : thresholdRestTypes types) :
    ∀ env, AllDissatisfactionCandidatesPossible
      (satisfactionCandidatesList fragments env) := by
  cases typed with
  | nil =>
      intro env
      trivial
  | @cons fragment ty fragments types headTyped tailTyped =>
      simp only [CoreFragment.allWellFormed] at wellFormed
      simp only [thresholdRestTypes] at restTypes
      intro env
      exact ⟨
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          headTyped wellFormed.1 restTypes.2.1 env,
        dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
          tailTyped wellFormed.2 restTypes.2.2.2 env⟩

end

/-- Every valid `d`-typed fragment has an unconditional raw dissatisfaction,
    including canonical candidates marked `DONTUSE`. -/
theorem unconditionalDissatisfaction_of_wellFormed_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx)
    (dissatisfiable : ty.mods.d = true) :
    UnconditionalDissatisfaction fragment := by
  intro env
  exact (dissatisfactionCandidatePossible_of_wellFormed_hasType
    typed wellFormed dissatisfiable env).witness

end LeanMiniscript.Miniscript
