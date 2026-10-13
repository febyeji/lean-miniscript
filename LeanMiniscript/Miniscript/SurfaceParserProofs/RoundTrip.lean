import LeanMiniscript.Miniscript.SurfaceParser
import LeanMiniscript.Miniscript.SurfaceParserProofs.CanonicalExpr

namespace LeanMiniscript.Miniscript

namespace SurfaceParser

/-!
# Surface parser proofs: canonical round trip

Every normalized, well-formed fragment renders to canonical surface text that
elaborates back to it, so unchecked parsing inverts pretty printing.

Some helpers here were `private` in the former single-file `SurfaceParserProofs`
module. They are visible only so that sibling submodules can use them; treat
them as internal proof helpers, not stable API.
-/

/-- Drop an empty wrapper chain from a canonical correctness fact. -/
private theorem canonicalExprCorrect_of_emptyChain
    {context : ScriptContext} {expr : SurfaceText.Expr}
    {fragment : SurfaceFragment}
    (hCorrect : CanonicalExprCorrect context expr
      (wrapSurfaceChain "" fragment)) :
    CanonicalExprCorrect context expr fragment := by
  simpa [wrapSurfaceChain] using hCorrect

/-- Move one canonical wrapper letter from the target fragment onto the
accumulated wrapper chain: correctness under `wrappers ++ [wrapper]` for the
inner fragment gives correctness under `wrappers` for
`wrapSurface wrapper inner`. -/
private theorem canonicalExprCorrect_appendWrapper
    {context : ScriptContext} {expr : SurfaceText.Expr}
    (wrappers : String) (wrapper : Char) (inner target : SurfaceFragment)
    (hWrappers : CanonicalWrappers wrappers)
    (hWrapper : CanonicalWrapper wrapper)
    (hStep : wrapSurface wrapper inner = target)
    (hRecursive : CanonicalWrappers (wrappers ++ String.ofList [wrapper]) →
      CanonicalExprCorrect context expr
        (wrapSurfaceChain (wrappers ++ String.ofList [wrapper]) inner)) :
    CanonicalExprCorrect context expr (wrapSurfaceChain wrappers target) := by
  have hCorrect := hRecursive
    (canonicalWrappers_append_char wrappers wrapper hWrappers hWrapper)
  have hSingle : wrapSurfaceChain (String.ofList [wrapper]) inner = target := by
    simpa [wrapSurfaceChain] using hStep
  rwa [wrapSurfaceChain_append, hSingle] at hCorrect

/-- Canonical correctness of a binary core combinator call whose elaborator
rebuilds the combinator from the desugared elaborated children. -/
private theorem canonicalExprCorrect_coreBinaryCall
    (context : ScriptContext) (name : String)
    (build : CoreFragment → CoreFragment → CoreFragment)
    (first second : CoreFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hFirst : CanonicalExprCorrect context
      (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
      (normalizeCoreAsSurface first))
    (hSecond : CanonicalExprCorrect context
      (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
      (normalizeCoreAsSurface second))
    (hElaborate : ∀ (fuel callPosition : Nat)
      (firstRaw secondRaw : RawSurfaceExpr) (x y : SurfaceFragment),
      elaborateRawFuel context resolveHexKey fuel firstRaw = .ok x →
      elaborateRawFuel context resolveHexKey fuel secondRaw = .ok y →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name [firstRaw, secondRaw]) =
          .ok (.core (build (desugar x) (desugar y)))) :
    CanonicalExprCorrect context
      (.call name
        [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
          SurfaceText.coreExprWithWrappers prettyPubKey "" second])
      (.core (build first second)) := by
  apply canonicalExprCorrect_binaryCall context name _ _ _ _ _ hNameSafe
    hFirst hSecond
  intro fuel callPosition firstRaw secondRaw hFirstRaw hSecondRaw
  rw [hElaborate fuel callPosition firstRaw secondRaw _ _ hFirstRaw hSecondRaw,
    desugar_normalizeCoreAsSurface, desugar_normalizeCoreAsSurface]

/-- Canonical correctness of a threshold call `name(k, arguments...)` with a
nonempty argument list, reduced to elaborating the already split raw
arguments. -/
private theorem canonicalExprCorrect_thresholdCall
    (context : ScriptContext) (name : String) (threshold : Nat)
    (arguments : List SurfaceText.Expr) (fragment : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hNonempty : arguments ≠ [])
    (hArgumentsSafe : ∀ argument ∈ arguments, argument.AtomsSafe)
    (hElaborate : ∀ (fuel callPosition thresholdPosition : Nat)
      (rest : List RawSurfaceExpr),
      rest.map RawSurfaceExpr.toExpr = arguments →
      rest.isEmpty = false →
      (∀ expr ∈ arguments, expr.lexemes.length < fuel) →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name
          (.atom thresholdPosition (toString threshold) :: rest)) =
        .ok fragment) :
    CanonicalExprCorrect context
      (.call name
        (SurfaceText.variadicArguments (.atom (toString threshold)) arguments))
      fragment := by
  rw [SurfaceText.variadicArguments_of_ne_nil _ _ hNonempty]
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hMem
    · unfold SurfaceText.Expr.AtomsSafe
      exact atomSafe_toString threshold
    · exact hArgumentsSafe argument hMem
  · intro fuel callPosition raws hMap hFuel
    obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
      rawExprMap_eq_cons raws (.atom (toString threshold)) arguments hMap
    have hRestNonempty : rest.isEmpty = false := by
      cases rest with
      | nil => exact False.elim (hNonempty (by simpa using hRest.symm))
      | cons => rfl
    cases thresholdRaw with
    | atom thresholdPosition token =>
        simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
        cases hThresholdRaw
        cases fuel with
        | zero => simp at hFuel
        | succ fuel =>
            apply hElaborate fuel callPosition thresholdPosition rest hRest
              hRestNonempty
            intro expr hMem
            have hLess := lexemes_length_lt_call_of_mem name
              (.atom (toString threshold) :: arguments) expr (by simp [hMem])
            omega
    | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
    | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw

mutual
  private theorem coreExprCanonicalCorrect
      (context : ScriptContext) (wrappers : String)
      (fragment : CoreFragment)
      (hWrappers : CanonicalWrappers wrappers)
      (hWellFormed : fragment.WellFormed context) :
      CanonicalExprCorrect context
        (SurfaceText.coreExprWithWrappers prettyPubKey wrappers fragment)
        (wrapSurfaceChain wrappers (normalizeCoreAsSurface fragment)) := by
    cases fragment with
    | zero =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers (.atom "0")
            (.core .zero) hWrappers (canonicalExprCorrect_zero context)
    | one =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers (.atom "1")
            (.core .one) hWrappers (canonicalExprCorrect_one context)
    | pk_k key =>
        have hBody := canonicalExprCorrect_pk_k context key hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | pk_h key =>
        have hBody := canonicalExprCorrect_pk_h context key hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | older value =>
        have hBody := canonicalExprCorrect_older context value
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | after value =>
        have hBody := canonicalExprCorrect_after context value
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | sha256 hash =>
        have hBody := canonicalExprCorrect_sha256 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | hash256 hash =>
        have hBody := canonicalExprCorrect_hash256 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | ripemd160 hash =>
        have hBody := canonicalExprCorrect_ripemd160 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | hash160 hash =>
        have hBody := canonicalExprCorrect_hash160 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | and_b first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "and_b" .and_b
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2.1))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_b first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "or_b" .or_b
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_c first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "or_c" .or_c
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_d first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "or_d" .or_d
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | a inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 'a'
            (normalizeCoreAsSurface inner) (.core (.a inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "a") inner · hWellFormed)
    | s inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 's'
            (normalizeCoreAsSurface inner) (.core (.s inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "s") inner · hWellFormed)
    | d inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 'd'
            (normalizeCoreAsSurface inner) (.core (.d inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "d") inner · hWellFormed)
    | v inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 'v'
            (normalizeCoreAsSurface inner) (.core (.v inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "v") inner · hWellFormed)
    | j inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 'j'
            (normalizeCoreAsSurface inner) (.core (.j inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "j") inner · hWellFormed)
    | n inner =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_appendWrapper wrappers 'n'
            (normalizeCoreAsSurface inner) (.core (.n inner)) hWrappers
            (by simp [CanonicalWrapper])
            (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
            (coreExprCanonicalCorrect context (wrappers ++ "n") inner · hWellFormed)
    | and_v first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "and_v" .and_v
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2.1))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        cases second with
        | one =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_appendWrapper wrappers 't'
                (normalizeCoreAsSurface first) (.t (normalizeCoreAsSurface first))
                hWrappers (by simp [CanonicalWrapper]) (by simp [wrapSurface])
                (coreExprCanonicalCorrect context (wrappers ++ "t") first ·
                  hWellFormed.1)
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | andor first second third =>
        have hFirst := canonicalExprCorrect_of_emptyChain
          (coreExprCanonicalCorrect context "" first canonicalWrappers_empty
            hWellFormed.1)
        have hSecond := canonicalExprCorrect_of_emptyChain
          (coreExprCanonicalCorrect context "" second canonicalWrappers_empty
            hWellFormed.2.1)
        have hThird := canonicalExprCorrect_of_emptyChain
          (coreExprCanonicalCorrect context "" third canonicalWrappers_empty
            hWellFormed.2.2.1)
        have hBody : CanonicalExprCorrect context
            (.call "andor"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second,
                SurfaceText.coreExprWithWrappers prettyPubKey "" third])
            (.core (.andor first second third)) := by
          apply canonicalExprCorrect_ternaryCall context "andor" _ _ _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · exact hThird
          · intro fuel position firstRaw secondRaw thirdRaw hFirstRaw hSecondRaw
              hThirdRaw
            simp [elaborateRawFuel, ternaryArguments]
            rw [hFirstRaw, hSecondRaw, hThirdRaw]
            change Except.ok (SurfaceFragment.core (.andor (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second))
              (desugar (normalizeCoreAsSurface third)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second,
              desugar_normalizeCoreAsSurface third]
        cases third with
        | zero =>
            have hSugar : CanonicalExprCorrect context
                (.call "and_n"
                  [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                    SurfaceText.coreExprWithWrappers prettyPubKey "" second])
                (.and_n (normalizeCoreAsSurface first)
                  (normalizeCoreAsSurface second)) := by
              apply canonicalExprCorrect_binaryCall context "and_n" _ _ _ _ _
              · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
                  SurfaceText.isPunctuation]
              · exact hFirst
              · exact hSecond
              · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
                simp [elaborateRawFuel, binaryArguments]
                rw [hFirstRaw, hSecondRaw]
                rfl
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers
                hSugar
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | c inner =>
        have hRecursive := canonicalExprCorrect_appendWrapper wrappers 'c'
          (normalizeCoreAsSurface inner) (.core (.c inner)) hWrappers
          (by simp [CanonicalWrapper])
          (by simp [wrapSurface, desugar_normalizeCoreAsSurface])
          (coreExprCanonicalCorrect context (wrappers ++ "c") inner · hWellFormed)
        cases inner with
        | pk_k key =>
            have hBody := canonicalExprCorrect_pk context key hWellFormed
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
        | pk_h key =>
            have hBody := canonicalExprCorrect_pkh context key hWellFormed
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | or_i first second =>
        have hBody := canonicalExprCorrect_coreBinaryCall context "or_i" .or_i
          first second
          (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation])
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            first canonicalWrappers_empty hWellFormed.1))
          (canonicalExprCorrect_of_emptyChain (coreExprCanonicalCorrect context ""
            second canonicalWrappers_empty hWellFormed.2))
          (by
            intro fuel position firstRaw secondRaw x y hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            rfl)
        have hRightRecursive := canonicalExprCorrect_appendWrapper wrappers 'u'
          (normalizeCoreAsSurface first) (.u (normalizeCoreAsSurface first))
          hWrappers (by simp [CanonicalWrapper]) (by simp [wrapSurface])
          (coreExprCanonicalCorrect context (wrappers ++ "u") first · hWellFormed.1)
        cases first with
        | zero =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_appendWrapper wrappers 'l'
                (normalizeCoreAsSurface second) (.l (normalizeCoreAsSurface second))
                hWrappers (by simp [CanonicalWrapper]) (by simp [wrapSurface])
                (coreExprCanonicalCorrect context (wrappers ++ "l") second ·
                  hWellFormed.2)
        | _ =>
            cases second with
            | zero =>
                simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
                  hRightRecursive
            | _ =>
                simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
                  canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | thresh threshold fragments =>
        have hFragments := coreExprListCanonicalCorrect context fragments hWellFormed.2.1
        have hFragmentsNonempty : fragments ≠ [] := by
          rintro rfl
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        refine canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers
          (canonicalExprCorrect_thresholdCall context "thresh" threshold _ _
            (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation])
            (by simpa using hFragmentsNonempty) hFragments.1 ?_)
        intro fuel callPosition thresholdPosition rest hRest hRestNonempty hEach
        simp [elaborateRawFuel]
        simp only [variadicArguments, hRestNonempty]
        simp only [Bool.false_eq_true, if_false]
        simp
        rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
        rw [hFragments.2 fuel rest hRest hEach]
        have hDesugarMap :
            (fragments.map normalizeCoreAsSurface).map desugar = fragments := by
          have hFunction : (desugar ∘ normalizeCoreAsSurface) = id := by
            funext fragment
            exact desugar_normalizeCoreAsSurface fragment
          rw [List.map_map, hFunction, List.map_id]
        change Except.ok (SurfaceFragment.core (.thresh threshold
          ((fragments.map normalizeCoreAsSurface).map desugar))) = _
        rw [hDesugarMap]
    | multi threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2.2
        have hKeysNonempty : keys ≠ [] := by
          rintro rfl
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        refine canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers
          (canonicalExprCorrect_thresholdCall context "multi" threshold _ _
            (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation])
            (by simpa using hKeysNonempty) hKeys.1 ?_)
        intro fuel callPosition thresholdPosition rest hRest hRestNonempty _
        cases context with
        | tapscript =>
            simp [CoreFragment.WellFormed,
              ScriptContext.permitsLegacyMulti] at hWellFormed
        | p2wsh =>
            simp [elaborateRawFuel]
            simp only [variadicArguments, hRestNonempty]
            simp only [Bool.false_eq_true, if_false]
            simp
            rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
            rw [hKeys.2 rest hRest]
            rfl
    | multi_a threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2.2
        have hKeysNonempty : keys ≠ [] := by
          rintro rfl
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        refine canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers
          (canonicalExprCorrect_thresholdCall context "multi_a" threshold _ _
            (by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation])
            (by simpa using hKeysNonempty) hKeys.1 ?_)
        intro fuel callPosition thresholdPosition rest hRest hRestNonempty _
        cases context with
        | p2wsh =>
            simp [CoreFragment.WellFormed,
              ScriptContext.permitsCheckSigAddMulti] at hWellFormed
        | tapscript =>
            simp [elaborateRawFuel]
            simp only [variadicArguments, hRestNonempty]
            simp only [Bool.false_eq_true, if_false]
            simp
            rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
            rw [hKeys.2 rest hRest]
            rfl

  private theorem coreExprListCanonicalCorrect
      (context : ScriptContext) (fragments : List CoreFragment)
      (hWellFormed : CoreFragment.allWellFormed context fragments) :
      CanonicalExprListCorrect context
        (fragments.map (SurfaceText.coreExprWithWrappers prettyPubKey ""))
        (fragments.map normalizeCoreAsSurface) := by
    cases fragments with
    | nil =>
        constructor
        · simp
        · intro fuel raws hMap hFuel
          have : raws = [] := rawExprMap_eq_nil raws (by simpa using hMap)
          subst raws
          rfl
    | cons fragment fragments =>
        simp only [CoreFragment.allWellFormed] at hWellFormed
        have hHead := coreExprCanonicalCorrect context "" fragment
          canonicalWrappers_empty hWellFormed.1
        have hTail := coreExprListCanonicalCorrect context fragments hWellFormed.2
        constructor
        · intro expr hMem
          simp only [List.map_cons, List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · exact hHead.1
          · exact hTail.1 expr hMem
        · intro fuel raws hMap hFuel
          obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
            rawExprMap_eq_cons raws
              (SurfaceText.coreExprWithWrappers prettyPubKey "" fragment)
              (fragments.map
                (SurfaceText.coreExprWithWrappers prettyPubKey "")) hMap
          simp only [List.mapM_cons, List.map_cons]
          rw [hHead.2 fuel raw hRaw (hFuel _ (by simp))]
          rw [hTail.2 fuel rest hRest (by
            intro expr hMem
            exact hFuel expr (by simp [hMem]))]
          rfl
end

private theorem normalizedSurfaceExprCanonicalCorrect
    (context : ScriptContext) (wrappers : String)
    (fragment : SurfaceFragment)
    (hWrappers : CanonicalWrappers wrappers)
    (hWellFormed : fragment.WellFormed context) :
    CanonicalExprCorrect context
      (SurfaceText.normalizedExprWithWrappers prettyPubKey wrappers
        (normalizeSurface fragment))
      (wrapSurfaceChain wrappers (normalizeSurface fragment)) := by
  induction fragment generalizing wrappers with
  | core core =>
      simpa [normalizeSurface,
        SurfaceText.normalizedExpr_normalizeCoreAsSurface] using
        coreExprCanonicalCorrect context wrappers core hWrappers hWellFormed
  | pk key =>
      have hValid : validResolvedPubKey context key := by
        simpa [SurfaceFragment.WellFormed, desugar,
          SurfaceFragment.desugar, CoreFragment.WellFormed] using hWellFormed
      have hBody := canonicalExprCorrect_pk context key hValid
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | pkh key =>
      have hValid : validResolvedPubKey context key := by
        simpa [SurfaceFragment.WellFormed, desugar,
          SurfaceFragment.desugar, CoreFragment.WellFormed] using hWellFormed
      have hBody := canonicalExprCorrect_pkh context key hValid
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | and_n first second hFirst hSecond =>
      have hFirstWellFormed : first.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      have hSecondWellFormed : second.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.2.1
      have hFirstCorrect := hFirst "" canonicalWrappers_empty hFirstWellFormed
      have hSecondCorrect := hSecond "" canonicalWrappers_empty hSecondWellFormed
      have hBody : CanonicalExprCorrect context
          (.call "and_n"
            [SurfaceText.normalizedExprWithWrappers prettyPubKey ""
                (normalizeSurface first),
              SurfaceText.normalizedExprWithWrappers prettyPubKey ""
                (normalizeSurface second)])
          (.and_n (normalizeSurface first) (normalizeSurface second)) := by
        apply canonicalExprCorrect_binaryCall context "and_n" _ _ _ _ _
        · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation]
        · exact hFirstCorrect
        · exact hSecondCorrect
        · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
          simp [elaborateRawFuel, binaryArguments]
          rw [hFirstRaw, hSecondRaw]
          rfl
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | t inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_appendWrapper wrappers 't'
          (normalizeSurface inner) (.t (normalizeSurface inner)) hWrappers
          (by simp [CanonicalWrapper]) (by simp [wrapSurface])
          (ih (wrappers ++ "t") · hInnerWellFormed)
  | l inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.2
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_appendWrapper wrappers 'l'
          (normalizeSurface inner) (.l (normalizeSurface inner)) hWrappers
          (by simp [CanonicalWrapper]) (by simp [wrapSurface])
          (ih (wrappers ++ "l") · hInnerWellFormed)
  | u inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_appendWrapper wrappers 'u'
          (normalizeSurface inner) (.u (normalizeSurface inner)) hWrappers
          (by simp [CanonicalWrapper]) (by simp [wrapSurface])
          (ih (wrappers ++ "u") · hInnerWellFormed)

theorem parseSurfaceUnchecked_prettySurface
    (context : ScriptContext) (fragment : SurfaceFragment)
    (hWellFormed : fragment.WellFormed context)
    (hDepth : surfaceTextWithinRecursionLimit
      (prettySurface fragment) = true) :
    parseSurfaceUnchecked context resolveHexKey (prettySurface fragment) =
      .ok (normalizeSurface fragment) := by
  let expr := SurfaceText.normalizedExprWithWrappers prettyPubKey ""
    (normalizeSurface fragment)
  have hCorrect : CanonicalExprCorrect context expr
      (normalizeSurface fragment) := by
    simpa [expr, wrapSurfaceChain] using
      normalizedSurfaceExprCanonicalCorrect context "" fragment
        canonicalWrappers_empty hWellFormed
  let tokens := tokenizeSurface expr.render
  have hTokens : tokens.map SurfaceToken.toLexeme = expr.lexemes := by
    exact tokenizeSurface_renderExpr expr hCorrect.1
  have hTokensNonempty : tokens ≠ [] := by
    intro hEmpty
    have hExprEmpty : expr.lexemes = [] := by
      rw [← hTokens]
      simp [hEmpty]
    exact SurfaceText.Expr.lexemes_ne_nil expr hExprEmpty
  obtain ⟨raw, hParse, hRaw⟩ :=
    parseRaw_tokenizeSurface_renderExpr expr hCorrect.1
  have hLengths : tokens.length = expr.lexemes.length := by
    have := congrArg List.length hTokens
    simpa using this
  have hElaborate :
      elaborateRawFuel context resolveHexKey (tokens.length + 1) raw =
        .ok (normalizeSurface fragment) := by
    apply hCorrect.2
    · exact hRaw
    · omega
  unfold parseSurfaceUnchecked
  change (do
    if tokens.isEmpty then
      Except.error SurfaceParseError.emptyInput
    else if !tokensWithinSurfaceRecursionLimit tokens then
      Except.error (.maxRecursionDepthExceeded maxSurfaceRecursionDepth)
    else
      let (raw, remaining) ← parseRaw tokens
      match remaining with
      | token :: _ =>
          Except.error (.trailingInput token.position (tokenText token))
      | [] => elaborateRawFuel context resolveHexKey (tokens.length + 1) raw) = _
  have hTokensIsEmpty : tokens.isEmpty = false := by
    cases hTokensValue : tokens with
    | nil => exact False.elim (hTokensNonempty hTokensValue)
    | cons => rfl
  rw [if_neg (by simpa using hTokensIsEmpty)]
  have hWithin : tokensWithinSurfaceRecursionLimit tokens = true := by
    simpa [surfaceTextWithinRecursionLimit, tokens, expr, prettySurface,
      prettySurfaceWith, SurfaceText.prettyNormalizedSurfaceWithWrappers]
      using hDepth
  rw [hWithin]
  rw [hParse]
  exact hElaborate

end SurfaceParser

end LeanMiniscript.Miniscript
