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
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hBody : CanonicalExprCorrect context
            (.call "and_b"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.and_b first second)) := by
          apply canonicalExprCorrect_binaryCall context "and_b" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.and_b (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_b first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_b"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_b first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_b" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_b (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_c first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_c"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_c first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_c" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_c (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_d first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_d"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_d first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_d" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_d (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | a inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "a") inner
          (canonicalWrappers_append_char wrappers 'a' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "a")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.a inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | s inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "s") inner
          (canonicalWrappers_append_char wrappers 's' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "s")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.s inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | d inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "d") inner
          (canonicalWrappers_append_char wrappers 'd' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "d")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.d inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | v inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "v") inner
          (canonicalWrappers_append_char wrappers 'v' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "v")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.v inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | j inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "j") inner
          (canonicalWrappers_append_char wrappers 'j' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "j")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.j inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | n inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "n") inner
          (canonicalWrappers_append_char wrappers 'n' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "n")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.n inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | and_v first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hBody : CanonicalExprCorrect context
            (.call "and_v"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.and_v first second)) := by
          apply canonicalExprCorrect_binaryCall context "and_v" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.and_v (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        cases second with
        | one =>
            have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "t") first
              (canonicalWrappers_append_char wrappers 't' hWrappers
                (by simp [CanonicalWrapper])) hWellFormed.1
            have hTarget : wrapSurfaceChain (wrappers ++ "t")
                (normalizeCoreAsSurface first) =
                wrapSurfaceChain wrappers (.t (normalizeCoreAsSurface first)) := by
              rw [wrapSurfaceChain_append]
              simp [wrapSurfaceChain, wrapSurface]
            rw [hTarget] at hRecursive
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | andor first second third =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hThird : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" third)
            (normalizeCoreAsSurface third) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" third
            canonicalWrappers_empty hWellFormed.2.2.1
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
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "c") inner
          (canonicalWrappers_append_char wrappers 'c' hWrappers
            (by simp [CanonicalWrapper])) hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "c")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.c inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
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
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_i"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_i first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_i" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_i (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        have hRightRecursive := coreExprCanonicalCorrect context (wrappers ++ "u") first
          (canonicalWrappers_append_char wrappers 'u' hWrappers
            (by simp [CanonicalWrapper])) hWellFormed.1
        have hRightTarget : wrapSurfaceChain (wrappers ++ "u")
            (normalizeCoreAsSurface first) =
            wrapSurfaceChain wrappers (.u (normalizeCoreAsSurface first)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface]
        rw [hRightTarget] at hRightRecursive
        cases first with
        | zero =>
            have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "l") second
              (canonicalWrappers_append_char wrappers 'l' hWrappers
                (by simp [CanonicalWrapper])) hWellFormed.2
            have hTarget : wrapSurfaceChain (wrappers ++ "l")
                (normalizeCoreAsSurface second) =
                wrapSurfaceChain wrappers (.l (normalizeCoreAsSurface second)) := by
              rw [wrapSurfaceChain_append]
              simp [wrapSurfaceChain, wrapSurface]
            rw [hTarget] at hRecursive
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
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
          intro hEmpty
          subst fragments
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedFragmentsNonempty :
            fragments.map
                (SurfaceText.coreExprWithWrappers prettyPubKey "") ≠ [] := by
          simpa using hFragmentsNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")) =
              .atom (toString threshold) ::
                fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "") :=
          SurfaceText.variadicArguments_of_ne_nil _ _
            hRenderedFragmentsNonempty
        have hBody : CanonicalExprCorrect context
            (.call "thresh"
              (.atom (toString threshold) ::
                fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")))
            (.core (.thresh threshold fragments)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hFragments.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hFragmentsNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
                    have hEach : ∀ expr ∈ fragments.map
                        (SurfaceText.coreExprWithWrappers prettyPubKey ""),
                        expr.lexemes.length < fuel := by
                      intro expr hMem
                      have hLess := lexemes_length_lt_call_of_mem "thresh"
                        (.atom (toString threshold) :: fragments.map
                          (SurfaceText.coreExprWithWrappers prettyPubKey ""))
                        expr (by simp [hMem])
                      omega
                    simp [elaborateRawFuel]
                    simp only [variadicArguments, hRestNonempty]
                    simp only [Bool.false_eq_true, if_false]
                    simp
                    rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
                    rw [hFragments.2 fuel rest hRest hEach]
                    have hDesugarMap :
                        (fragments.map normalizeCoreAsSurface).map desugar =
                          fragments := by
                      have hFunction :
                          (desugar ∘ normalizeCoreAsSurface) = id := by
                        funext fragment
                        exact desugar_normalizeCoreAsSurface fragment
                      rw [List.map_map, hFunction, List.map_id]
                    change Except.ok (SurfaceFragment.core (.thresh threshold
                      ((fragments.map normalizeCoreAsSurface).map desugar))) = _
                    rw [hDesugarMap]
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody
    | multi threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2.2
        have hKeysNonempty : keys ≠ [] := by
          intro hEmpty
          subst keys
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedKeysNonempty :
            keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) ≠ [] := by
          simpa using hKeysNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) =
              .atom (toString threshold) ::
                keys.map (fun key => .atom (prettyPubKey key)) :=
          SurfaceText.variadicArguments_of_ne_nil _ _ hRenderedKeysNonempty
        have hBody : CanonicalExprCorrect context
            (.call "multi" (.atom (toString threshold) ::
              keys.map (fun key => .atom (prettyPubKey key))))
            (.core (.multi threshold keys)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hKeys.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hKeysNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
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
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody
    | multi_a threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2.2
        have hKeysNonempty : keys ≠ [] := by
          intro hEmpty
          subst keys
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedKeysNonempty :
            keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) ≠ [] := by
          simpa using hKeysNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) =
              .atom (toString threshold) ::
                keys.map (fun key => .atom (prettyPubKey key)) :=
          SurfaceText.variadicArguments_of_ne_nil _ _ hRenderedKeysNonempty
        have hBody : CanonicalExprCorrect context
            (.call "multi_a" (.atom (toString threshold) ::
              keys.map (fun key => .atom (prettyPubKey key))))
            (.core (.multi_a threshold keys)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hKeys.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hKeysNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
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
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody

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
      have hRecursive := ih (wrappers ++ "t")
        (canonicalWrappers_append_char wrappers 't' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "t")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.t (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive
  | l inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.2
      have hRecursive := ih (wrappers ++ "l")
        (canonicalWrappers_append_char wrappers 'l' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "l")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.l (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive
  | u inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      have hRecursive := ih (wrappers ++ "u")
        (canonicalWrappers_append_char wrappers 'u' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "u")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.u (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive

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
