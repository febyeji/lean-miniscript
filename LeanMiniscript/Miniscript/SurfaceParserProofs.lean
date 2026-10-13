import LeanMiniscript.Miniscript.SurfaceParser
import LeanMiniscript.Miniscript.SurfaceParserProofs.RawParser
import LeanMiniscript.Miniscript.SurfaceParserProofs.Atoms
import LeanMiniscript.Miniscript.SurfaceParserProofs.CanonicalExpr
import LeanMiniscript.Miniscript.SurfaceParserProofs.RoundTrip

namespace LeanMiniscript.Miniscript

/-! Tokenization, elaboration and canonical surface-text round-trip proofs.

The supporting development lives in the `SurfaceParserProofs/` submodules. -/

open SurfaceParser

/-- A successful public parse returns the normalization of an unchecked parse
    that passed validation: it is context-valid and well-typed. -/
private theorem exists_unchecked_of_parseSurface_eq_ok
    (context : ScriptContext) (resolver : KeyResolver) (input : String)
    (fragment : SurfaceFragment)
    (h : parseSurface context resolver input = .ok fragment) :
    ∃ unchecked, fragment = normalizeSurface unchecked ∧
      fragment.WellFormed context ∧
        ∃ ty, HasType context (desugar fragment) ty := by
  unfold parseSurface at h
  cases hUnchecked : parseSurfaceUnchecked context resolver input with
  | error error =>
      rw [hUnchecked] at h
      contradiction
  | ok unchecked =>
      rw [hUnchecked] at h
      change validateSurface context (normalizeSurface unchecked) = .ok fragment at h
      by_cases hValid : (normalizeSurface unchecked).WellFormed context
      · cases hTyped : inferTyped context
          (desugar (normalizeSurface unchecked)) with
        | none => simp [validateSurface, hValid, hTyped] at h
        | some typed =>
            simp [validateSurface, hValid, hTyped] at h
            change Except.ok (normalizeSurface unchecked) = Except.ok fragment at h
            injection h with hFragment
            subst hFragment
            exact ⟨unchecked, rfl, hValid, ⟨typed.val, typed.property⟩⟩
      · simp [validateSurface, hValid] at h

/-- Every successfully parsed surface fragment is already in canonical form. -/
theorem normalizeSurface_of_parseSurface_eq_ok
    (context : ScriptContext) (resolver : KeyResolver) (input : String)
    (fragment : SurfaceFragment)
    (h : parseSurface context resolver input = .ok fragment) :
    normalizeSurface fragment = fragment := by
  obtain ⟨unchecked, rfl, -⟩ :=
    exists_unchecked_of_parseSurface_eq_ok context resolver input fragment h
  exact normalizeSurface_idempotent unchecked

/-- Successful public parsing returns a context-valid and well-typed surface
    fragment. -/
theorem wellFormed_and_hasType_of_parseSurface_eq_ok
    (context : ScriptContext) (resolver : KeyResolver) (input : String)
    (fragment : SurfaceFragment)
    (h : parseSurface context resolver input = .ok fragment) :
    fragment.WellFormed context ∧
      ∃ ty, HasType context (desugar fragment) ty :=
  (exists_unchecked_of_parseSurface_eq_ok context resolver input fragment h).choose_spec.2

/-- `parseSurfaceHex` is a left inverse of `prettySurface` for every
    context-valid, inferred surface fragment, modulo the documented surface
    normalization. -/
theorem parseSurfaceHex_prettySurface
    (context : ScriptContext) (fragment : SurfaceFragment)
    (hWellFormed : fragment.WellFormed context)
    (hDepth : surfaceTextWithinRecursionLimit
      (prettySurface fragment) = true)
    (hInferred : (inferTyped context (desugar fragment)).isSome = true) :
    parseSurfaceHex context (prettySurface fragment) =
      .ok (normalizeSurface fragment) := by
  have hNormalizedWellFormed :
      (normalizeSurface fragment).WellFormed context := by
    unfold SurfaceFragment.WellFormed
    change (desugar (normalizeSurface fragment)).WellFormed context
    rw [desugar_normalizeSurface]
    exact hWellFormed
  have hNormalizedInferred :
      (inferTyped context (desugar (normalizeSurface fragment))).isSome = true := by
    rw [desugar_normalizeSurface]
    exact hInferred
  unfold parseSurfaceHex parseSurface
  rw [parseSurfaceUnchecked_prettySurface context fragment hWellFormed hDepth]
  change validateSurface context (normalizeSurface (normalizeSurface fragment)) =
    .ok (normalizeSurface fragment)
  rw [normalizeSurface_idempotent]
  cases hTyped : inferTyped context (desugar (normalizeSurface fragment)) with
  | none => simp [hTyped] at hNormalizedInferred
  | some typed =>
      simp [validateSurface, hNormalizedWellFormed, hTyped]
      rfl

end LeanMiniscript.Miniscript
