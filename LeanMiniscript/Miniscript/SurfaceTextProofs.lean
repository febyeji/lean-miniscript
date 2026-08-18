import LeanMiniscript.Miniscript.SurfacePretty
import LeanMiniscript.Miniscript.SurfaceParser

namespace LeanMiniscript.Miniscript

/-!
# Surface text normalization proofs

These lemmas record the proof-facing contract behind canonical surface text:
normalization preserves the core fragment, is a fixed point, and therefore does
not change canonical pretty-printed text when applied repeatedly.
-/

/-- Surface normalization preserves context-aware well-formedness in both
    directions. This is the validation bridge needed by the parser/printer
    round-trip theorem: canonical spelling changes syntax, not the checked
    core fragment. -/
theorem wellFormed_normalizeSurface_iff (context : ScriptContext)
    (fragment : SurfaceFragment) :
    (normalizeSurface fragment).WellFormed context ↔ fragment.WellFormed context := by
  unfold SurfaceFragment.WellFormed
  rw [show (normalizeSurface fragment).desugar = fragment.desugar by
    simpa [desugar] using desugar_normalizeSurface fragment]

/-- Normalizing before canonical pretty-printing does not change the text. -/
theorem prettySurface_normalizeSurface (fragment : SurfaceFragment) :
    prettySurface (normalizeSurface fragment) = prettySurface fragment := by
  simp [prettySurface, prettySurfaceWith, normalizeSurface_idempotent]

/-- The end-to-end canonical hexadecimal surface codec contract. -/
def SurfaceTextRoundTrip : Prop :=
  ∀ (context : ScriptContext) (fragment : SurfaceFragment),
    fragment.WellFormed context →
      parseSurfaceHex context (prettySurface fragment) =
        .ok (normalizeSurface fragment)

/-- Canonical hexadecimal surface printing and context-aware parsing satisfy
    `SurfaceTextRoundTrip`. -/
theorem surfaceTextRoundTrip : SurfaceTextRoundTrip := by
  intro context fragment hWellFormed
  exact parseSurfaceHex_prettySurface context fragment hWellFormed

end LeanMiniscript.Miniscript
