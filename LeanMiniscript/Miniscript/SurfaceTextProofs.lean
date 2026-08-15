import LeanMiniscript.Miniscript.SurfacePretty
import LeanMiniscript.Miniscript.SurfaceParser

namespace LeanMiniscript.Miniscript

/-!
# Surface text normalization proofs

These lemmas record the proof-facing contract behind canonical surface text:
normalization preserves the core fragment, is a fixed point, and therefore does
not change canonical pretty-printed text when applied repeatedly.
-/

/-- Recognizing surface sugar does not change the desugared core fragment. -/
theorem desugar_normalizeCoreAsSurface (fragment : CoreFragment) :
    desugar (normalizeCoreAsSurface fragment) = fragment := by
  cases fragment with
  | c x => cases x <;> rfl
  | andor x y z =>
      have hx := desugar_normalizeCoreAsSurface x
      have hy := desugar_normalizeCoreAsSurface y
      cases z <;>
        simp_all [normalizeCoreAsSurface, desugar, SurfaceFragment.desugar]
  | and_v x y =>
      have hx := desugar_normalizeCoreAsSurface x
      cases y <;>
        simp_all [normalizeCoreAsSurface, desugar, SurfaceFragment.desugar]
  | or_i x y =>
      have hx := desugar_normalizeCoreAsSurface x
      have hy := desugar_normalizeCoreAsSurface y
      cases x <;> cases y <;>
        simp_all [normalizeCoreAsSurface, desugar, SurfaceFragment.desugar]
  | _ => rfl
termination_by structural fragment

/-- Recursive surface normalization preserves desugaring. -/
theorem desugar_normalizeSurface (fragment : SurfaceFragment) :
    desugar (normalizeSurface fragment) = desugar fragment := by
  induction fragment with
  | core core => exact desugar_normalizeCoreAsSurface core
  | pk _ | pkh _ => rfl
  | and_n x y hx hy =>
      change CoreFragment.andor
        (normalizeSurface x).desugar (normalizeSurface y).desugar .zero =
          .andor x.desugar y.desugar .zero
      rw [show (normalizeSurface x).desugar = x.desugar by
        simpa [desugar] using hx]
      rw [show (normalizeSurface y).desugar = y.desugar by
        simpa [desugar] using hy]
  | t x hx | l x hx | u x hx =>
      simp only [normalizeSurface, desugar, SurfaceFragment.desugar]
      rw [show (normalizeSurface x).desugar = x.desugar by
        simpa [desugar] using hx]

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

/-- Core-shape recognition already produces a normalized surface fragment. -/
theorem normalizeSurface_normalizeCoreAsSurface (fragment : CoreFragment) :
    normalizeSurface (normalizeCoreAsSurface fragment) =
      normalizeCoreAsSurface fragment := by
  cases fragment with
  | c x => cases x <;> rfl
  | andor x y z =>
      have hx := normalizeSurface_normalizeCoreAsSurface x
      have hy := normalizeSurface_normalizeCoreAsSurface y
      cases z <;>
        simp_all [normalizeCoreAsSurface, normalizeSurface]
  | and_v x y =>
      have hx := normalizeSurface_normalizeCoreAsSurface x
      cases y <;>
        simp_all [normalizeCoreAsSurface, normalizeSurface]
  | or_i x y =>
      have hx := normalizeSurface_normalizeCoreAsSurface x
      have hy := normalizeSurface_normalizeCoreAsSurface y
      cases x <;> cases y <;>
        simp_all [normalizeCoreAsSurface, normalizeSurface]
  | _ => rfl
termination_by structural fragment

/-- Surface normalization is idempotent. -/
theorem normalizeSurface_idempotent (fragment : SurfaceFragment) :
    normalizeSurface (normalizeSurface fragment) = normalizeSurface fragment := by
  induction fragment <;>
    simp_all [normalizeSurface, normalizeSurface_normalizeCoreAsSurface]

/-- Normalizing before canonical pretty-printing does not change the text. -/
theorem prettySurface_normalizeSurface (fragment : SurfaceFragment) :
    prettySurface (normalizeSurface fragment) = prettySurface fragment := by
  simp [prettySurface, prettySurfaceWith, normalizeSurface_idempotent]

/-- The precise remaining end-to-end codec obligation. Raw surface ASTs are
    intentionally permitted to be invalid, so parsing their printed form can
    only be required after context-aware validation. -/
def SurfaceTextRoundTrip : Prop :=
  ∀ (context : ScriptContext) (fragment : SurfaceFragment),
    fragment.WellFormed context →
      parseSurfaceHex context (prettySurface fragment) =
        .ok (normalizeSurface fragment)

end LeanMiniscript.Miniscript
