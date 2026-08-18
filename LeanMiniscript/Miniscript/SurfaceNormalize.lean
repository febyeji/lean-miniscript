import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

/-!
# Canonical surface normalization

`SurfaceFragment` deliberately keeps a thin sugar layer over `CoreFragment`.
The same Miniscript can therefore be represented either by a surface sugar or
by its desugared core shape. These functions select the surface spelling as the
canonical representation whenever the core shape matches exactly.
-/

/-- Recognize core shapes that have a canonical surface spelling. Core shapes
    without a surface spelling remain embedded with `SurfaceFragment.core`. -/
def normalizeCoreAsSurface : CoreFragment → SurfaceFragment
  | .c (.pk_k key) => .pk key
  | .c (.pk_h key) => .pkh key
  | .andor x y .zero =>
      .and_n (normalizeCoreAsSurface x) (normalizeCoreAsSurface y)
  | .and_v x .one =>
      .t (normalizeCoreAsSurface x)
  | .or_i .zero x =>
      .l (normalizeCoreAsSurface x)
  | .or_i x .zero =>
      .u (normalizeCoreAsSurface x)
  | fragment => .core fragment

/-- Normalize a surface fragment recursively, preferring the documented surface
    sugar whenever an embedded core fragment has the corresponding shape. -/
def normalizeSurface : SurfaceFragment → SurfaceFragment
  | .core fragment => normalizeCoreAsSurface fragment
  | .pk key => .pk key
  | .pkh key => .pkh key
  | .and_n x y => .and_n (normalizeSurface x) (normalizeSurface y)
  | .t x => .t (normalizeSurface x)
  | .l x => .l (normalizeSurface x)
  | .u x => .u (normalizeSurface x)

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

end LeanMiniscript.Miniscript
