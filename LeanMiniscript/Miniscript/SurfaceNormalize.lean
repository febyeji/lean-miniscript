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

end LeanMiniscript.Miniscript
