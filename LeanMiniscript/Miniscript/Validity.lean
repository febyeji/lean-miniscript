import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Validation

namespace LeanMiniscript.Miniscript

/-- The context, structural, and correctness-typing evidence needed before a
    semantic claim is made about a core fragment. -/
structure ValidTypedFragment (ctx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop where
  wellFormed : m.WellFormed ctx
  hasType : HasType ctx m ty

/-- A top-level Miniscript is a context-valid core fragment with B base type. -/
def ValidMiniscript (ctx : ScriptContext) (m : CoreFragment) : Prop :=
  ∃ mods, ValidTypedFragment ctx m ⟨.B, mods⟩

/-- A top-level Miniscript carrying the correctness type system's `d`
    guarantee. -/
def ValidDissatisfiableMiniscript (ctx : ScriptContext)
    (m : CoreFragment) : Prop :=
  ∃ mods, ValidTypedFragment ctx m ⟨.B, mods⟩ ∧ mods.d = true

/-- Surface validity is stated through the single core desugaring boundary. -/
def ValidTypedSurfaceFragment (ctx : ScriptContext) (m : SurfaceFragment)
    (ty : MiniType) : Prop :=
  ValidTypedFragment ctx (desugar m) ty

/-- A top-level surface Miniscript is valid exactly when its desugared core is. -/
def ValidSurfaceMiniscript (ctx : ScriptContext)
    (m : SurfaceFragment) : Prop :=
  ValidMiniscript ctx (desugar m)

/-- Surface dissatisfaction validity is inherited from desugared core. -/
def ValidDissatisfiableSurfaceMiniscript (ctx : ScriptContext)
    (m : SurfaceFragment) : Prop :=
  ValidDissatisfiableMiniscript ctx (desugar m)

end LeanMiniscript.Miniscript
