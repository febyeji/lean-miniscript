import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Miniscript.Checked

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Checked concrete compilation

Checked adapters are separate so callers of the raw concrete compiler do not
import validation and type-inference modules.
-/

/-- Compile a checked core fragment with Bitcoin's concrete HASH160. -/
def compileConcreteChecked {ctx : ScriptContext}
    (checked : CheckedFragment ctx) : Script :=
  compileCheckedWithKeyHash concreteKeyHash checked

/-- Compile a checked surface fragment with Bitcoin's concrete HASH160. -/
def compileSurfaceConcreteChecked {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) : Script :=
  compileCheckedSurfaceWithKeyHash concreteKeyHash checked

end LeanMiniscript.Miniscript
