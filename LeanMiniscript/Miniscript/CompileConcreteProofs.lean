import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Miniscript.CompileConcreteChecked
import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Executable compilation guarantees

Proofs are kept separate from `CompileConcrete` so consumers that only need the
executable compiler do not import the relational and structural proof graph.
-/

/-- Concrete core compilation is an instance of the relational BIP 379 result. -/
theorem compileConcrete_conforms (fragment : CoreFragment) :
    Bip379Compilation concreteKeyHash fragment (compileConcrete fragment) :=
  compileWithKeyHash_conforms concreteKeyHash fragment

/-- Concrete surface compilation conforms after desugaring. -/
theorem compileSurfaceConcrete_conforms (fragment : SurfaceFragment) :
    Bip379Compilation concreteKeyHash (desugar fragment)
      (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_conforms concreteKeyHash fragment

/-- Concrete core compilation has balanced conditional control flow. -/
theorem compileConcrete_balancedControlFlow (fragment : CoreFragment) :
    BalancedControlFlow (compileConcrete fragment) :=
  compileWithKeyHash_balancedControlFlow concreteKeyHash fragment

/-- Concrete surface compilation has balanced conditional control flow. -/
theorem compileSurfaceConcrete_balancedControlFlow (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_balancedControlFlow concreteKeyHash fragment

/-- Concrete core compilation emits only opcodes allowed by the validated
Script context. -/
theorem compileConcrete_scriptAllowed
    {ctx : ScriptContext} {fragment : CoreFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileConcrete fragment) :=
  compileWithKeyHash_scriptAllowed concreteKeyHash wellFormed

/-- Concrete surface compilation emits only opcodes allowed by the validated
Script context. -/
theorem compileSurfaceConcrete_scriptAllowed
    {ctx : ScriptContext} {fragment : SurfaceFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_scriptAllowed concreteKeyHash wellFormed

/-- Concrete checked-core compilation carries context safety from the checked
boundary. -/
theorem compileConcreteChecked_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedFragment ctx) :
    ScriptAllowed ctx (compileConcreteChecked checked) :=
  compileCheckedWithKeyHash_scriptAllowed concreteKeyHash checked

/-- Concrete checked-surface compilation carries context safety from the
checked boundary. -/
theorem compileSurfaceConcreteChecked_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) :
    ScriptAllowed ctx (compileSurfaceConcreteChecked checked) :=
  compileCheckedSurfaceWithKeyHash_scriptAllowed concreteKeyHash checked

end LeanMiniscript.Miniscript
