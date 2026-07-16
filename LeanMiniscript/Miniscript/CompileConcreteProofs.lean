import LeanMiniscript.Miniscript.CompileConcrete
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

end LeanMiniscript.Miniscript
