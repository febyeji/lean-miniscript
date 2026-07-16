import LeanHash160
import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Executable compilation

The core compiler remains parameterized over a key-HASH160 resolver so its
formal results do not depend on a particular cryptographic implementation.
This module instantiates that boundary with the pure Lean implementation from
the pinned `lean-hash160` package.
-/

/-- Compile a core fragment with Bitcoin's concrete HASH160 operation. -/
def compileConcrete (fragment : CoreFragment) : Script :=
  compileWithKeyHash LeanHash160.hash160 fragment

/-- Compile a surface fragment with Bitcoin's concrete HASH160 operation. -/
def compileSurfaceConcrete (fragment : SurfaceFragment) : Script :=
  compileSurfaceWithKeyHash LeanHash160.hash160 fragment

/-- Concrete core compilation is an instance of the relational BIP 379 result. -/
theorem compileConcrete_conforms (fragment : CoreFragment) :
    Bip379Compilation LeanHash160.hash160 fragment (compileConcrete fragment) :=
  compileWithKeyHash_conforms LeanHash160.hash160 fragment

/-- Concrete surface compilation conforms after desugaring. -/
theorem compileSurfaceConcrete_conforms (fragment : SurfaceFragment) :
    Bip379Compilation LeanHash160.hash160 (desugar fragment)
      (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_conforms LeanHash160.hash160 fragment

/-- Concrete core compilation has balanced conditional control flow. -/
theorem compileConcrete_balancedControlFlow (fragment : CoreFragment) :
    BalancedControlFlow (compileConcrete fragment) :=
  compileWithKeyHash_balancedControlFlow LeanHash160.hash160 fragment

/-- Concrete surface compilation has balanced conditional control flow. -/
theorem compileSurfaceConcrete_balancedControlFlow (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_balancedControlFlow LeanHash160.hash160 fragment

/-- Concrete compiler output remains inside the model's opcode universe. -/
theorem compileConcrete_usesOnlyModeledOpcodes (fragment : CoreFragment) :
    UsesOnlyModeledOpcodes (compileConcrete fragment) :=
  usesOnlyModeledOpcodes _

end LeanMiniscript.Miniscript
