import LeanHash160
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Executable compilation

The core compiler remains parameterized over a key-HASH160 resolver so its
formal results do not depend on a particular cryptographic implementation.
This module instantiates that boundary with the pure Lean implementation from
the pinned `lean-hash160` package.
-/

/-- Bitcoin's concrete HASH160 implementation at the typed key/hash boundary. -/
def concreteKeyHash (key : PubKey) : Hash160 :=
  Hash160.ofBytes (LeanHash160.hash160 key.bytes)

/-- Compile a core fragment with Bitcoin's concrete HASH160 operation. -/
def compileConcrete (fragment : CoreFragment) : Script :=
  compileWithKeyHash concreteKeyHash fragment

/-- Compile a surface fragment with Bitcoin's concrete HASH160 operation. -/
def compileSurfaceConcrete (fragment : SurfaceFragment) : Script :=
  compileSurfaceWithKeyHash concreteKeyHash fragment

end LeanMiniscript.Miniscript
