import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-- Bitcoin consensus limits. -/
def MAX_STACK_SIZE : Nat := 1000
def MAX_SCRIPT_SIZE : Nat := 10000
def MAX_OPS_PER_SCRIPT : Nat := 201
def MAX_SCRIPT_ELEMENT_SIZE : Nat := 520

-- TODO(ast): define stack depth computation for core fragments.
-- def maxStackDepth : CoreFragment → Nat

-- TODO(ast): define script size computation for compiled core fragments.
-- def scriptSize : CoreFragment → Nat

-- TODO(ast): define sigop count computation for core fragments.
-- def sigopCount : CoreFragment → Nat

/-!
TODO(theorem): resource-bound soundness.

Core proof tasks:
- Define `scriptSize`, `maxStackDepth`, and `sigopCount` over `CoreFragment`.
- Prove the resource-bound theorem for well-typed core fragments compiled with
  `compile`.
- State the surface corollary by applying the core theorem to `desugar s`, so
  surface syntax does not need a duplicate resource proof.
-/

end LeanMiniscript.Properties
