import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript

-- TODO(theorem): define what "canonical" witness means.
-- A canonical witness satisfies additional constraints:
-- - Signatures use low-S form
-- - CHECKMULTISIG dummy is exactly OP_0
-- - IF/NOTIF arguments are exactly OP_0 or OP_1 (MINIMALIF)

-- TODO(theorem): define non-malleability over core fragments.
-- def nonMalleable : CoreFragment → Prop

/-!
TODO(theorem): non-malleability.

Core proof tasks:
- Define canonical witnesses and `nonMalleable` over `CoreFragment`.
- Prove that any two canonical satisfying witnesses for the same non-malleable
  core fragment are equal.
- State the surface corollary by applying the core theorem to `desugar s`.
-/

end LeanMiniscript.Properties
