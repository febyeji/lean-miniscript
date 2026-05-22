import LeanMiniscript.Script.SmallStep
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
TODO(theorem): state small-step/big-step equivalence once the execution
boundary API is stable.

Core proof tasks:
- Define the canonical small-step initial state, final-state predicate, and
  result extraction function used by both semantics.
- Prove Small -> Big: every terminating `Steps` derivation produces the same
  `Eval` result.
- Prove Big -> Small: every `Eval` derivation has a corresponding `Steps`
  execution with the same extracted result.
- Prove the opcode-local simulation lemmas first, then lift them through
  sequencing/control-flow opcodes.

Miniscript-facing use:
- Apply the equivalence to scripts produced by `compile : CoreFragment -> Script`.
- For surface syntax, use `compileSurface s = compile (desugar s)` instead of
  duplicating the equivalence theorem.
-/

end LeanMiniscript.Script
