/-
  LeanMiniscript.Script.SmallStep
  ============================
  Small-step operational semantics for Bitcoin Script.

  The intended model gives each opcode a single state transition:
    (stack, altstack, script, flags) →₁ (stack', altstack', script', flags')

  The planned granularity follows Bitcoin Core's EvalScript loop structure:
    while (pc < script.end()) { opcode = *pc++; switch(opcode) { ... } }

  References:
  - Bitcoin Core: src/script/interpreter.cpp, EvalScript()
  - KEVM (CSF 2018) uses a similar small-step approach for EVM
-/

import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-- Small-step transition relation.
    `Step s s'` means state `s` transitions to state `s'` in one step.

    The relation is intentionally empty until real opcode rules are defined;
    an unfinished model must not manufacture semantic self-transitions. -/
inductive Step : ExecState → ExecState → Prop

/- TODO: Define transition rules for each opcode
  --
  -- Example structure (to be filled in):
  --
  -- | step_OP_DUP : ∀ s x rest,
  --     s.stack = x :: rest →
  --     s.script = .op .OP_DUP :: remaining →
  --     Step s { s with stack := x :: x :: rest, script := remaining, pc := s.pc + 1 }
  --
  -- | step_OP_IF_true : ∀ s x rest,
  --     s.stack = x :: rest →
  --     CastToBool x = true →
  --     s.script = .op .OP_IF :: remaining →
  --     Step s { s with stack := rest, condStack := true :: s.condStack, ... }
  --
  -- Categories to implement:
  -- 1. Stack manipulation: DUP, SWAP, IFDUP, TOALTSTACK, FROMALTSTACK
  -- 2. Flow control: IF, NOTIF, ELSE, ENDIF
  -- 3. Arithmetic: ADD, BOOLAND, BOOLOR, 0NOTEQUAL
  -- 4. Comparison: EQUAL, EQUALVERIFY, NUMEQUAL
  -- 5. Crypto: SHA256, HASH256, RIPEMD160, HASH160
  -- 6. Signature: CHECKSIG, CHECKSIGADD, CHECKMULTISIG
  -- 7. Timelock: CHECKSEQUENCEVERIFY, CHECKLOCKTIMEVERIFY
  -- 8. Other: SIZE
-/

/-- No one-step execution claim is available from the unfinished relation. -/
theorem noStep (state next : ExecState) : ¬ Step state next := by
  intro transition
  cases transition

/-- Reflexive transitive closure of Step (multi-step execution). -/
inductive Steps : ExecState → ExecState → Prop where
  | refl : (s : ExecState) → Steps s s
  | step : (s s' s'' : ExecState) → Step s s' → Steps s' s'' → Steps s s''

-- TODO: Prove determinism of Step (each state has at most one successor)
-- TODO: Prove termination (Script is not Turing-complete)

end LeanMiniscript.Script
