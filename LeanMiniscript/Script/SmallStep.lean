/-
  LeanMiniscript.Script.SmallStep
  ============================
  Small-step operational semantics for Bitcoin Script.

  Each opcode is modeled as a single state transition:
    (stack, altstack, script, flags) →₁ (stack', altstack', script', flags')

  This matches Bitcoin Core's EvalScript loop structure:
    while (pc < script.end()) { opcode = *pc++; switch(opcode) { ... } }

  References:
  - Bitcoin Core: src/script/interpreter.cpp, EvalScript()
  - KEVM (CSF 2018) uses a similar small-step approach for EVM
  - See also: docs/decisions/02-semantics-style.md
-/

import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-- Small-step transition relation.
    `step s s'` means state `s` transitions to state `s'` in one step. -/
inductive Step : ExecState → ExecState → Prop where
  -- TODO: Define transition rules for each opcode
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
  | placeholder : (state : ExecState) → Step state state  -- Remove once real rules are defined

/-- Reflexive transitive closure of Step (multi-step execution). -/
inductive Steps : ExecState → ExecState → Prop where
  | refl : (s : ExecState) → Steps s s
  | step : (s s' s'' : ExecState) → Step s s' → Steps s' s'' → Steps s s''

-- TODO: Prove determinism of Step (each state has at most one successor)
-- TODO: Prove termination (Script is not Turing-complete)

end LeanMiniscript.Script
