import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Script.BigStepProofs

namespace LeanMiniscript.Script

open LeanMiniscript.Miniscript

/-!
# Explicit Script underflow fixtures

These fixtures pin the fixed main-stack arity table and exercise terminal
underflow results both for raw opcodes and for compiler-generated Script.
-/

structure OpcodeArityFixture where
  opcode : Opcode
  expected : Option Nat

/-- Exact fixed main-stack arity for every modeled opcode. The two
    `CHECKMULTISIG` variants remain separate because their input count is
    encoded in the stack. -/
def opcodeArityFixtures : List OpcodeArityFixture := [
  ⟨.OP_NOP, some 0⟩,
  ⟨.OP_NOP1, some 0⟩,
  ⟨.OP_NOP4, some 0⟩,
  ⟨.OP_NOP5, some 0⟩,
  ⟨.OP_NOP6, some 0⟩,
  ⟨.OP_NOP7, some 0⟩,
  ⟨.OP_NOP8, some 0⟩,
  ⟨.OP_NOP9, some 0⟩,
  ⟨.OP_NOP10, some 0⟩,
  ⟨.OP_RETURN, some 0⟩,
  ⟨.OP_IF, some 1⟩,
  ⟨.OP_NOTIF, some 1⟩,
  ⟨.OP_ELSE, some 0⟩,
  ⟨.OP_ENDIF, some 0⟩,
  ⟨.OP_2DROP, some 2⟩,
  ⟨.OP_2DUP, some 2⟩,
  ⟨.OP_3DUP, some 3⟩,
  ⟨.OP_2OVER, some 4⟩,
  ⟨.OP_2ROT, some 6⟩,
  ⟨.OP_2SWAP, some 4⟩,
  ⟨.OP_IFDUP, some 1⟩,
  ⟨.OP_DEPTH, some 0⟩,
  ⟨.OP_DROP, some 1⟩,
  ⟨.OP_DUP, some 1⟩,
  ⟨.OP_NIP, some 2⟩,
  ⟨.OP_OVER, some 2⟩,
  ⟨.OP_PICK, some 2⟩,
  ⟨.OP_ROLL, some 2⟩,
  ⟨.OP_ROT, some 3⟩,
  ⟨.OP_SWAP, some 2⟩,
  ⟨.OP_TUCK, some 2⟩,
  ⟨.OP_TOALTSTACK, some 1⟩,
  ⟨.OP_FROMALTSTACK, some 0⟩,
  ⟨.OP_1ADD, some 1⟩,
  ⟨.OP_1SUB, some 1⟩,
  ⟨.OP_NEGATE, some 1⟩,
  ⟨.OP_ABS, some 1⟩,
  ⟨.OP_ADD, some 2⟩,
  ⟨.OP_SUB, some 2⟩,
  ⟨.OP_NUMNOTEQUAL, some 2⟩,
  ⟨.OP_LESSTHAN, some 2⟩,
  ⟨.OP_GREATERTHAN, some 2⟩,
  ⟨.OP_LESSTHANOREQUAL, some 2⟩,
  ⟨.OP_GREATERTHANOREQUAL, some 2⟩,
  ⟨.OP_MIN, some 2⟩,
  ⟨.OP_MAX, some 2⟩,
  ⟨.OP_BOOLAND, some 2⟩,
  ⟨.OP_BOOLOR, some 2⟩,
  ⟨.OP_NOT, some 1⟩,
  ⟨.OP_0NOTEQUAL, some 1⟩,
  ⟨.OP_EQUAL, some 2⟩,
  ⟨.OP_EQUALVERIFY, some 2⟩,
  ⟨.OP_NUMEQUAL, some 2⟩,
  ⟨.OP_NUMEQUALVERIFY, some 2⟩,
  ⟨.OP_WITHIN, some 3⟩,
  ⟨.OP_SHA256, some 1⟩,
  ⟨.OP_HASH256, some 1⟩,
  ⟨.OP_RIPEMD160, some 1⟩,
  ⟨.OP_HASH160, some 1⟩,
  ⟨.OP_CHECKSIG, some 2⟩,
  ⟨.OP_CHECKSIGVERIFY, some 2⟩,
  ⟨.OP_CHECKSIGADD, some 3⟩,
  ⟨.OP_CHECKMULTISIG, none⟩,
  ⟨.OP_CHECKMULTISIGVERIFY, none⟩,
  ⟨.OP_CHECKSEQUENCEVERIFY, some 1⟩,
  ⟨.OP_CHECKLOCKTIMEVERIFY, some 1⟩,
  ⟨.OP_VERIFY, some 1⟩,
  ⟨.OP_SIZE, some 1⟩
]

example : opcodeArityFixtures.all (fun fixture =>
    fixture.opcode.fixedMainStackInputs? == fixture.expected) = true := by
  native_decide

theorem opcodeArityFixtures_cover (opcode : Opcode) :
    opcode ∈ opcodeArityFixtures.map (·.opcode) := by
  cases opcode <;> simp [opcodeArityFixtures]

end LeanMiniscript.Script
