import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Script.BigStep

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

/-- Exact fixed main-stack arity for every modeled opcode. `CHECKMULTISIG`
    remains separate because its input count is encoded in the stack. -/
def opcodeArityFixtures : List OpcodeArityFixture := [
  ⟨.OP_NOP, some 0⟩,
  ⟨.OP_IF, some 1⟩,
  ⟨.OP_NOTIF, some 1⟩,
  ⟨.OP_ELSE, some 0⟩,
  ⟨.OP_ENDIF, some 0⟩,
  ⟨.OP_IFDUP, some 1⟩,
  ⟨.OP_DUP, some 1⟩,
  ⟨.OP_SWAP, some 2⟩,
  ⟨.OP_TOALTSTACK, some 1⟩,
  ⟨.OP_FROMALTSTACK, some 0⟩,
  ⟨.OP_ADD, some 2⟩,
  ⟨.OP_BOOLAND, some 2⟩,
  ⟨.OP_BOOLOR, some 2⟩,
  ⟨.OP_0NOTEQUAL, some 1⟩,
  ⟨.OP_EQUAL, some 2⟩,
  ⟨.OP_EQUALVERIFY, some 2⟩,
  ⟨.OP_NUMEQUAL, some 2⟩,
  ⟨.OP_SHA256, some 1⟩,
  ⟨.OP_HASH256, some 1⟩,
  ⟨.OP_RIPEMD160, some 1⟩,
  ⟨.OP_HASH160, some 1⟩,
  ⟨.OP_CHECKSIG, some 2⟩,
  ⟨.OP_CHECKSIGADD, some 3⟩,
  ⟨.OP_CHECKMULTISIG, none⟩,
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

private def fixtureFlags : ScriptFlags := {}

private def fixtureTxContext : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

/-! ## Raw opcode boundaries -/

example : Eval [.op .OP_DUP] [] [] fixtureFlags fixtureTxContext
    (.failure .stackUnderflow) := by
  exact Eval.fixedArityStackUnderflow rfl (by decide)

example : Eval [.op .OP_EQUAL] [trueElement] [] fixtureFlags fixtureTxContext
    (.failure .stackUnderflow) := by
  exact Eval.fixedArityStackUnderflow rfl (by decide)

example : Eval [.op .OP_CHECKSIGADD] [trueElement, falseElement] []
    fixtureFlags fixtureTxContext (.failure .stackUnderflow) := by
  exact Eval.fixedArityStackUnderflow rfl (by decide)

example : Eval [.op .OP_IF, .pushNum 1, .op .OP_ENDIF] [] []
    fixtureFlags fixtureTxContext (.failure .stackUnderflow) := by
  exact Eval.fixedArityStackUnderflow rfl (by decide)

example : Eval [.op .OP_FROMALTSTACK] [trueElement] []
    fixtureFlags fixtureTxContext (.failure .altStackUnderflow) := by
  exact Eval.fromAltStackUnderflow

/-- The explicit main-stack error excludes a successful result for the same
    fixed-arity opcode state. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_EQUAL] [trueElement] [] fixtureFlags fixtureTxContext
      (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.fixedArityStackUnderflow_result
    (arity := rfl) (underflow := by decide) evaluated
  cases impossible

/-- The explicit alternate-stack error likewise excludes normal
    `OP_FROMALTSTACK` execution. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_FROMALTSTACK] [trueElement] [] fixtureFlags fixtureTxContext
      (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.fromAltStack_empty_result evaluated
  cases impossible

/-! ## Compiler-generated boundaries -/

private def compressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0x11).toArray⟩

/-- `c:pk_k` without a signature reaches CHECKSIG with only the pushed key. -/
example : Eval (compile (.c (.pk_k compressedKey))) [] []
    fixtureFlags fixtureTxContext (.failure .stackUnderflow) := by
  simpa [compile, compileWithKeyHash] using
    (Eval.pushDataNext (data := compressedKey)
      (Eval.fixedArityStackUnderflow
        (opcode := .OP_CHECKSIG) (required := 2)
        (arity := rfl) (underflow := by decide)))

/-- Wrapper `a:` requires a value to protect on the alternate stack before
    executing its child. -/
example : Eval (compile (.a .zero)) [] []
    fixtureFlags fixtureTxContext (.failure .stackUnderflow) := by
  exact Eval.fixedArityStackUnderflow rfl (by decide)

end LeanMiniscript.Script
