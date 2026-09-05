import LeanMiniscript.Script.Evaluator

namespace LeanMiniscript.Script

/-! # Executable evaluator fixtures -/

private def fixtureFlags : ScriptFlags := {}

private def fixtureTxContext : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def rejectingOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => false)
    (fun _signatures _pubkeys _sigHash => false)

private def acceptingOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => true)
    (fun _signatures _pubkeys _sigHash => true)

private def isSingleSuccess (expected : StackElement) : ExecResult → Bool
  | .success [actual] [] => stackElementEq actual expected
  | _ => false

private def isFailure (expected : ScriptError) : ExecResult → Bool
  | .failure actual => actual == expected
  | _ => false

/-- Ordinary numeric execution is directly computable. -/
example : isSingleSuccess (scriptNum 3)
    (evaluate rejectingOracle [.pushNum 1, .pushNum 2, .op .OP_ADD]
      [] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

/-- OP_NOP preserves both stacks and continues with the remaining script. -/
example : Eval [.op .OP_NOP] [trueElement] [falseElement]
    fixtureFlags fixtureTxContext
    (.success [trueElement] [falseElement]) := by
  apply Eval.nop
  exact Eval.empty [trueElement] [falseElement] fixtureFlags fixtureTxContext

example : evaluate rejectingOracle [.op .OP_NOP] [trueElement]
    [falseElement] fixtureFlags fixtureTxContext =
    .success [trueElement] [falseElement] := by
  simp [evaluate]

/-- Repeated same-depth `ELSE` toggles use the same executable splitter as the
    relational semantics. -/
example : isSingleSuccess (scriptNum 2)
    (evaluate rejectingOracle
      [.op .OP_IF, .pushNum 1, .op .OP_ELSE, .pushNum 2,
        .op .OP_ELSE, .pushNum 3, .op .OP_ENDIF]
      [falseElement] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

/-- Typed failures are returned rather than display strings. -/
example : isFailure .stackUnderflow
    (evaluate rejectingOracle [.op .OP_SWAP] [trueElement] []
      fixtureFlags fixtureTxContext) = true := by
  native_decide

/-- Runtime errors in active unclosed branches precede the structural error
    Bitcoin Core reports only after successful execution reaches EOF. -/
example : isFailure .verify
    (evaluate rejectingOracle [.op .OP_IF, .op .OP_VERIFY]
      [trueElement, falseElement] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

example : isFailure .unbalancedConditional
    (evaluate rejectingOracle [.op .OP_IF, .op .OP_VERIFY]
      [falseElement, falseElement] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

example : isFailure .verify
    (evaluate rejectingOracle
      [.op .OP_IF, .op .OP_ELSE, .pushNum 1, .op .OP_ELSE, .op .OP_VERIFY]
      [trueElement, falseElement] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

private def sha256Abc : StackElement :=
  ⟨#[0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
      0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
      0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad]⟩

/-- The executable oracle uses the pinned pure-Lean SHA-256 implementation. -/
example : isSingleSuccess sha256Abc
    (evaluate rejectingOracle [.pushData "abc".toUTF8, .op .OP_SHA256]
      [] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

/-- Signature behavior is injected independently of the executable hashes. -/
example : isSingleSuccess trueElement
    (evaluate acceptingOracle [.op .OP_CHECKSIG]
      [⟨#[0x02]⟩, ⟨#[0x30]⟩] [] fixtureFlags fixtureTxContext) = true := by
  native_decide

/-- The model oracle evaluator is equivalent to the relational semantics. -/
example {script : Script} {stack altStack : Stack} {result : ExecResult} :
    Eval script stack altStack fixtureFlags fixtureTxContext result ↔
      evaluate CryptoOracle.model script stack altStack fixtureFlags
        fixtureTxContext = result :=
  evaluate_model_iff

end LeanMiniscript.Script
