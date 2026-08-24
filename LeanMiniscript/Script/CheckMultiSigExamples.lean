import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

open LeanMiniscript.Miniscript

/-!
# Legacy CHECKMULTISIG operand fixtures

These examples pin Bitcoin Core's variable stack-frame decoding order for
`OP_CHECKMULTISIG`. The main stack is top-first: the public-key count is on top,
followed by public keys, the signature count, signatures, the historical dummy,
and the untouched stack tail.
-/

private def checkMultiSigFlags : ScriptFlags := {}

private def relaxedCheckMultiSigFlags : ScriptFlags where
  minimalData := false

private def checkMultiSigTx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def keyA : StackElement := ⟨#[0x02]⟩
private def keyB : StackElement := ⟨#[0x03]⟩
private def signature : StackElement := ⟨#[0x30]⟩
private def nonMinimalCountOne : StackElement := ⟨#[0x01, 0x00]⟩

private def pubkeyA : PubKey := PubKey.ofBytes keyA
private def pubkeyB : PubKey := PubKey.ofBytes keyB

private def oneOfTwoFragment : CoreFragment := .multi 1 [pubkeyA, pubkeyB]

private def oneOfTwoStack : Stack :=
  [scriptNum 2, keyB, keyA, scriptNum 1, signature, falseElement]

private def oneOfTwoOperands : CheckMultiSigOperands where
  pubkeys := [keyB, keyA]
  signatures := [signature]
  dummy := falseElement
  rest := []

/-! ## Decoder order and bounds -/

example : decodeCheckMultiSigOperands checkMultiSigFlags oneOfTwoStack =
    .ok oneOfTwoOperands := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags [] =
    .error .stackUnderflow := by
  rfl

/-- The public-key count is decoded before the remaining frame is inspected. -/
example : decodeCheckMultiSigOperands checkMultiSigFlags [nonMinimalCountOne] =
    .error .scriptNumNonMinimal := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags [scriptNum (-1)] =
    .error .pubkeyCount := by
  rfl

/-- The consensus 20-key bound is checked before pubkey-frame underflow. -/
example : decodeCheckMultiSigOperands checkMultiSigFlags [scriptNum 21] =
    .error .pubkeyCount := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    (scriptNum 20 :: List.replicate 20 keyA ++ [scriptNum 0, falseElement]) =
      .ok {
        pubkeys := List.replicate 20 keyA
        signatures := []
        dummy := falseElement
        rest := []
      } := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 2147483648] = .error .scriptNumOverflow := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 2, keyA, scriptNum 1] = .error .stackUnderflow := by
  rfl

/-- Once the pubkey frame is present, the signature count is decoded before the
    signature and dummy frame is inspected. -/
example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 1, keyA, nonMinimalCountOne] =
      .error .scriptNumNonMinimal := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 1, keyA, scriptNum (-1)] = .error .signatureCount := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 1, keyA, scriptNum 2] = .error .signatureCount := by
  rfl

example : decodeCheckMultiSigOperands checkMultiSigFlags
    [scriptNum 1, keyA, scriptNum 1, signature] =
      .error .stackUnderflow := by
  rfl

/-- Relaxed flags accept redundant count encodings while preserving the same
    decoded frame. -/
example : decodeCheckMultiSigOperands relaxedCheckMultiSigFlags
    [nonMinimalCountOne, keyA, nonMinimalCountOne, signature, falseElement] =
      .ok {
        pubkeys := [keyA]
        signatures := [signature]
        dummy := falseElement
        rest := []
      } := by
  rfl

/-! ## Evaluation boundaries -/

example : Eval [.op .OP_CHECKMULTISIG] [] [] checkMultiSigFlags checkMultiSigTx
    (.failure .stackUnderflow) := by
  exact Eval.checkMultiSigOperandFailure (by rfl)

/-- NULLDUMMY is checked at the decoded dummy position, below all signatures. -/
example : Eval [.op .OP_CHECKMULTISIG]
    [scriptNum 2, keyB, keyA, scriptNum 1, signature, trueElement] []
    checkMultiSigFlags checkMultiSigTx (.failure .nullDummy) := by
  apply Eval.checkmultisig_nulldummy_failure (operands := {
    pubkeys := [keyB, keyA]
    signatures := [signature]
    dummy := trueElement
    rest := []
  })
  · rfl
  · simp [nullDummySatisfied, checkMultiSigFlags, stackElementEq,
      trueElement, falseElement]

example : ¬ ∃ main alt,
    Eval [.op .OP_CHECKMULTISIG]
      [scriptNum 2, keyB, keyA, scriptNum 1, signature, trueElement] []
      checkMultiSigFlags checkMultiSigTx (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.checkMultiSigNullDummyFailure_result
    (operands := {
      pubkeys := [keyB, keyA]
      signatures := [signature]
      dummy := trueElement
      rest := []
    })
    (decoded := by rfl)
    (invalidDummy := by
      simp [nullDummySatisfied, checkMultiSigFlags, stackElementEq,
        trueElement, falseElement])
    evaluated
  cases impossible

example
    (verified : checkMultiSig [signature] [keyB, keyA]
      checkMultiSigTx.sigHash = true) :
    Eval [.op .OP_CHECKMULTISIG] oneOfTwoStack [] checkMultiSigFlags
      checkMultiSigTx (.success [trueElement] []) := by
  apply Eval.checkmultisig_success (operands := oneOfTwoOperands)
  · rfl
  · simp [nullDummySatisfied, checkMultiSigFlags, oneOfTwoOperands,
      stackElementEq, falseElement]
  · exact verified
  · exact Eval.done

example
    (rejected : checkMultiSig [signature] [keyB, keyA]
      checkMultiSigTx.sigHash = false) :
    Eval [.op .OP_CHECKMULTISIG] oneOfTwoStack [] checkMultiSigFlags
      checkMultiSigTx (.success [falseElement] []) := by
  apply Eval.checkmultisig_failure (operands := oneOfTwoOperands)
  · rfl
  · simp [nullDummySatisfied, checkMultiSigFlags, oneOfTwoOperands,
      stackElementEq, falseElement]
  · exact rejected
  · exact Eval.done

/-- Compiler-emitted `multi(1, keyA, keyB)` reaches the decoder with signatures
    above the historical dummy and keys in top-first evaluation order. -/
example
    (verified : checkMultiSig [signature] [keyB, keyA]
      checkMultiSigTx.sigHash = true) :
    Eval (compile oneOfTwoFragment) [signature, falseElement] []
      checkMultiSigFlags checkMultiSigTx (.success [trueElement] []) := by
  simp only [oneOfTwoFragment, compile, compileWithKeyHash, compileKeyPushes]
  apply Eval.pushNum
  apply Eval.pushData
  apply Eval.pushData
  apply Eval.pushNum
  apply Eval.checkmultisig_success (operands := oneOfTwoOperands)
  · rfl
  · simp [nullDummySatisfied, checkMultiSigFlags, oneOfTwoOperands,
      stackElementEq, falseElement]
  · exact verified
  · exact Eval.done

/-- A decoder failure excludes successful evaluation of the same state. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_CHECKMULTISIG] [] [] checkMultiSigFlags checkMultiSigTx
      (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.checkMultiSigOperandFailure_result
    (decoded := by rfl) evaluated
  cases impossible

end LeanMiniscript.Script
