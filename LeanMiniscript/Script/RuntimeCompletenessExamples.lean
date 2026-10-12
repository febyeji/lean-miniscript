import LeanMiniscript.Script.RuntimeCompletenessProofs

namespace LeanMiniscript.Script.RuntimeCompletenessExamples

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty, sigVersion := .tapscript }
private def oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)
private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩
private def run (script : Script) (stack : Stack) (weight : Nat) : WeightedResult :=
  evaluateWithRuntimeLimits oracle script stack [] {} ctx weight

-- All three signature opcodes debit the same 50 units. The final CHECKSIGADD
-- reaches the exact budget boundary after the preceding two checks succeed.
private def signatures : Script :=
  [.pushData (bytes 64), .pushData (bytes 32), .op .OP_CHECKSIGVERIFY,
   .pushData (bytes 64), .pushData (bytes 32), .op .OP_CHECKSIG, .op .OP_DROP,
   .pushData (bytes 64), .pushNum 0, .pushData (bytes 32), .op .OP_CHECKSIGADD]

example : staticValidationWeight signatures = 150 ∧
    run signatures [] (staticValidationWeight signatures) = .success [trueElement] [] 0 ∧
    run signatures [] 149 = .failure .tapscriptValidationWeight := by native_decide

-- The source bound deliberately includes empty signatures, which debit zero.
example : staticValidationWeight [.op .OP_CHECKSIG] = 50 ∧
    run [.op .OP_CHECKSIG] [bytes 32, ByteArray.empty] 0 =
      .success [falseElement] [] 0 := by native_decide

-- An outer inactive branch contains nested IF/NOTIF and repeated ELSEs.
-- Restoring it preserves the selected result and the entire unused budget.
private def nested : Script :=
  [.op .OP_IF, .op .OP_IF, .op .OP_CHECKSIG,
   .op .OP_ELSE, .op .OP_CHECKSIGVERIFY, .op .OP_ELSE, .op .OP_NOTIF,
   .op .OP_CHECKSIGADD, .op .OP_ENDIF, .op .OP_ENDIF,
   .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF]

example : staticValidationWeight nested = 150 ∧
    run nested [falseElement] (staticValidationWeight nested) =
      .success [trueElement] [] 150 := by native_decide

-- A selected nested NOTIF executes while its ELSE signature is skipped.
private def selectedNested : Script :=
  [.op .OP_IF, .pushNum 0, .op .OP_NOTIF, .pushNum 1,
   .op .OP_ELSE, .op .OP_CHECKSIG, .op .OP_ENDIF, .op .OP_ENDIF]

example : run selectedNested [trueElement] (staticValidationWeight selectedNested) =
    .success [trueElement] [] 50 := by native_decide

-- Projected execution alone omits this 521-byte push; source completion
-- additionally needs the push bound on the inactive branch.
private def skippedPush (size : Nat) : Script :=
  [.op .OP_IF, .pushData (bytes size), .op .OP_ENDIF, .pushNum 1]

example : (match evaluate oracle (skippedPush 521) [falseElement] [] {} ctx with
      | .success stack alt => stack == [trueElement] && alt.isEmpty
      | .failure _ => false) = true ∧
    run (skippedPush 521) [falseElement] 0 = .failure .pushSize ∧
    run (skippedPush 520) [falseElement] 0 = .success [trueElement] [] 0 := by native_decide

-- Sufficient weight preserves ordinary operand errors. CHECKSIGADD's count
-- decoding still precedes the debit and cryptographic verification.
example : run [.op .OP_CHECKSIGADD] [bytes 32, bytes 5, bytes 64] 50 =
    .failure .scriptNumOverflow := by native_decide

end LeanMiniscript.Script.RuntimeCompletenessExamples
