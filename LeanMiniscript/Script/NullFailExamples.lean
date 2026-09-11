import LeanMiniscript.Script.Evaluator

namespace LeanMiniscript.Script

/-!
# NULLFAIL fixtures

These examples cover the common NULLFAIL boundary for CHECKSIG, CHECKSIGADD,
and CHECKMULTISIG. A failed check may push its ordinary false result only when
every supplied signature is empty or the flag is disabled.
-/

private def nullFailFlags : ScriptFlags := {}

private def nullFailDisabledFlags : ScriptFlags where
  nullFail := false

private def nullFailTx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def pubkey : StackElement := ⟨#[0x02]⟩
private def signature : StackElement := ⟨#[0x30]⟩

example (rejected : checkSig signature pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIG] [pubkey, signature] [] nullFailFlags nullFailTx
      (.failure .sigNullFail) := by
  exact Eval.checksigNullFail rejected (by native_decide)

example (rejected : checkSig falseElement pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIG] [pubkey, falseElement] [] nullFailFlags nullFailTx
      (.success [falseElement] []) := by
  exact Eval.checksigFalse rejected
    (falseElement_nullFailSatisfied nullFailFlags) Eval.done

example (rejected : checkSig signature pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIG] [pubkey, signature] [] nullFailDisabledFlags nullFailTx
      (.success [falseElement] []) := by
  apply Eval.checksigFalse rejected
  · simp [nullFailSatisfied, nullFailDisabledFlags]
  · exact Eval.done

example (rejected : checkSig signature pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIGADD] [pubkey, scriptNum 2, signature] []
      nullFailFlags nullFailTx (.failure .sigNullFail) := by
  apply Eval.checksigadd_nullfail_failure (count := 2)
  · rfl
  · exact rejected
  · native_decide

example (rejected : checkSig falseElement pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIGADD] [pubkey, scriptNum 2, falseElement] []
      nullFailFlags nullFailTx (.success [scriptNum 2] []) := by
  apply Eval.checksigadd_failure (count := 2)
  · rfl
  · exact rejected
  · exact falseElement_nullFailSatisfied nullFailFlags
  · exact Eval.done

private def rejectingOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => false)
    (fun _signatures _pubkeys _sigHash => false)

private def isFailure (expected : ScriptError) : ExecResult → Bool
  | .failure actual => actual == expected
  | _ => false

example : isFailure .sigNullFail (evaluate rejectingOracle [.op .OP_CHECKSIG]
    [pubkey, signature] [] nullFailFlags nullFailTx) = true := by
  native_decide

example : isFailure .sigNullFail (evaluate rejectingOracle [.op .OP_CHECKSIGADD]
    [pubkey, scriptNum 2, signature] [] nullFailFlags nullFailTx) = true := by
  native_decide

example : isFailure .sigNullFail (evaluate rejectingOracle [.op .OP_CHECKMULTISIG]
    [scriptNum 1, pubkey, scriptNum 1, signature, falseElement] []
      nullFailFlags nullFailTx) = true := by
  native_decide

end LeanMiniscript.Script
