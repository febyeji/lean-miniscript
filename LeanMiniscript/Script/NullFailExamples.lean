import LeanMiniscript.Script.Evaluator

namespace LeanMiniscript.Script

/-!
# NULLFAIL fixtures

These examples cover the pre-Tapscript NULLFAIL boundary for CHECKSIG and
CHECKMULTISIG. A failed check may push its ordinary false result only when
every supplied signature is empty or the flag is disabled.
-/

private def nullFailFlags : ScriptFlags := { strictEncoding := false }

private def nullFailDisabledFlags : ScriptFlags where
  strictEncoding := false
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
  apply Eval.checksigNullFail
  have encoded : checkSigEncodingFor nullFailFlags nullFailTx.sigVersion
      signature pubkey = .ok () := rfl
  have verified : verifySigFor checkSig checkSchnorrSig nullFailTx
      signature pubkey = false := rejected
  simp only [checkSigWithEncoding, encoded, verified, Bool.false_eq_true, ↓reduceIte]
  rfl

example (rejected : checkSig falseElement pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIG] [pubkey, falseElement] [] nullFailFlags nullFailTx
      (.success [falseElement] []) := by
  apply Eval.checksigFalse _ Eval.done
  apply checkSigWithEncoding_empty
  · rfl
  · exact rejected

example (rejected : checkSig signature pubkey nullFailTx.sigHash = false) :
    Eval [.op .OP_CHECKSIG] [pubkey, signature] [] nullFailDisabledFlags nullFailTx
      (.success [falseElement] []) := by
  apply Eval.checksigFalse _ Eval.done
  have encoded : checkSigEncodingFor nullFailDisabledFlags nullFailTx.sigVersion
      signature pubkey = .ok () := rfl
  have verified : verifySigFor checkSig checkSchnorrSig nullFailTx
      signature pubkey = false := rejected
  simp only [checkSigWithEncoding, encoded, verified, Bool.false_eq_true, ↓reduceIte]
  rfl

private def rejectingOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => false)

private def isFailure (expected : ScriptError) : ExecResult → Bool
  | .failure actual => actual == expected
  | _ => false

example : isFailure .sigNullFail (evaluate rejectingOracle [.op .OP_CHECKSIG]
    [pubkey, signature] [] nullFailFlags nullFailTx) = true := by
  native_decide

example : isFailure .badOpcode (evaluate rejectingOracle [.op .OP_CHECKSIGADD]
    [pubkey, scriptNum 2, signature] [] nullFailFlags nullFailTx) = true := by
  native_decide

example : isFailure .sigNullFail (evaluate rejectingOracle [.op .OP_CHECKMULTISIG]
    [scriptNum 1, pubkey, scriptNum 1, signature, falseElement] []
      nullFailFlags nullFailTx) = true := by
  native_decide

end LeanMiniscript.Script
