import LeanMiniscript.Script.Evaluator
import LeanMiniscript.Miniscript.Acceptance

namespace LeanMiniscript.Script

/-!
# Signature-version regression fixtures

These exercise byte rules and injected cryptographic results, not real BIP340
verification or transaction-derived sighashes. Tapscript budget exhaustion and
Taproot witness/control-block validation remain outside these fixtures.
-/

private def flags : ScriptFlags := {}
private def tx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[0xab]⟩
  sigVersion := .tapscript

private def key : StackElement := ⟨Array.replicate 32 0x11⟩
private def sig : StackElement := ⟨Array.replicate 64 0x22⟩
private def explicitSig (hashType : UInt8) : StackElement :=
  ⟨sig.data.push hashType⟩
private def badSig : StackElement := ⟨#[0x30]⟩
private def unknownKey : StackElement := ⟨#[0x02]⟩
private def compressedKey : StackElement := ⟨#[0x02] ++ Array.replicate 32 0x11⟩
private def uncompressedKey : StackElement := ⟨#[0x04] ++ Array.replicate 64 0x11⟩
private def derSig : StackElement := ⟨#[0x30, 6, 2, 1, 1, 2, 1, 1, 1]⟩

private def rejecting : CryptoOracle := CryptoOracle.pureLeanHashes
  (fun _ _ _ => false) (fun _ _ _ => false)
private def acceptingAll : CryptoOracle := CryptoOracle.pureLeanHashes
  (fun _ _ _ => true) (fun _ _ _ => true)
private def ecdsaOnly : CryptoOracle := CryptoOracle.pureLeanHashes
  (fun _ _ _ => true) (fun _ _ _ => false)
private def schnorrOnly : CryptoOracle := CryptoOracle.pureLeanHashes
  (fun _ _ _ => false) (fun bytes pubkey hash =>
    stackElementEq bytes sig && stackElementEq pubkey key &&
      stackElementEq hash tx.sigHash)

private def errorIs (expected : ScriptError) {α : Type} : Except ScriptError α → Bool
  | .error actual => actual == expected
  | .ok _ => false
private def failed (expected : ScriptError) : ExecResult → Bool
  | .failure actual => actual == expected
  | _ => false
private def single (expected : StackElement) : ExecResult → Bool
  | .success [actual] [] => stackElementEq actual expected
  | _ => false

private def checksig (oracle : CryptoOracle) (signature pubkey : StackElement)
    (context : TxContext := tx) (settings : ScriptFlags := flags) : ExecResult :=
  evaluate oracle [.op .OP_CHECKSIG] [pubkey, signature] [] settings context

/-- Exactly 64 and 65 bytes enter Schnorr hash-type checks. -/
example : (List.range 76).all (fun size =>
    let signature : StackElement := ⟨Array.replicate size 0⟩
    if size == 64 then !errorIs .schnorrSigSize (checkSchnorrSignatureEncoding signature)
    else if size == 65 then errorIs .schnorrSigHashType (checkSchnorrSignatureEncoding signature)
    else errorIs .schnorrSigSize (checkSchnorrSignatureEncoding signature)) = true := by
  native_decide

/-- Explicit default and reserved sighash bits are rejected; only six bytes
    are accepted. The callback sees the same 64-byte signature in each case. -/
example : (List.range 256).all (fun value =>
    let hashType := UInt8.ofNat value
    let allowed := [1, 2, 3, 0x81, 0x82, 0x83].contains value
    let result := checksig schnorrOnly (explicitSig hashType) key
    if allowed then single trueElement result
    else failed .schnorrSigHashType result) = true := by
  native_decide

/-- Tapscript ignores all three ECDSA encoding flags. -/
example : single trueElement (checksig schnorrOnly sig key tx
    { flags with derSig := true, lowS := true, strictEncoding := true }) = true := by
  native_decide

/-- ECDSA and Schnorr use independent callbacks. -/
example : failed .schnorrSig (checksig ecdsaOnly sig key) &&
    single trueElement (checksig schnorrOnly sig key) &&
    single trueElement (checksig ecdsaOnly sig key { tx with sigVersion := .base }
      { flags with strictEncoding := false }) &&
    failed .sigNullFail (checksig schnorrOnly sig key { tx with sigVersion := .witnessV0 }
      { flags with strictEncoding := false }) = true := by
  native_decide

/-- Empty signatures bypass verifiers but still enforce public-key rules. -/
example : single falseElement (checksig acceptingAll falseElement key) &&
    single falseElement (checksig ecdsaOnly falseElement key) &&
    single falseElement (checksig schnorrOnly falseElement key) &&
    failed .tapscriptEmptyPubkey (checksig schnorrOnly falseElement falseElement) &&
    failed .tapscriptEmptyPubkey (checksig schnorrOnly badSig falseElement) = true := by
  native_decide

/-- Unknown nonempty key versions accept any nonempty signature without
    verifier or Schnorr-encoding checks, unless the policy flag is enabled. -/
example : [1, 31, 33, 65].all (fun size =>
    let pubkey : StackElement := ⟨Array.replicate size 0⟩
    single trueElement (checksig rejecting badSig pubkey) &&
    single falseElement (checksig rejecting falseElement pubkey) &&
    failed .discourageUpgradablePubkeyType (checksig rejecting badSig pubkey tx
      { flags with discourageUpgradablePubKeyType := true }) &&
    failed .discourageUpgradablePubkeyType (checksig rejecting falseElement pubkey tx
      { flags with discourageUpgradablePubKeyType := true })) = true := by
  native_decide

/-- Known-key error precedence: key, size, hash type, then verification. A
    cryptographically rejected Schnorr signature always aborts. -/
example : failed .schnorrSigSize (checksig schnorrOnly badSig key) &&
    failed .schnorrSigHashType (checksig rejecting (explicitSig 0) key) &&
    failed .schnorrSig (checksig rejecting sig key tx { flags with nullFail := false }) &&
    failed .discourageUpgradablePubkeyType (checksig schnorrOnly badSig unknownKey tx
      { flags with discourageUpgradablePubKeyType := true }) = true := by
  native_decide

/-- Witness-v0 compressed-key policy is version-specific and follows DER
    and STRICTENC key checks. -/
example :
    let settings := { flags with witnessPubKeyType := true }
    let witness := { tx with sigVersion := .witnessV0 }
    let legacy := { tx with sigVersion := .base }
    single trueElement (checksig ecdsaOnly derSig compressedKey witness settings) &&
    failed .witnessPubkeyType (checksig ecdsaOnly derSig uncompressedKey witness settings) &&
    single trueElement (checksig ecdsaOnly derSig uncompressedKey legacy settings) &&
    failed .sigDer (checksig ecdsaOnly badSig uncompressedKey witness settings) &&
    failed .pubkeyType (checksig ecdsaOnly falseElement unknownKey witness settings) &&
    failed .witnessPubkeyType (checksig ecdsaOnly falseElement uncompressedKey witness settings) = true := by
  native_decide

/-- Witness-v0 multisignature matching checks only reached keys, including
    compressed-key policy, and skips unused trailing malformed keys. -/
example :
    let witness := { tx with sigVersion := .witnessV0 }
    let settings := { flags with witnessPubKeyType := true }
    errorIs .witnessPubkeyType (checkMultiSigFor (fun _ _ _ => true) settings witness
      [derSig] [uncompressedKey, compressedKey]) &&
    (match checkMultiSigFor (fun _ _ _ => true) settings witness
        [derSig] [compressedKey, unknownKey] with
      | .ok true => true
      | _ => false) = true := by
  native_decide

/-- CHECKSIGADD preserves negative counts and adds one only on success. -/
example : single (scriptNum (-1)) (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [key, scriptNum (-2), sig] [] flags tx) &&
    single (scriptNum (-2)) (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [key, scriptNum (-2), falseElement] [] flags tx) &&
    single (scriptNum 2147483648) (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [key, scriptNum 2147483647, sig] [] flags tx) &&
    failed .schnorrSig (evaluate rejecting [.op .OP_CHECKSIGADD]
      [key, scriptNum 0, sig] [] { flags with nullFail := false } tx) = true := by
  native_decide

/-- Availability precedes stack/number errors; in Tapscript, accumulator
    decoding precedes signature/key checks. -/
example : [.base, .witnessV0].all (fun version =>
    let context := { tx with sigVersion := version }
    failed .badOpcode (evaluate schnorrOnly [.op .OP_CHECKSIGADD] [] [] flags context) &&
    failed .badOpcode (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [falseElement, ⟨#[1, 0]⟩, badSig] [] flags context)) &&
    failed .stackUnderflow (evaluate schnorrOnly [.op .OP_CHECKSIGADD] [] [] flags tx) &&
    failed .scriptNumNonMinimal (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [falseElement, ⟨#[1, 0]⟩, badSig] [] flags tx) &&
    failed .scriptNumOverflow (evaluate schnorrOnly [.op .OP_CHECKSIGADD]
      [falseElement, ⟨#[1, 0, 0, 0, 0]⟩, badSig] [] flags tx) = true := by
  native_decide

/-- Disabled CHECKMULTISIG precedes all frame validation but does not execute
    in skipped branches. CHECKSIGADD also stays skipped outside Tapscript. -/
example : failed .tapscriptCheckMultiSig (evaluate schnorrOnly [.op .OP_CHECKMULTISIG]
      [] [] flags tx) &&
    failed .tapscriptCheckMultiSig (evaluate schnorrOnly [.op .OP_CHECKMULTISIG]
      [scriptNum 21] [] flags tx) &&
    single trueElement (evaluate schnorrOnly
      [.pushNum 0, .op .OP_IF, .op .OP_CHECKMULTISIG, .op .OP_ENDIF, .pushNum 1]
      [] [] flags tx) &&
    single trueElement (evaluate schnorrOnly
      [.pushNum 0, .op .OP_IF, .op .OP_CHECKSIGADD, .op .OP_ENDIF, .pushNum 1]
      [] [] flags { tx with sigVersion := .base }) = true := by
  native_decide

/-- Relational byte failure and its unique terminal result. -/
example : Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] [key, badSig] [] flags tx
    (.failure .schnorrSigSize) := by
  apply Eval.checksig_encoding_failure
  rfl

example {result : ExecResult}
    (evaluated : Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] [key, badSig] [] flags tx result) :
    result = .failure .schnorrSigSize :=
  Eval.checksigEncodingFailure_result (by rfl) evaluated

example : Eval [.op .OP_CHECKSIGADD] [] [] flags { tx with sigVersion := .base }
    (.failure .badOpcode) := by
  apply Eval.checksigadd_unavailable
  decide

example : Eval [.op .OP_CHECKMULTISIG] [] [] flags tx
    (.failure .tapscriptCheckMultiSig) :=
  Eval.checkMultiSigOperandFailure (by rfl)

/-- A witness context cannot accidentally run legacy signature rules. -/
example : ¬ LeanMiniscript.Miniscript.ModeledContextVersion .p2wsh
    { tx with sigVersion := .base } := by
  simp [LeanMiniscript.Miniscript.ModeledContextVersion]

example : LeanMiniscript.Miniscript.ModeledContextFlags .tapscript
    { flags with derSig := true, lowS := true, strictEncoding := true, nullFail := false } := by
  simp [LeanMiniscript.Miniscript.ModeledContextFlags, flags]

end LeanMiniscript.Script
