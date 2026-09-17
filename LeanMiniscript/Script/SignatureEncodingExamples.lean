import LeanMiniscript.Script.Evaluator

namespace LeanMiniscript.Script

/-! # ECDSA encoding, matching order, and error precedence fixtures -/

private def strict : ScriptFlags := {}
private def derOnly : ScriptFlags := { strictEncoding := false, derSig := true }
private def lowOnly : ScriptFlags := { strictEncoding := false, lowS := true }
private def relaxed : ScriptFlags := { strictEncoding := false, nullFail := false }
private def tx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ⟨#[]⟩ }
private def goodKey : StackElement := ⟨#[0x02] ++ Array.replicate 32 1⟩
private def badKey : StackElement := ⟨#[0x06] ++ Array.replicate 64 1⟩
private def goodSig : StackElement := ⟨#[0x30, 6, 2, 1, 1, 2, 1, 1, 1]⟩
private def badSig : StackElement := ⟨#[0x30]⟩
private def rejecting : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
private def accepting : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => true)

private def errorIs {α : Type} (expected : ScriptError) : Except ScriptError α → Bool
  | .error actual => actual == expected
  | .ok _ => false

private def okIs (expected : Bool) : Except ScriptError Bool → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def isSingleSuccess (expected : StackElement) : ExecResult → Bool
  | .success [actual] [] => stackElementEq actual expected
  | _ => false

private def isFailure (expected : ScriptError) : ExecResult → Bool
  | .failure actual => actual == expected
  | _ => false

/-- Minimum DER length, zero scalars, and required sign padding are valid. -/
example : [goodSig, ⟨#[0x30, 6, 2, 1, 0, 2, 1, 0, 1]⟩,
    ⟨#[0x30, 7, 2, 2, 0, 0x80, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 7, 2, 1, 1, 2, 2, 0, 0x80, 1]⟩].all
      isValidSignatureEncoding = true := by native_decide

/-- Every strict-DER rejection branch has a concrete byte fixture. -/
example : [falseElement, badSig,
    ⟨#[0x31, 6, 2, 1, 1, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 7, 2, 1, 1, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 5, 1, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 1, 1, 2, 2, 1, 1]⟩,
    ⟨#[0x30, 6, 3, 1, 1, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 0, 2, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 1, 0x80, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 7, 2, 2, 0, 1, 2, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 1, 1, 3, 1, 1, 1]⟩,
    ⟨#[0x30, 6, 2, 2, 1, 1, 2, 0, 1]⟩,
    ⟨#[0x30, 6, 2, 1, 1, 2, 1, 0x80, 1]⟩,
    ⟨#[0x30, 7, 2, 1, 1, 2, 2, 0, 1, 1]⟩,
    ⟨Array.replicate 74 0⟩].all (fun sig => !isValidSignatureEncoding sig) = true := by
  native_decide

private def maximumSig : StackElement :=
  ⟨#[0x30, 70, 2, 33, 0, 0x80] ++ Array.replicate 31 0 ++
    #[2, 33, 0, 0x80] ++ Array.replicate 31 0 ++ #[1]⟩

example : maximumSig.size == 73 && isValidSignatureEncoding maximumSig = true := by
  native_decide

/-- Check all 256 sighash bytes; only the six defined forms are accepted. -/
example : (List.range 256).all (fun value =>
    isDefinedHashtypeSignature ⟨goodSig.data.set! 8 (UInt8.ofNat value)⟩ ==
      [1, 2, 3, 0x81, 0x82, 0x83].contains value) = true := by native_decide

/-- Key shape validation checks exact length and prefix, not curve membership. -/
example : [goodKey, ⟨#[3] ++ Array.replicate 32 0⟩,
    ⟨#[4] ++ Array.replicate 64 0⟩].all isCompressedOrUncompressedPubKey = true := by
  native_decide

example : [falseElement, badKey, ⟨#[2] ++ Array.replicate 31 0⟩,
    ⟨#[2] ++ Array.replicate 64 0⟩, ⟨#[4] ++ Array.replicate 32 0⟩,
    ⟨#[4] ++ Array.replicate 65 0⟩].all
      (fun key => !isCompressedOrUncompressedPubKey key) = true := by native_decide

private def halfOrderBytes : Array UInt8 :=
  #[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d,
    0xdf, 0xe9, 0x2f, 0x46, 0x68, 0x1b, 0x20, 0xa0]
private def orderBytes : Array UInt8 :=
  #[0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
    0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b,
    0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41]

private def scalarSig (r s : Array UInt8) (hashType : UInt8 := 1) : StackElement :=
  ⟨#[0x30, UInt8.ofNat (r.size + s.size + 4), 2, UInt8.ofNat r.size] ++ r ++
    #[2, UInt8.ofNat s.size] ++ s ++ #[hashType]⟩
private def highSig : StackElement := scalarSig #[1] (halfOrderBytes.set! 31 0xa1)

/-- LOW_S's boundary is inclusive, and scalar overflow reproduces Core's
    zeroed invalid signature rather than treating overflow as high S. -/
example : isLowDERSignature (scalarSig #[1] halfOrderBytes) &&
    !isLowDERSignature highSig &&
    isLowDERSignature (scalarSig #[1] #[0]) &&
    isLowDERSignature (scalarSig #[1] orderBytes) &&
    isLowDERSignature (scalarSig orderBytes (halfOrderBytes.set! 31 0xa1)) = true := by
  native_decide

example : errorIs .sigDer (checkSignatureEncoding lowOnly badSig) &&
    errorIs .sigHighS (checkSignatureEncoding lowOnly highSig) &&
    errorIs .sigHashType (checkSignatureEncoding strict
      (scalarSig #[1] #[1] 5)) &&
    !errorIs .sigHashType (checkSignatureEncoding derOnly
      (scalarSig #[1] #[1] 5)) = true := by native_decide

/-- DER precedes high S, high S precedes sighash, and signature errors precede
    public-key errors. An empty signature still checks the key. -/
example : errorIs .sigDer (checkECDSAEncoding { strict with lowS := true } badSig badKey) &&
    errorIs .sigHighS (checkECDSAEncoding { strict with lowS := true }
      (scalarSig #[1] (halfOrderBytes.set! 31 0xa1) 5) badKey) &&
    errorIs .sigHashType (checkECDSAEncoding strict (scalarSig #[1] #[1] 5) badKey) &&
    errorIs .pubkeyType (checkECDSAEncoding strict falseElement badKey) = true := by
  native_decide

example : Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] [badKey, badSig] [] strict tx
    (.failure .sigDer) := by
  apply Eval.checksig_encoding_failure
  rfl

example {result : ExecResult}
    (evaluated : Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] [badKey, badSig] []
      strict tx result) : result = .failure .sigDer :=
  Eval.checksigEncodingFailure_result (by rfl) evaluated

example : Eval [.op .OP_CHECKMULTISIG]
    [scriptNum 1, badKey, scriptNum 1, badSig, trueElement] [] strict tx
    (.failure .sigDer) := by
  apply Eval.checkmultisig_encoding_failure (operands := {
    pubkeys := [badKey], signatures := [badSig], dummy := some trueElement, rest := [] })
  · rfl
  · simp only [checkMultiSigFor, checkSigEncodingFor, tx]
    rfl

/-- Encoding errors occur before any verifier result and before NULLFAIL and
    NULLDUMMY. Passing encoding still permits a terminal NULLFAIL error. -/
example : isFailure .sigDer (evaluate accepting [.op .OP_CHECKSIG]
      [badKey, badSig] [] strict tx) &&
    isFailure .pubkeyType (evaluate accepting [.op .OP_CHECKSIG]
      [badKey, falseElement] [] strict tx) &&
    isFailure .sigNullFail (evaluate rejecting [.op .OP_CHECKSIG]
      [goodKey, goodSig] [] strict tx) &&
    isFailure .sigDer (evaluate rejecting [.op .OP_CHECKMULTISIG]
      [scriptNum 1, badKey, scriptNum 1, badSig, trueElement] [] strict tx) &&
    isFailure .sigNullFail (evaluate rejecting [.op .OP_CHECKMULTISIG]
      [scriptNum 1, goodKey, scriptNum 1, goodSig, trueElement] [] strict tx) = true := by
  native_decide

/-- A signature is retained after a failed key attempt and consumed only
    after a successful match. Ordered matching can skip keys but not reorder
    signatures. -/
private def secondKey : StackElement := ⟨#[3] ++ Array.replicate 32 1⟩
private def secondSig : StackElement := ⟨#[0x30, 6, 2, 1, 2, 2, 1, 1, 1]⟩
private def selective : CryptoOracle := CryptoOracle.pureLeanHashes fun sig key _ =>
  (stackElementEq sig goodSig && stackElementEq key goodKey) ||
    (stackElementEq sig secondSig && stackElementEq key secondKey)

example : okIs true (checkMultiSigFor selective.checkSig strict tx
      [goodSig] [secondKey, goodKey]) &&
    okIs true (checkMultiSigFor selective.checkSig strict tx
      [goodSig, secondSig] [goodKey, goodKey, secondKey]) &&
    okIs false (checkMultiSigFor selective.checkSig strict tx
      [goodSig, secondSig] [secondKey, goodKey]) = true := by native_decide

/-- Early matching failure skips later signatures, while a successful first
    match reaches their encoding checks. Prevalidating every input is wrong. -/
example : okIs false (checkMultiSigFor rejecting.checkSig derOnly tx
      [goodSig, badSig] [goodKey, goodKey]) &&
    errorIs .sigDer (checkMultiSigFor accepting.checkSig derOnly tx
      [goodSig, badSig] [goodKey, goodKey]) &&
    okIs true (checkMultiSigFor accepting.checkSig strict tx
      [goodSig] [goodKey, badKey]) &&
    errorIs .pubkeyType (checkMultiSigFor accepting.checkSig strict tx
      [goodSig] [badKey, goodKey]) &&
    okIs true (checkMultiSigFor rejecting.checkSig strict tx
      [] [badKey]) = true := by native_decide

example : isSingleSuccess falseElement (evaluate rejecting [.op .OP_CHECKMULTISIG]
    [scriptNum 2, goodKey, goodKey, scriptNum 2, goodSig, badSig, falseElement]
      [] { derOnly with nullFail := false } tx) = true := by native_decide

/-- A missing dummy is checked after encoding and NULLFAIL; with no
    signatures, matching succeeds and reports its absence immediately. -/
example : isFailure .sigDer (evaluate accepting [.op .OP_CHECKMULTISIG]
      [scriptNum 1, goodKey, scriptNum 1, badSig] [] strict tx) &&
    isFailure .sigNullFail (evaluate rejecting [.op .OP_CHECKMULTISIG]
      [scriptNum 1, goodKey, scriptNum 1, goodSig] [] strict tx) &&
    isFailure .stackUnderflow (evaluate accepting [.op .OP_CHECKMULTISIG]
      [scriptNum 1, goodKey, scriptNum 1, goodSig] [] strict tx) &&
    isFailure .stackUnderflow (evaluate rejecting [.op .OP_CHECKMULTISIG]
      [scriptNum 0, scriptNum 0] [] strict tx) = true := by native_decide

/-- Rejected matching that passes NULLFAIL then checks NULLDUMMY. -/
example : isFailure .nullDummy (evaluate rejecting [.op .OP_CHECKMULTISIG]
    [scriptNum 1, goodKey, scriptNum 1, goodSig, trueElement]
      [] { strict with nullFail := false } tx) = true := by native_decide

/-- Disabling all ECDSA byte checks preserves the abstract verification
    boundary. CHECKSIGADD never applies DER rules to Schnorr-shaped bytes. -/
example : isSingleSuccess trueElement (evaluate accepting [.op .OP_CHECKSIG]
      [badKey, badSig] [] relaxed tx) &&
    isSingleSuccess (scriptNum 2) (evaluate (CryptoOracle.pureLeanHashes (fun _ _ _ => false)
      (fun _ _ _ => true)) [.op .OP_CHECKSIGADD]
      [⟨Array.replicate 32 1⟩, scriptNum 1, ⟨Array.replicate 64 1⟩] [] strict
        { tx with sigVersion := .tapscript }) =
    true := by native_decide

end LeanMiniscript.Script
