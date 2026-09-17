import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-!
# Pre-Tapscript signature encoding

The byte checks and matching order target Bitcoin Core v31.1 at
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, `src/script/interpreter.cpp`.
They apply to ECDSA CHECKSIG and legacy CHECKMULTISIG. `SignatureChecks`
selects these checks by signature version and implements Schnorr byte rules.
-/

/-- BIP 66 encoding, including the final sighash byte. This checks the shape
    of R and S, not whether either scalar produces a valid signature. -/
def isValidSignatureEncoding (sig : StackElement) : Bool := Id.run do
  if sig.size < 9 || sig.size > 73 then return false
  if sig[0]! != 0x30 || sig[1]!.toNat != sig.size - 3 then return false
  let lenR := sig[3]!.toNat
  if 5 + lenR ≥ sig.size then return false
  let lenS := sig[5 + lenR]!.toNat
  if lenR + lenS + 7 != sig.size then return false
  if sig[2]! != 0x02 || lenR == 0 then return false
  if sig[4]! &&& 0x80 != 0 then return false
  if lenR > 1 && sig[4]! == 0 && sig[5]! &&& 0x80 == 0 then return false
  if sig[lenR + 4]! != 0x02 || lenS == 0 then return false
  if sig[lenR + 6]! &&& 0x80 != 0 then return false
  if lenS > 1 && sig[lenR + 6]! == 0 && sig[lenR + 7]! &&& 0x80 == 0 then
    return false
  return true

/-- secp256k1's group order. -/
def secp256k1Order : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- secp256k1's group order divided by two, rounded down. -/
def secp256k1HalfOrder : Nat :=
  0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0

/-- Core's lax scalar parser replaces both scalars with zero if either
    overflows the group order. Such signatures pass LOW_S but fail crypto
    verification. Otherwise LOW_S compares S with half the group order. -/
def isLowDERSignature (sig : StackElement) : Bool :=
  if !isValidSignatureEncoding sig then false
  else
    let lenR := sig[3]!.toNat
    let lenS := sig[5 + lenR]!.toNat
    let readScalar := fun (bytes : ByteArray) =>
      bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0
    let r := readScalar (sig.extract 4 (4 + lenR))
    let s := readScalar (sig.extract (lenR + 6) (lenR + 6 + lenS))
    r ≥ secp256k1Order || s ≥ secp256k1Order || s ≤ secp256k1HalfOrder

/-- Only ALL, NONE, and SINGLE, optionally with ANYONECANPAY, are defined. -/
def isDefinedHashtypeSignature (sig : StackElement) : Bool :=
  if sig.size == 0 then false
  else
    let hashType := sig[sig.size - 1]! &&& 0x7f
    1 ≤ hashType && hashType ≤ 3

/-- STRICTENC accepts 33-byte compressed and 65-byte uncompressed keys.
    Curve membership is left to cryptographic verification. -/
def isCompressedOrUncompressedPubKey (pubkey : StackElement) : Bool :=
  (pubkey.size == 33 && (pubkey[0]! == 0x02 || pubkey[0]! == 0x03)) ||
    (pubkey.size == 65 && pubkey[0]! == 0x04)

/-- Empty signatures bypass signature encoding checks. Error precedence is
    DER, LOW_S, then the STRICTENC sighash check. -/
def checkSignatureEncoding (flags : ScriptFlags) (sig : StackElement) :
    Except ScriptError Unit :=
  if sig.size == 0 then .ok ()
  else if (flags.derSig || flags.lowS || flags.strictEncoding) &&
      !isValidSignatureEncoding sig then .error .sigDer
  else if flags.lowS && !isLowDERSignature sig then .error .sigHighS
  else if flags.strictEncoding && !isDefinedHashtypeSignature sig then
    .error .sigHashType
  else .ok ()

def checkPubKeyEncoding (flags : ScriptFlags) (pubkey : StackElement) :
    Except ScriptError Unit :=
  if flags.strictEncoding && !isCompressedOrUncompressedPubKey pubkey then
    .error .pubkeyType
  else .ok ()

/-- Signature errors precede public-key errors, including when the signature
    is empty and only the public-key check remains. -/
def checkECDSAEncoding (flags : ScriptFlags) (sig pubkey : StackElement) :
    Except ScriptError Unit := do
  checkSignatureEncoding flags sig
  checkPubKeyEncoding flags pubkey

@[simp] theorem checkSignatureEncoding_empty (flags : ScriptFlags) :
    checkSignatureEncoding flags falseElement = .ok () := by
  rfl

@[simp] theorem checkECDSAEncoding_empty (flags : ScriptFlags)
    (pubkey : StackElement) :
    checkECDSAEncoding flags falseElement pubkey =
      checkPubKeyEncoding flags pubkey := by
  rfl

/-- Core checks the historical dummy after matching and NULLFAIL. Its absence
    is a stack error; a present nonempty dummy fails only with NULLDUMMY. -/
def checkMultiSigDummy (flags : ScriptFlags) :
    Option StackElement → Except ScriptError Unit
  | none => .error .stackUnderflow
  | some dummy =>
      if nullDummySatisfied flags dummy then .ok () else .error .nullDummy

/-- Match legacy multisignatures in top-first stack order. Only reached pairs
    are checked: success consumes a signature, each attempt consumes a key,
    and too few remaining keys stops matching before another encoding check.
    An empty signature list succeeds without inspecting any key. -/
def checkMultiSigWithEncoding
    (verify : StackElement → StackElement → ByteArray → Bool)
    (flags : ScriptFlags) (sigHash : ByteArray) :
    Stack → Stack → Except ScriptError Bool
  | [], _ => .ok true
  | _ :: _, [] => .ok false
  | sig :: signatures, pubkey :: pubkeys => do
      checkECDSAEncoding flags sig pubkey
      let remaining := if verify sig pubkey sigHash then signatures
        else sig :: signatures
      if remaining.length > pubkeys.length then return false
      checkMultiSigWithEncoding verify flags sigHash remaining pubkeys
termination_by _ pubkeys => pubkeys.length

/-- A malformed first pair fails independently of every verifier result. -/
theorem checkMultiSigWithEncoding_first_error
    (verify : StackElement → StackElement → ByteArray → Bool)
    {flags : ScriptFlags} {sigHash : ByteArray} {sig pubkey : StackElement}
    {signatures pubkeys : Stack} {error : ScriptError}
    (encoded : checkECDSAEncoding flags sig pubkey = .error error) :
    checkMultiSigWithEncoding verify flags sigHash (sig :: signatures)
      (pubkey :: pubkeys) = .error error := by
  simp only [checkMultiSigWithEncoding, encoded]
  rfl

/-- Pointwise agreement of the per-key verifier preserves the complete
    checked matching result, including its encoding failures. -/
theorem checkMultiSigWithEncoding_congr
    {first second : StackElement → StackElement → ByteArray → Bool}
    (agree : ∀ sig pubkey hash, first sig pubkey hash = second sig pubkey hash)
    (flags : ScriptFlags) (sigHash : ByteArray) (signatures pubkeys : Stack) :
    checkMultiSigWithEncoding first flags sigHash signatures pubkeys =
      checkMultiSigWithEncoding second flags sigHash signatures pubkeys := by
  have equal : first = second := funext fun sig => funext fun pubkey =>
    funext fun hash => agree sig pubkey hash
  rw [equal]

end LeanMiniscript.Script
