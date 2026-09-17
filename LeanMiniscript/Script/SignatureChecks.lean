import LeanMiniscript.Script.SignatureEncoding

namespace LeanMiniscript.Script

/-!
# Signature-version rules

Targets Bitcoin Core v31.1, commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, `src/script/interpreter.cpp`,
and BIP341/342. Signature hashing uses transaction data when supplied;
abstract contexts keep
their external hash. These opcode checks are resource-free;
`ValidationWeight` adds the full-witness Tapscript execution budget.
-/

def isCompressedPubKey (pubkey : StackElement) : Bool :=
  pubkey.size == 33 && (pubkey[0]! == 0x02 || pubkey[0]! == 0x03)

/-- An implicit default occupies 64 bytes. A 65-byte signature must have one
    of the six explicit non-default BIP341 sighash types. -/
def checkSchnorrSignatureEncoding (sig : StackElement) :
    Except ScriptError Unit :=
  if sig.size != 64 && sig.size != 65 then .error .schnorrSigSize
  else if sig.size == 65 &&
      !(sig[64]! == 1 || sig[64]! == 2 || sig[64]! == 3 ||
        sig[64]! == 0x81 || sig[64]! == 0x82 || sig[64]! == 0x83) then
    .error .schnorrSigHashType
  else .ok ()

/-- Byte errors in Core's order, before cryptographic verification. For
    Tapscript, public-key versions precede signature-size and sighash checks;
    unknown nonempty key versions bypass Schnorr checks unless discouraged. -/
def checkSigEncodingFor (flags : ScriptFlags) (version : SignatureVersion)
    (sig pubkey : StackElement) : Except ScriptError Unit := do
  match version with
  | .base | .witnessV0 =>
      checkECDSAEncoding flags sig pubkey
      if version = .witnessV0 then
        if flags.witnessPubKeyType && !isCompressedPubKey pubkey then
          throw .witnessPubkeyType
  | .tapscript =>
      if pubkey.size == 0 then throw .tapscriptEmptyPubkey
      if pubkey.size != 32 then
        if flags.discourageUpgradablePubKeyType then
          throw .discourageUpgradablePubkeyType
      else if sig.size != 0 then
        checkSchnorrSignatureEncoding sig

/-- Compute a separate signing hash for each signature's hash-type byte.
    Abstract contexts retain their supplied hash. Transaction contexts must
    contain script-path metadata when used by a Tapscript signature opcode. -/
def signatureHashFor (ctx : TxContext) (sig : StackElement) :
    Except ScriptError ByteArray :=
  match ctx.taproot with
  | none => .ok ctx.sigHash
  | some hashContext =>
      match hashContext.spendPath with
      | .keyPath => .error .schnorrSigHashType
      | .scriptPath _ _ _ =>
          match Bitcoin.taprootSignatureHash hashContext
              (if sig.size = 65 then sig[64]! else 0) with
          | .error _ => .error .schnorrSigHashType
          | .ok digest => .ok digest

/-- Crypto dispatch with transaction-derived hashing errors kept distinct
    from a rejected Schnorr verification. Empty/unknown-key checks bypass
    hashing exactly as they bypass the cryptographic verifier. -/
def checkedVerifySigFor
    (ecdsa schnorr : StackElement → StackElement → ByteArray → Bool)
    (ctx : TxContext) (sig pubkey : StackElement) : Except ScriptError Bool :=
  match ctx.sigVersion with
  | .base | .witnessV0 => .ok (ecdsa sig pubkey ctx.sigHash)
  | .tapscript =>
      if sig.size == 0 then .ok false
      else if pubkey.size != 32 then .ok true
      else match signatureHashFor ctx sig with
        | .error error => .error error
        | .ok digest => .ok (schnorr (sig.extract 0 64) pubkey digest)

/-- Boolean compatibility boundary used by satisfaction environments.
    Hash construction failure cannot count as signature validity. -/
def verifySigFor
    (ecdsa schnorr : StackElement → StackElement → ByteArray → Bool)
    (ctx : TxContext) (sig pubkey : StackElement) : Bool :=
  match checkedVerifySigFor ecdsa schnorr ctx sig pubkey with
  | .error _ => false
  | .ok checked => checked

/-- Checked signature result shared by the executable and relational models.
    Rejected nonempty Schnorr signatures abort with SCHNORR_SIG even when
    NULLFAIL is disabled. Legacy rejection retains the flag-controlled rule. -/
def checkSigWithEncoding
    (ecdsa schnorr : StackElement → StackElement → ByteArray → Bool)
    (flags : ScriptFlags) (ctx : TxContext) (sig pubkey : StackElement) :
    Except ScriptError Bool :=
  match checkSigEncodingFor flags ctx.sigVersion sig pubkey with
  | .error error => .error error
  | .ok () =>
      match checkedVerifySigFor ecdsa schnorr ctx sig pubkey with
      | .error error => .error error
      | .ok checked =>
          if checked then .ok true
          else if ctx.sigVersion = .tapscript then
            if sig.size != 0 then .error .schnorrSig else .ok false
          else if nullFailSatisfied flags [sig] then .ok false
          else .error .sigNullFail

theorem checkSigWithEncoding_true
    {ecdsa schnorr : StackElement → StackElement → ByteArray → Bool}
    {flags : ScriptFlags} {ctx : TxContext} {sig pubkey : StackElement}
    (encoded : checkSigEncodingFor flags ctx.sigVersion sig pubkey = .ok ())
    (checked : verifySigFor ecdsa schnorr ctx sig pubkey = true) :
    checkSigWithEncoding ecdsa schnorr flags ctx sig pubkey = .ok true := by
  cases verified : checkedVerifySigFor ecdsa schnorr ctx sig pubkey with
  | error error => simp [verifySigFor, verified] at checked
  | ok valid =>
      have validTrue : valid = true := by simpa [verifySigFor, verified] using checked
      simp [checkSigWithEncoding, encoded, verified, validTrue]

theorem checkSigWithEncoding_empty
    {ecdsa schnorr : StackElement → StackElement → ByteArray → Bool}
    {flags : ScriptFlags} {ctx : TxContext} {pubkey : StackElement}
    (encoded : checkSigEncodingFor flags ctx.sigVersion falseElement pubkey = .ok ())
    (checked : verifySigFor ecdsa schnorr ctx falseElement pubkey = false) :
    checkSigWithEncoding ecdsa schnorr flags ctx falseElement pubkey = .ok false := by
  have verified : checkedVerifySigFor ecdsa schnorr ctx falseElement pubkey = .ok false := by
    cases version : ctx.sigVersion <;>
      simp only [verifySigFor, checkedVerifySigFor, version] at checked ⊢
    all_goals first | rfl | rw [checked]
  simp only [checkSigWithEncoding, encoded, verified, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [falseElement_nullFailSatisfied] <;> rfl

/-- Version errors precede accumulator decoding. -/
def decodeCheckSigAddCount (flags : ScriptFlags) (ctx : TxContext)
    (count : StackElement) : Except ScriptError Int :=
  if ctx.sigVersion ≠ .tapscript then .error .badOpcode
  else decodeScriptNum count flags.minimalData maxArithmeticScriptNumBytes

/-- Tapscript disables CHECKMULTISIG before count or stack validation. -/
def decodeCheckMultiSigOperandsFor (flags : ScriptFlags) (ctx : TxContext)
    (stack : Stack) : Except ScriptError CheckMultiSigOperands :=
  if ctx.sigVersion = .tapscript then .error .tapscriptCheckMultiSig
  else decodeCheckMultiSigOperands flags stack

/-- Legacy/witness-v0 matching checks only reached pairs. Its caller first
    uses `decodeCheckMultiSigOperandsFor` to reject the Tapscript opcode. -/
def checkMultiSigFor
    (ecdsa : StackElement → StackElement → ByteArray → Bool)
    (flags : ScriptFlags) (ctx : TxContext) :
    Stack → Stack → Except ScriptError Bool
  | [], _ => .ok true
  | _ :: _, [] => .ok false
  | sig :: signatures, pubkey :: pubkeys => do
      checkSigEncodingFor flags ctx.sigVersion sig pubkey
      let remaining := if ecdsa sig pubkey ctx.sigHash then signatures
        else sig :: signatures
      if remaining.length > pubkeys.length then return false
      checkMultiSigFor ecdsa flags ctx remaining pubkeys
termination_by _ pubkeys => pubkeys.length

end LeanMiniscript.Script
