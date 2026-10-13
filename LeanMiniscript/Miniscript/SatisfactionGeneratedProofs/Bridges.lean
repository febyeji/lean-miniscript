import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: numeric and encoding bridges

Timelock execution facts, signature-encoding checks, and size bounds for
selected witness elements.
-/

/-! ## Numeric and encoding bridges -/

/-- The two codec facts needed to execute a well-formed timelock literal. -/
structure TimelockExecutionFacts (n : Nat) (flags : ScriptFlags) : Prop where
  decoded : decodeScriptNum (scriptNat n) flags.minimalData
    maxTimelockScriptNumBytes = .ok (Int.ofNat n)
  positive : castToBool (scriptNat n) = true

namespace TimelockExecutionFacts

/-- BIP 379's positive, below-bit-31 timelock bound supplies both the extended
    five-byte decoder result and the truthiness of the canonical operand. -/
theorem of_validTimelockArg {n : Nat} {flags : ScriptFlags}
    (valid : validTimelockArg n) : TimelockExecutionFacts n flags := by
  rcases valid with ⟨positive, bound⟩
  constructor
  · apply decodeScriptNum_mono (small := maxArithmeticScriptNumBytes)
    · decide
    · apply decodeScriptNum_scriptNat_of_lt
      simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
        maxArithmeticScriptNatExclusive] using bound
  · apply castToBool_scriptNat_of_pos_of_lt
    · omega
    · simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
        maxArithmeticScriptNatExclusive] using bound

end TimelockExecutionFacts

/-- A context-valid key accepts the canonical empty signature under the flags
    and signature version required by that Miniscript context. -/
theorem checkSigEncodingFor_empty_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {flags : ScriptFlags}
    {txCtx : TxContext} (wellFormed : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx txCtx)
    (modeled : ModeledContextFlags scriptCtx flags) :
    checkSigEncodingFor flags txCtx.sigVersion falseElement key.bytes =
      .ok () := by
  cases scriptCtx with
  | p2wsh =>
      rcases wellFormed with ⟨keySize, keyPrefix⟩
      rcases modeled with ⟨_, _, _, _, strict⟩
      simp only [ModeledContextVersion] at version
      have h0 : 0 < key.bytes.size := by omega
      have dataH0 : 0 < key.bytes.data.size := by
        simpa [ByteArray.size_data] using h0
      have indexEq : key.bytes[0]! = key.bytes.get! 0 := by
        rw [getElem!_pos key.bytes 0 h0]
        change key.bytes.data[0] = key.bytes.data[0]!
        rw [getElem!_pos key.bytes.data 0 dataH0]
      have compressed : isCompressedPubKey key.bytes = true := by
        unfold isCompressedPubKey
        rw [indexEq]
        simp [keySize, keyPrefix]
      have ordinary : isCompressedOrUncompressedPubKey key.bytes = true := by
        unfold isCompressedOrUncompressedPubKey
        rw [indexEq]
        simp [keySize, keyPrefix]
      simp [checkSigEncodingFor, version, checkECDSAEncoding,
        checkPubKeyEncoding, strict, compressed, ordinary]
      rfl
  | tapscript =>
      simp only [validResolvedPubKey] at wellFormed
      simp only [ModeledContextVersion] at version
      have keySize : key.bytes.size = 32 := wellFormed
      have falseEq : falseElement = ByteArray.empty := by
        simp [falseElement, ByteArray.ext_iff]
      simp [checkSigEncodingFor, version, keySize, falseEq]
      rfl

private theorem isCompressedPubKey_of_validCompressed
    {bytes : StackElement} (valid : validCompressedPubKeyBytes bytes) :
    isCompressedPubKey bytes = true := by
  rcases valid with ⟨size, headByte⟩
  have positive : 0 < bytes.size := by omega
  have dataPositive : 0 < bytes.data.size := by
    simpa [ByteArray.size_data] using positive
  have indexEq : bytes[0]! = bytes.get! 0 := by
    rw [getElem!_pos bytes 0 positive]
    change bytes.data[0] = bytes.data[0]!
    rw [getElem!_pos bytes.data 0 dataPositive]
  unfold isCompressedPubKey
  rw [indexEq]
  simp [size, headByte]

private theorem isOrdinaryPubKey_of_validCompressed
    {bytes : StackElement} (valid : validCompressedPubKeyBytes bytes) :
    isCompressedOrUncompressedPubKey bytes = true := by
  rcases valid with ⟨size, headByte⟩
  have positive : 0 < bytes.size := by omega
  have dataPositive : 0 < bytes.data.size := by
    simpa [ByteArray.size_data] using positive
  have indexEq : bytes[0]! = bytes.get! 0 := by
    rw [getElem!_pos bytes 0 positive]
    change bytes.data[0] = bytes.data[0]!
    rw [getElem!_pos bytes.data 0 dataPositive]
  unfold isCompressedOrUncompressedPubKey
  rw [indexEq]
  simp [size, headByte]

/-- In witness-v0, a signature which passes encoding checks against one key
    passes them against every other context-valid compressed key. The signature
    encoding check is key-independent; target validity discharges the two
    possible public-key encoding checks. -/
theorem checkSigEncodingFor_witnessV0_rekey
    {flags : ScriptFlags} {signature sourceKey targetKey : StackElement}
    (targetValid : validCompressedPubKeyBytes targetKey)
    (encoded : checkSigEncodingFor flags .witnessV0 signature sourceKey = .ok ()) :
    checkSigEncodingFor flags .witnessV0 signature targetKey = .ok () := by
  have compressed := isCompressedPubKey_of_validCompressed targetValid
  have ordinary := isOrdinaryPubKey_of_validCompressed targetValid
  cases signatureEncoded : checkSignatureEncoding flags signature with
  | error error =>
      simp only [checkSigEncodingFor, checkECDSAEncoding] at encoded
      rw [signatureEncoded] at encoded
      contradiction
  | ok value =>
      cases value
      simp [checkSigEncodingFor, checkECDSAEncoding, signatureEncoded,
        checkPubKeyEncoding, compressed, ordinary]
      rfl

private theorem isValidSignatureEncoding_size_le
    {signature : StackElement}
    (valid : isValidSignatureEncoding signature = true) :
    signature.size ≤ 73 := by
  by_cases bound : signature.size ≤ 73
  · exact bound
  · have oversized : signature.size > 73 := by omega
    simp [isValidSignatureEncoding, oversized] at valid

private theorem checkSignatureEncoding_size_le_of_strict
    {flags : ScriptFlags} {signature : StackElement}
    (strict : flags.strictEncoding = true)
    (checked : checkSignatureEncoding flags signature = .ok ()) :
    signature.size ≤ 73 := by
  by_cases empty : signature.size = 0
  · omega
  have valid : isValidSignatureEncoding signature = true := by
    cases validEq : isValidSignatureEncoding signature with
    | false => simp [checkSignatureEncoding, empty, strict, validEq] at checked
    | true => rfl
  exact isValidSignatureEncoding_size_le valid

private theorem checkSchnorrSignatureEncoding_size_le
    {signature : StackElement}
    (checked : checkSchnorrSignatureEncoding signature = .ok ()) :
    signature.size ≤ 65 := by
  by_cases bound : signature.size ≤ 65
  · exact bound
  · have not64 : signature.size ≠ 64 := by omega
    have not65 : signature.size ≠ 65 := by omega
    simp [checkSchnorrSignatureEncoding, not64, not65] at checked

/-- A context-valid key is always a legal witness element. -/
theorem validResolvedPubKey_size_le
    {scriptCtx : ScriptContext} {key : PubKey}
    (valid : validResolvedPubKey scriptCtx key) :
    key.bytes.size ≤ maxScriptElementSize := by
  cases scriptCtx <;>
    simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size,
      maxScriptElementSize]

theorem validResolvedPubKey_size_ne_zero
    {scriptCtx : ScriptContext} {key : PubKey}
    (valid : validResolvedPubKey scriptCtx key) :
    key.bytes.size ≠ 0 := by
  cases scriptCtx <;>
    simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size]

/-- A selected signature which passes the modeled encoding checks is a legal
    witness element. Tapscript additionally uses the context-valid 32-byte key
    shape to select Schnorr encoding. -/
theorem selectedSignature_size_le
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} {signature : StackElement}
    (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (encodings : env.EncodingSound flags)
    (selected : env.signatureFor key = some signature) :
    signature.size ≤ maxScriptElementSize := by
  have encoded := encodings key signature selected
  cases scriptCtx with
  | p2wsh =>
      rcases modeled with ⟨_, _, _, _, strict⟩
      simp only [ModeledContextVersion] at version
      rw [version] at encoded
      have checked : checkSignatureEncoding flags signature = .ok () := by
        cases checkedSig : checkSignatureEncoding flags signature with
        | error error =>
            simp only [checkSigEncodingFor, checkECDSAEncoding] at encoded
            rw [checkedSig] at encoded
            contradiction
        | ok value =>
            cases value
            rfl
      have := checkSignatureEncoding_size_le_of_strict strict checked
      change signature.size ≤ 520
      omega
  | tapscript =>
      simp only [validResolvedPubKey, PubKey.size] at valid
      simp only [ModeledContextVersion] at version
      rw [version] at encoded
      by_cases empty : signature.size = 0
      · change signature.size ≤ 520
        omega
      have checked : checkSchnorrSignatureEncoding signature = .ok () := by
        simpa [checkSigEncodingFor, valid, empty] using encoded
      have := checkSchnorrSignatureEncoding_size_le checked
      change signature.size ≤ 520
      omega

theorem selectedPreimage_size_le
    {env : SatEnv} (sound : env.Sound) {lock : HashLock}
    {preimage : StackElement}
    (selected : env.preimageFor lock = some preimage) :
    preimage.size ≤ maxScriptElementSize := by
  have exactSize := (sound.preimageMatches selected).1
  change preimage.size ≤ 520
  omega

theorem selectedNonPreimage_size_le
    {env : SatEnv} (sound : env.Sound) (lock : HashLock) :
    (env.nonPreimageFor lock).size ≤ maxScriptElementSize := by
  have exactSize := (sound.nonPreimageMismatches lock).1
  change (env.nonPreimageFor lock).size ≤ 520
  omega

theorem falseElement_size_le :
    falseElement.size ≤ maxScriptElementSize := by decide

theorem trueElement_size_le :
    trueElement.size ≤ maxScriptElementSize := by decide

theorem selectedSignature_size_ne_zero
    {key : PubKey} {env : SatEnv} {signature : StackElement}
    (sound : env.Sound) (selected : env.signatureFor key = some signature) :
    signature.size ≠ 0 := by
  intro empty
  have signatureEmpty : signature = ByteArray.empty :=
    ByteArray.size_eq_zero_iff.mp empty
  have falseEmpty : falseElement = ByteArray.empty := by
    simp [falseElement, ByteArray.ext_iff]
  have signatureFalse : signature = falseElement :=
    signatureEmpty.trans falseEmpty.symm
  have verified := sound.signatureValid selected
  rw [signatureFalse, sound.emptySignatureInvalid key] at verified
  contradiction

end LeanMiniscript.Miniscript
