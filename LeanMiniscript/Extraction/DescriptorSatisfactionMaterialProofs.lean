import LeanMiniscript.Extraction.DescriptorSatisfaction

namespace LeanMiniscript.Extraction.DescriptorSatisfactionMaterial

open LeanMiniscript.Script LeanMiniscript.Miniscript

/-- Filtering retains exactly supplied signatures whose encoding and
transaction-specific verification both pass. -/
theorem validated_signature_iff
    (material : DescriptorSatisfactionMaterial) (oracle : CryptoOracle)
    (flags : ScriptFlags) (context : TxContext) (key : PubKey) (signature : StackElement) :
    (material.validated oracle flags context).signatureFor key = some signature ↔
    material.signatureFor key = some signature ∧
    checkSigEncodingFor flags context.sigVersion signature key.bytes = .ok () ∧
    verifySigFor oracle.checkSig oracle.checkSchnorrSig context signature key.bytes = true := by
  simp only [validated, Option.filter_eq_some_iff]
  constructor
  · rintro ⟨supplied, valid⟩
    cases encoded : checkSigEncodingFor flags context.sigVersion signature key.bytes with
    | error error => simp [encoded] at valid
    | ok result =>
      cases result
      exact ⟨supplied, rfl, by simpa [encoded] using valid⟩
  · rintro ⟨supplied, encoded, valid⟩
    exact ⟨supplied, by simp [encoded, valid]⟩

/-- Retained preimages have exactly the hashlock's required size and digest. -/
theorem validated_preimage_iff
    (material : DescriptorSatisfactionMaterial) (oracle : CryptoOracle)
    (flags : ScriptFlags) (context : TxContext) (lock : HashLock) (preimage : StackElement) :
    (material.validated oracle flags context).preimageFor lock = some preimage ↔
    material.preimageFor lock = some preimage ∧
    preimage.size = 32 ∧ hashDigest oracle lock preimage = lock.expected := by
  simp only [validated, Option.filter_eq_some_iff, Bool.and_eq_true, beq_iff_eq]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨ByteArray.ext, fun same => congrArg ByteArray.data same⟩

/-- Signature encoding is established by filtering, for every retained key. -/
theorem validated_encodingSound
    (material : DescriptorSatisfactionMaterial) (oracle : CryptoOracle)
    (flags : ScriptFlags) (context : TxContext) :
    ((material.validated oracle flags context).toEnv context).EncodingSound flags := by
  intro key signature supplied
  exact ((validated_signature_iff material oracle flags context key signature).mp supplied).2.1

/-- Under oracle refinement, the retained signature and preimage facts supply
the corresponding abstract environment contract. Empty Tapscript signatures
are rejected by dispatch. Hash dissatisfaction material keeps its existing
caller-supplied nonpreimage contract. -/
theorem validated_sound
    (material : DescriptorSatisfactionMaterial) (oracle : CryptoOracle)
    (flags : ScriptFlags) (context : TxContext)
    (agreement : oracle.RefinesModel) (version : context.sigVersion = .tapscript)
    (nonPreimages : ∀ lock : HashLock, lock.Mismatches (material.nonPreimageFor lock)) :
    ((material.validated oracle flags context).toEnv context).Sound := by
  have ecdsa : oracle.checkSig = checkSig := funext fun sig =>
    funext fun key => funext fun hash => agreement.2.2.2.2.1 sig key hash
  have schnorr : oracle.checkSchnorrSig = checkSchnorrSig := funext fun sig =>
    funext fun key => funext fun hash => agreement.2.2.2.2.2 sig key hash
  refine ⟨?_, ?_, ?_, nonPreimages⟩
  · intro key signature supplied
    have valid := ((validated_signature_iff material oracle flags context key signature).mp supplied).2.2
    simpa only [toEnv, ecdsa, schnorr] using valid
  · intro key
    simp only [toEnv, verifySigFor, checkedVerifySigFor, version]
    rfl
  · intro lock preimage supplied
    obtain ⟨_, size, digest⟩ :=
      (validated_preimage_iff material oracle flags context lock preimage).mp supplied
    refine ⟨size, ?_⟩
    have hashes : hashDigest oracle lock preimage = lock.digest preimage := by
      cases lock with
      | sha256 hash => exact agreement.1 preimage
      | hash256 hash => exact agreement.2.1 preimage
      | ripemd160 hash => exact agreement.2.2.1 preimage
      | hash160 hash => exact agreement.2.2.2.1 preimage
    exact hashes.symm.trans digest

end LeanMiniscript.Extraction.DescriptorSatisfactionMaterial
