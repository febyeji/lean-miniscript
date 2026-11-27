import LeanMiniscript.Extraction.P2WSHNonMalleabilityKeyChoice
import LeanMiniscript.Extraction.TapscriptHashWitnessProofs

/-!
# Recovery of disclosed P2WSH signature material

A usable satisfaction contains selectors, public keys, selected signatures and selected
preimages. STRICTENC separates selectors and compressed keys from checked signatures.
The third-party condition identifies the key of a selected signature. This leaves one
lookup to check: a published preimage that passes a signature check for a fragment key.
-/

namespace LeanMiniscript.Extraction.P2WSHRecovery

open LeanMiniscript.Script LeanMiniscript.Miniscript

/-- Candidate spend-local premise for the preimage-to-signature lookup.
    The same item may fill both slots when the lookups agree. -/
def PublishedPreimageSignatureAgreement (root : CoreFragment) (env : SatEnv)
    (flags : ScriptFlags) (arguments : Witness) : Prop :=
  ∀ item ∈ arguments, ThirdPartyWitness root env.txCtx arguments [item] →
    (∃ lock ∈ root.hashLocks, env.preimageFor lock = some item) →
    ∀ key ∈ root.keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true →
      env.signatureFor key = some item

theorem agreement_of_disjoint {root env flags arguments}
    (disjoint : LocalPreimageSignatureDisjoint root env flags arguments) :
    PublishedPreimageSignatureAgreement root env flags arguments :=
  fun item mem eligible opened key hk checked =>
    (disjoint item mem eligible opened key hk checked).elim

private theorem valid_of_allKeysValid {ctx : ScriptContext} {keys : List PubKey}
    (valid : CoreFragment.allKeysValid ctx keys) :
    ∀ key ∈ keys, validResolvedPubKey ctx key := by
  induction keys with
  | nil => simp
  | cons key keys ih => exact List.forall_mem_cons.mpr ⟨valid.1, ih valid.2⟩

private theorem wellFormed_keys {ctx : ScriptContext} (root : CoreFragment) :
    root.WellFormed ctx → ∀ key ∈ root.keys, validResolvedPubKey ctx key := by
  induction root using CoreFragment.rec (motive_2 := fun children =>
      CoreFragment.allWellFormed ctx children →
        ∀ key ∈ CoreFragment.keysList children, validResolvedPubKey ctx key) with
  | multi _ _ | multi_a _ _ => exact fun wf => valid_of_allKeysValid wf.2.2.2
  | _ =>
    simp_all [CoreFragment.keys, CoreFragment.keysList, CoreFragment.WellFormed,
      CoreFragment.allWellFormed] <;> grind

/-- STRICTENC separates a checked signature from every compressed key of the
    enclosing script, including a key other than the one being checked. -/
theorem checked_ne_key (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {item : StackElement} {key k : PubKey}
    (version : env.txCtx.sigVersion = .witnessV0) (strict : flags.strictEncoding = true)
    (member : k ∈ sane.checked.fragment.keys)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true) :
    item ≠ k.bytes := by
  have encoded := P2WSHNonMalleabilityInversion.encoding_of_checkSigWithEncoding_ok checked
  rw [version] at encoded
  have rekeyed := checkSigEncodingFor_witnessV0_rekey
    (wellFormed_keys _ sane.checked.wellFormed k member) encoded
  exact P2WSHNonMalleabilityInversion.signature_ne_pubkey_of_strict
    (ctx := env.txCtx) strict version (version ▸ rekeyed)

/-- A checked item found in a source fragment's candidate material is either a
    selected signature for this key in that source or a preimage selected there.
    In particular, a source with disjoint keys leaves only the preimage case. -/
theorem checked_source_material (sane : SaneFragment .p2wsh)
    {source : CoreFragment} {env : SatEnv} {flags : ScriptFlags} {arguments other : Witness}
    {item : StackElement} {key : PubKey} (sound : env.Sound)
    (version : env.txCtx.sigVersion = .witnessV0) (modeled : ModeledContextFlags .p2wsh flags)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (mem : item ∈ other) (keyMem : key ∈ sane.checked.fragment.keys)
    (keysIn : ∀ k ∈ source.keys, k ∈ sane.checked.fragment.keys)
    (material : TapscriptWitness.Material source env item)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true) :
    (key ∈ source.keys ∧ env.signatureFor key = some item) ∨
      ∃ lock ∈ source.hashLocks, env.preimageFor lock = some item := by
  have valid := P2WSHNonMalleabilitySubcase.verifySigFor_of_checkSigWithEncoding_true checked
  have strict := modeled.2.2.2.2
  rcases material with rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, selected⟩ | preimage
  · rw [sound.emptySignatureInvalid] at valid
    contradiction
  · exact (P2WSHNonMalleabilityKeyChoice.checked_signature_ne_true strict version checked rfl).elim
  · exact (checked_ne_key sane version strict (keysIn k hk) checked rfl).elim
  · by_cases same : key = k
    · exact same ▸ Or.inl ⟨hk, selected⟩
    · exact (third.1 item mem key keyMem k (keysIn k hk) same valid (sound.signatureValid selected)).elim
  · exact Or.inr preimage

/-- Disjoint roles identify the source of a checked signature among both
    satisfaction and dissatisfaction rows of a descendant. -/
theorem checked_source_signature (sane : SaneFragment .p2wsh)
    {source : CoreFragment} {env : SatEnv} {flags : ScriptFlags} {arguments other : Witness}
    {item : StackElement} {key : PubKey} (sound : env.Sound)
    (version : env.txCtx.sigVersion = .witnessV0) (modeled : ModeledContextFlags .p2wsh flags)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (disjoint : LocalPreimageSignatureDisjoint sane.checked.fragment env flags arguments)
    (mem : item ∈ other) (keyMem : key ∈ sane.checked.fragment.keys)
    (keysIn : ∀ k ∈ source.keys, k ∈ sane.checked.fragment.keys)
    (locksIn : ∀ l ∈ source.hashLocks, l ∈ sane.checked.fragment.hashLocks)
    (material : TapscriptWitness.Material source env item)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true) :
    key ∈ source.keys ∧ env.signatureFor key = some item := by
  rcases checked_source_material sane sound version modeled third mem keyMem keysIn material checked with
    selected | ⟨lock, hl, lookup⟩
  · exact selected
  · have published := third.2.2.1 item mem lock (locksIn lock hl) (sound.preimageMatches lookup)
    exact (disjoint item published (third.singleton_of_mem mem) ⟨lock, locksIn lock hl, lookup⟩
      key keyMem checked).elim

/-- On a generated P2WSH satisfaction, agreement on disclosed preimages is necessary
    and sufficient for recovering every eligible, successfully checked signature slot. -/
theorem signatureAgreement_iff_of_satisfy (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {arguments : Witness}
    (sound : env.Sound) (version : env.txCtx.sigVersion = .witnessV0)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfy sane.checked.fragment env = some arguments) :
    PublishedPreimageSignatureAgreement sane.checked.fragment env flags arguments ↔
      ∀ other, ThirdPartyWitness sane.checked.fragment env.txCtx arguments other →
        ∀ item ∈ other, ∀ key ∈ sane.checked.fragment.keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true →
          env.signatureFor key = some item := by
  constructor
  · intro agree other third item mem key keyMem checked
    have valid := P2WSHNonMalleabilitySubcase.verifySigFor_of_checkSigWithEncoding_true checked
    have published := third.2.1 item mem key keyMem valid
    have material := TapscriptWitness.satisfy_material generated item published
    rcases checked_source_material sane sound version modeled third mem keyMem
      (fun _ h => h) material checked with ⟨_, selected⟩ | preimage
    · exact selected
    · exact agree item published (third.singleton_of_mem mem) preimage key keyMem checked
  · intro recover item _ eligible _ key keyMem checked
    exact recover [item] eligible item (.head _) key keyMem checked

theorem publishedPreimageSignatureAgreement_iff (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {arguments : Witness}
    (sound : env.Sound) (version : env.txCtx.sigVersion = .witnessV0)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfyFinal sane.checked.fragment env = some arguments) :
    PublishedPreimageSignatureAgreement sane.checked.fragment env flags arguments ↔
      ∀ other, ThirdPartyWitness sane.checked.fragment env.txCtx arguments other →
        ∀ item ∈ other, ∀ key ∈ sane.checked.fragment.keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true →
          env.signatureFor key = some item :=
  signatureAgreement_iff_of_satisfy sane sound version modeled (satisfyFinal_some_satisfy generated)

/-- A matching legacy CHECKMULTISIG pair passes the same checked-signature boundary
    as CHECKSIG for a compressed key of the sane fragment. -/
theorem checked_of_multisig_match (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {key : PubKey} {sig : StackElement}
    (version : env.txCtx.sigVersion = .witnessV0) (modeled : ModeledContextFlags .p2wsh flags)
    (member : key ∈ sane.checked.fragment.keys) (encoded : checkECDSAEncoding flags sig key.bytes = .ok ())
    (matchSig : checkSig sig key.bytes env.txCtx.sigHash = true) :
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true := by
  apply checkSigWithEncoding_true
  · have empty := checkSigEncodingFor_empty_of_modeled
      (wellFormed_keys _ sane.checked.wellFormed key member) version modeled
    rw [version] at empty ⊢
    cases pub : checkPubKeyEncoding flags key.bytes with
    | error err => simp [checkSigEncodingFor, pub, bind, Except.bind] at empty
    | ok result =>
        cases result
        simpa only [checkSigEncodingFor, encoded, checkECDSAEncoding_empty, pub] using empty
  · rwa [P2WSHNonMalleabilitySubcase.verifySigFor_witnessV0 _ _ version]

end LeanMiniscript.Extraction.P2WSHRecovery
