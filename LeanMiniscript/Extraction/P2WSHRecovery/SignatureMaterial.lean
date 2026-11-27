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

/-- On a generated P2WSH satisfaction, agreement on disclosed preimages is necessary
    and sufficient for recovering every eligible, successfully checked signature slot. -/
theorem publishedPreimageSignatureAgreement_iff (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {arguments : Witness}
    (sound : env.Sound) (version : env.txCtx.sigVersion = .witnessV0)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfyFinal sane.checked.fragment env = some arguments) :
    PublishedPreimageSignatureAgreement sane.checked.fragment env flags arguments ↔
      ∀ other, ThirdPartyWitness sane.checked.fragment env.txCtx arguments other →
        ∀ item ∈ other, ∀ key ∈ sane.checked.fragment.keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx item key.bytes = .ok true →
          env.signatureFor key = some item := by
  constructor
  · intro agree other third item mem key keyMem checked
    have valid := P2WSHNonMalleabilitySubcase.verifySigFor_of_checkSigWithEncoding_true checked
    have published := third.2.1 item mem key keyMem valid
    have material := TapscriptWitness.satisfy_material (satisfyFinal_some_satisfy generated) item published
    have strict := modeled.2.2.2.2
    rcases material with rfl | rfl | ⟨source, sourceMem, rfl⟩ | ⟨source, sourceMem, selected⟩ | preimage
    · rw [sound.emptySignatureInvalid] at valid
      contradiction
    · exact (P2WSHNonMalleabilityKeyChoice.checked_signature_ne_true strict version checked rfl).elim
    · have encoded := P2WSHNonMalleabilityInversion.encoding_of_checkSigWithEncoding_ok checked
      rw [version] at encoded
      have rekeyed := checkSigEncodingFor_witnessV0_rekey
        (wellFormed_keys _ sane.checked.wellFormed source sourceMem) encoded
      exact (P2WSHNonMalleabilityInversion.signature_ne_pubkey_of_strict
        (ctx := env.txCtx) strict version (version ▸ rekeyed) rfl).elim
    · by_cases same : key = source
      · exact same ▸ selected
      · exact (third.1 item mem key keyMem source sourceMem same valid
          (sound.signatureValid selected)).elim
    · exact agree item published (third.singleton_of_mem mem) preimage key keyMem checked
  · intro recover item _ eligible _ key keyMem checked
    exact recover [item] eligible item (.head _) key keyMem checked

end LeanMiniscript.Extraction.P2WSHRecovery
