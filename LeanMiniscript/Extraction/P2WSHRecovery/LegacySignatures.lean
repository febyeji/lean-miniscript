import LeanMiniscript.Extraction.P2WSHRecovery.SignatureMaterial

/-! Signature lookup in a successful legacy multisignature match, in execution order. -/

namespace LeanMiniscript.Extraction.P2WSHRecovery

open LeanMiniscript.Script LeanMiniscript.Miniscript P2WSHNonMalleabilityInversion

private theorem matched_frame {P : StackElement → PubKey → Prop} {flags : ScriptFlags}
    {hash : ByteArray} (keys : List PubKey) (sigs : Stack)
    (pair : ∀ sig ∈ sigs, ∀ key ∈ keys, checkECDSAEncoding flags sig key.bytes = .ok () →
      checkSig sig key.bytes hash = true → P sig key)
    (matched : checkMultiSigWithEncoding checkSig flags hash sigs (keys.map PubKey.bytes) = .ok true) :
    ∃ used, used.Sublist keys ∧ SignatureFrame P sigs used := by
  induction keys generalizing sigs with
  | nil =>
      cases sigs with
      | nil => exact ⟨[], .slnil, .nil⟩
      | cons => simp [checkMultiSigWithEncoding] at matched
  | cons key keys ih =>
      cases sigs with
      | nil => exact ⟨[], List.nil_sublist _, .nil⟩
      | cons sig sigs =>
          cases encoded : checkECDSAEncoding flags sig key.bytes with
          | error err =>
              simp [checkMultiSigWithEncoding, encoded, bind, Except.bind] at matched
          | ok result =>
              cases result
              cases verified : checkSig sig key.bytes hash with
              | false =>
                  simp only [List.map_cons, checkMultiSigWithEncoding, encoded, verified, Bool.false_eq_true,
                    if_false, bind, Except.bind] at matched
                  split at matched
                  · contradiction
                  · obtain ⟨used, sub, frame⟩ := ih _ (fun s hs k hk =>
                      pair s hs k (List.mem_cons_of_mem _ hk)) matched
                    exact ⟨used, sub.cons _, frame⟩
              | true =>
                  simp only [List.map_cons, checkMultiSigWithEncoding, encoded, verified, if_true,
                    bind, Except.bind] at matched
                  split at matched
                  · contradiction
                  · obtain ⟨used, sub, frame⟩ := ih _ (fun s hs k hk =>
                      pair s (List.mem_cons_of_mem _ hs) k (List.mem_cons_of_mem _ hk)) matched
                    exact ⟨key :: used, sub.cons_cons _, .cons (pair sig (.head _) key (.head _)
                      encoded verified) frame⟩

/-- Each consumed signature is the selected lookup for its matched key. The keys form
    a subsequence of the CHECKMULTISIG input; skipped keys consume no signature. -/
theorem multisig_lookup_frame_of_satisfy (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {arguments other : Witness} {sigs : Stack}
    {keys : List PubKey} (sound : env.Sound) (version : env.txCtx.sigVersion = .witnessV0)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfy sane.checked.fragment env = some arguments)
    (agreement : PublishedPreimageSignatureAgreement sane.checked.fragment env flags arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (consumed : ∀ sig ∈ sigs, sig ∈ other) (members : ∀ key ∈ keys, key ∈ sane.checked.fragment.keys)
    (matched : checkMultiSigWithEncoding checkSig flags env.txCtx.sigHash sigs
      (keys.map PubKey.bytes) = .ok true) :
    ∃ used, used.Sublist keys ∧ SignatureFrame (fun sig key => env.signatureFor key = some sig) sigs used := by
  apply matched_frame keys sigs _ matched
  intro sig hs key hk encoded verified
  exact (signatureAgreement_iff_of_satisfy sane sound version modeled generated).mp agreement
    other third sig (consumed sig hs) key (members key hk)
    (checked_of_multisig_match sane version modeled (members key hk) encoded verified)

theorem multisig_lookup_frame (sane : SaneFragment .p2wsh)
    {env : SatEnv} {flags : ScriptFlags} {arguments other : Witness} {sigs : Stack}
    {keys : List PubKey} (sound : env.Sound) (version : env.txCtx.sigVersion = .witnessV0)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (agreement : PublishedPreimageSignatureAgreement sane.checked.fragment env flags arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (consumed : ∀ sig ∈ sigs, sig ∈ other) (members : ∀ key ∈ keys, key ∈ sane.checked.fragment.keys)
    (matched : checkMultiSigWithEncoding checkSig flags env.txCtx.sigHash sigs
      (keys.map PubKey.bytes) = .ok true) :
    ∃ used, used.Sublist keys ∧ SignatureFrame (fun sig key => env.signatureFor key = some sig) sigs used :=
  multisig_lookup_frame_of_satisfy sane sound version modeled (satisfyFinal_some_satisfy generated)
    agreement third consumed members matched

end LeanMiniscript.Extraction.P2WSHRecovery
