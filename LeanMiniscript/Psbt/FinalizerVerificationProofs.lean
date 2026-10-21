import LeanMiniscript.Psbt.FinalizerProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Script

/-- Preparation uses the compiled descriptor, selected UTXO, and unsigned
transaction read from this PSBT. -/
theorem prepareFinalization_spec {decoded : DecodedPsbt} {index : Nat}
    {descriptor : OutputDescriptor} {prepared : FinalizationContext}
    (result : prepareFinalization decoded index descriptor = .ok prepared) :
    compileOutputDescriptor descriptor = .ok prepared.compiled ∧
      decoded.spentOutput index = .ok prepared.spent ∧
      decoded.unsignedTransaction = .ok prepared.transaction := by
  unfold prepareFinalization compileDescriptor liftPsbt at result
  cases hc : compileOutputDescriptor descriptor <;>
    simp only [hc, Except.mapError, bind, Except.bind] at result
  · contradiction
  cases hs : decoded.spentOutput index <;>
    simp only [hs] at result
  · contradiction
  cases ht : decoded.unsignedTransaction <;>
    simp only [ht, pure, Except.pure] at result
  · contradiction
  cases result
  exact ⟨rfl, rfl, rfl⟩

/-- A legacy final input commits to the descriptor output and passes the
transaction-backed script-pair verifier with an empty witness. -/
def LegacyFinalVerified (config : FinalizerConfig) (decoded : DecodedPsbt)
    (index : Nat) (descriptor : OutputDescriptor) (final : FinalInput) : Prop :=
  ∃ prepared, prepareFinalization decoded index descriptor = .ok prepared ∧
    prepared.spent.scriptPubKey = prepared.compiled.scriptPubKey ∧
    final.witness = [] ∧
    verifyLegacyFinal config prepared.transaction index prepared.compiled final = .ok ()

theorem finalizeLegacySingle_verified {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {input : InputFields} {descriptor : OutputDescriptor} {key : PubKey}
    {pkh : Bool} {final : FinalInput}
    (result : finalizeLegacySingle config decoded index input descriptor key pkh = .ok final) :
    LegacyFinalVerified config decoded index descriptor final := by
  unfold finalizeLegacySingle at result
  cases hp : prepareFinalization decoded index descriptor with
  | error error => simp [hp, bind, Except.bind] at result
  | ok prepared =>
    rcases prepared with ⟨compiled, spent, tx⟩
    simp only [hp, bind, Except.bind] at result
    by_cases agrees : spent.scriptPubKey = compiled.scriptPubKey
    · simp only [checkFinalizerOutput, agrees, ne_eq, not_true_eq_false, if_false,
        pure, Except.pure] at result
      refine ⟨⟨compiled, spent, tx⟩, hp, agrees, ?_⟩
      repeat' (split at result <;> try simp_all [throw, throwThe, MonadExceptOf.throw])
      all_goals cases result; rfl
    · simp [checkFinalizerOutput, agrees, throw, throwThe, MonadExceptOf.throw] at result

theorem finalizeLegacyMulti_verified {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {input : InputFields} {descriptor : OutputDescriptor}
    {threshold : Nat} {keys : List PubKey} {final : FinalInput}
    (result : finalizeLegacyMulti config decoded index input descriptor threshold keys = .ok final) :
    LegacyFinalVerified config decoded index descriptor final := by
  unfold finalizeLegacyMulti at result
  cases hp : prepareFinalization decoded index descriptor with
  | error error => simp [hp, bind, Except.bind] at result
  | ok prepared =>
    rcases prepared with ⟨compiled, spent, tx⟩
    simp only [hp, bind, Except.bind] at result
    by_cases agrees : spent.scriptPubKey = compiled.scriptPubKey
    · simp only [checkFinalizerOutput, agrees, ne_eq, not_true_eq_false, if_false,
        pure, Except.pure] at result
      refine ⟨⟨compiled, spent, tx⟩, hp, agrees, ?_⟩
      repeat' (split at result <;> try simp_all [throw, throwThe, MonadExceptOf.throw])
      all_goals cases result; rfl
    · simp [checkFinalizerOutput, agrees, throw, throwThe, MonadExceptOf.throw] at result

theorem finalizeLegacyFragment_verified {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {input : InputFields} {descriptor : OutputDescriptor}
    {fragment : SurfaceFragment} {final : FinalInput}
    (result : finalizeLegacyFragment config decoded index input descriptor fragment = .ok final) :
    LegacyFinalVerified config decoded index descriptor final := by
  unfold finalizeLegacyFragment at result
  cases hp : prepareFinalization decoded index descriptor with
  | error error => simp [hp, bind, Except.bind] at result
  | ok prepared =>
    rcases prepared with ⟨compiled, spent, tx⟩
    simp only [hp, bind, Except.bind] at result
    by_cases agrees : spent.scriptPubKey = compiled.scriptPubKey
    · simp only [checkFinalizerOutput, agrees, ne_eq, not_true_eq_false, if_false,
        pure, Except.pure] at result
      refine ⟨⟨compiled, spent, tx⟩, hp, agrees, ?_⟩
      repeat' (split at result <;> try simp_all [throw, throwThe, MonadExceptOf.throw])
      all_goals cases result; rfl
    · cases hr : compiled.redeemScript <;>
        simp [hr, checkFinalizerOutput, agrees, throw, throwThe, MonadExceptOf.throw] at result

/-- A P2WPKH final input has the signature/key witness and the descriptor's
scriptSig, and passes verification using the selected UTXO amount. -/
def WpkhFinalVerified (config : FinalizerConfig) (decoded : DecodedPsbt)
    (index : Nat) (descriptor : OutputDescriptor) (key : PubKey) (final : FinalInput) : Prop :=
  ∃ prepared signature, prepareFinalization decoded index descriptor = .ok prepared ∧
    prepared.spent.scriptPubKey = prepared.compiled.scriptPubKey ∧
    final.witness = [signature, key.bytes] ∧
    final.scriptSig = (prepared.compiled.redeemScript.map pushData).getD ByteArray.empty ∧
    verifyWitnessV0Final config prepared.transaction index prepared.compiled final
      prepared.spent.amount = .ok ()

theorem finalizeWpkh_verified {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {input : InputFields} {descriptor : OutputDescriptor} {key : PubKey}
    {final : FinalInput}
    (result : finalizeWpkh config decoded index input descriptor key = .ok final) :
    WpkhFinalVerified config decoded index descriptor key final := by
  unfold finalizeWpkh at result
  cases hp : prepareFinalization decoded index descriptor with
  | error error => simp [hp, bind, Except.bind] at result
  | ok prepared =>
    rcases prepared with ⟨compiled, spent, tx⟩
    simp only [hp, bind, Except.bind] at result
    by_cases agrees : spent.scriptPubKey = compiled.scriptPubKey
    · simp only [checkFinalizerOutput, agrees, ne_eq, not_true_eq_false, if_false,
        pure, Except.pure] at result
      repeat' (split at result <;> try simp_all [throw, throwThe, MonadExceptOf.throw])
      rename_i signature _ _ _ verified
      cases result
      exact ⟨⟨compiled, spent, tx⟩, signature, hp, agrees, rfl, rfl, verified⟩
    · simp [checkFinalizerOutput, agrees, throw, throwThe, MonadExceptOf.throw] at result

/-- Descriptor forms finalized with legacy signature hashing. -/
def LegacyFinalDescriptor : OutputDescriptor → Prop
  | .pk _ | .pkh _ | .multi _ _ | .sh _ => True
  | _ => False

/-- Newly finalized legacy inputs carry a verified scriptSig. An input that
was already final is preserved, as specified by `finalizeInput_spec`. -/
theorem Psbt.finalizeInput_legacy_sound {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor}
    (shape : LegacyFinalDescriptor descriptor)
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    result = psbt ∨ ∃ decoded final,
      psbt.decode = .ok decoded ∧ LegacyFinalVerified config decoded index descriptor final ∧
      result = { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) } := by
  obtain ⟨decoded, input, decodes, found, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, same⟩ | ⟨final, produced, _, same⟩
  · exact .inl same
  · refine .inr ⟨decoded, final, decodes, ?_, same⟩
    obtain ⟨_, _, _, verified⟩ := finalInput_spec produced
    cases descriptor <;> simp only [LegacyFinalDescriptor] at shape
    all_goals first
      | contradiction
      | exact finalizeLegacySingle_verified verified
      | exact finalizeLegacyMulti_verified verified
      | exact finalizeLegacyFragment_verified verified

/-- Newly finalized native and nested P2WPKH inputs carry a verified
signature/key witness and the descriptor's scriptSig. -/
theorem Psbt.finalizeInput_wpkh_sound {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor} {key : PubKey}
    (shape : descriptor = .wpkh key ∨ descriptor = .shWpkh key)
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    result = psbt ∨ ∃ decoded final,
      psbt.decode = .ok decoded ∧ WpkhFinalVerified config decoded index descriptor key final ∧
      result = { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) } := by
  obtain ⟨decoded, input, decodes, found, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, same⟩ | ⟨final, produced, _, same⟩
  · exact .inl same
  · refine .inr ⟨decoded, final, decodes, ?_, same⟩
    obtain ⟨_, _, _, verified⟩ := finalInput_spec produced
    rcases shape with rfl | rfl <;> exact finalizeWpkh_verified verified

end LeanMiniscript.Psbt
