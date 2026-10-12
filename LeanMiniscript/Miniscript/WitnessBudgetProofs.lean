import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs
import LeanMiniscript.Script.RuntimeCompletenessProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private theorem serializeWitness_fold_size (items : Witness) (initialBytes : ByteArray) :
    (items.foldl (fun bytes item => bytes ++ Bitcoin.serializeByteVector item) initialBytes).size =
      initialBytes.size + items.candidateCost := by
  induction items generalizing initialBytes with
  | nil => simp [Witness.candidateCost]
  | cons item items ih =>
      simp [List.foldl_cons, ih, Witness.candidateCost, Nat.add_assoc]

/-- Witness wire size includes the count prefix and every length-prefixed item. -/
theorem Witness.wireSize_eq (witness : Witness) :
    witness.wireSize = (Bitcoin.compactSize witness.length).length + witness.candidateCost := by
  unfold Witness.wireSize Bitcoin.serializeWitness
  rw [serializeWitness_fold_size]
  simp only [ByteArray.size, List.size_toArray]

/-- The payload bytes of any sublist of witness items fit in the full witness
budget, including script, control block and optional annex items. -/
theorem Witness.payloadSize_le_initialValidationWeight
    {arguments fullWitness : Witness} (included : arguments.Sublist fullWitness) :
    (arguments.map ByteArray.size).sum ≤ initialValidationWeight fullWitness := by
  have payload : ∀ items : Witness,
      (items.map ByteArray.size).sum ≤ items.candidateCost := by
    intro items
    induction items with
    | nil => simp [Witness.candidateCost]
    | cons item items ih =>
        simp only [Witness.candidateCost, List.map_cons, List.sum_cons,
          Bitcoin.serializeByteVector, ByteArray.size_append] at *
        omega
  have subset : (arguments.map ByteArray.size).sum ≤
      (fullWitness.map ByteArray.size).sum := by
    induction included <;> simp_all <;> omega
  have wire := fullWitness.wireSize_eq
  have bound := payload fullWitness
  change _ ≤ validationWeightOffset + fullWitness.wireSize
  omega

/-- A nonempty signature accepted for a 32-byte Tapscript key has enough
payload bytes to pay its 50-unit debit. Empty signatures cost zero. -/
theorem signatureValidationWeight_le_size_of_encoding
    {signature key : StackElement} {flags : ScriptFlags}
    (keySize : key.size = 32)
    (encoded : checkSigEncodingFor flags .tapscript signature key = .ok ()) :
    signatureValidationWeight signature ≤ signature.size := by
  by_cases empty : signature.size = 0
  · simp [signatureValidationWeight, empty]
  have schnorr : checkSchnorrSignatureEncoding signature = .ok () := by
    simpa [checkSigEncodingFor, keySize, empty] using encoded
  have size : signature.size = 64 ∨ signature.size = 65 := by
    by_cases is64 : signature.size = 64
    · exact Or.inl is64
    by_cases is65 : signature.size = 65
    · exact Or.inr is65
    simp [checkSchnorrSignatureEncoding, is64, is65] at schnorr
  simp only [signatureValidationWeight, empty, ↓reduceIte, validationWeightPerSigop]
  omega

/-- A signature selected by an encoding-sound Tapscript environment pays its
own debit from its witness payload. -/
theorem selectedSignature_validationWeight_le_size
    {key : PubKey} {env : SatEnv} {flags : ScriptFlags} {signature : StackElement}
    (valid : validResolvedPubKey .tapscript key)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (encodings : env.EncodingSound flags)
    (selected : env.signatureFor key = some signature) :
    signatureValidationWeight signature ≤ signature.size := by
  have encoded := encodings key signature selected
  simp only [ModeledContextVersion] at version
  rw [version] at encoded
  exact signatureValidationWeight_le_size_of_encoding valid encoded

/-- If executed signature debits are funded by distinct argument payloads,
serialization supplies the full-witness budget automatically. -/
theorem Witness.signatureWeight_le_initialValidationWeight
    {arguments fullWitness : Witness} {debit : Nat}
    (included : arguments.Sublist fullWitness)
    (funded : debit ≤ (arguments.map ByteArray.size).sum) :
    debit ≤ initialValidationWeight fullWitness :=
  Nat.le_trans funded (Witness.payloadSize_le_initialValidationWeight included)

/-- A successful observation whose debit fits the argument payload completes
with the serialized full-witness budget. The payload bound must account for
how often each signature is used; encoding validity alone does not supply it. -/
theorem runtime_complete_of_witness_funding
    {script : Script} {arguments fullWitness : Witness} {finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    {oracle : CryptoOracle}
    (agreement : oracle.RefinesModel)
    (observed : EvalResources script arguments.toInitialStack [] flags ctx
      finalStack finalAlt resources)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (peak : resources.peakStackItems ≤ maxStackSize)
    (included : arguments.Sublist fullWitness)
    (funded : resources.signatureWeight ≤ (arguments.map ByteArray.size).sum) :
    ∃ remaining,
      evaluateWithRuntimeLimits oracle script arguments.toInitialStack [] flags ctx
        (initialValidationWeight fullWitness) = .success finalStack finalAlt remaining ∧
      remaining + resources.signatureWeight = initialValidationWeight fullWitness :=
  observed.runtime_complete_exact agreement pushes peak _
    (Witness.signatureWeight_le_initialValidationWeight included funded)

end LeanMiniscript.Miniscript
