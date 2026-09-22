import LeanMiniscript.Extraction.TaprootBytes
import LeanMiniscript.Script.Codec.VerificationProofs

namespace LeanMiniscript.Extraction

open Script Bitcoin

/-- Every successfully serialized AST is accepted by the canonical decoder,
    which returns the codec's normalized representative. -/
theorem decodeCanonicalTapscript_serializeScript
    (script : Script) (bytes : ByteArray)
    (serialized : serializeScript script = .ok bytes) :
    decodeCanonicalTapscript bytes = .ok (normalizeSerializedScript script) := by
  simp [decodeCanonicalTapscript, deserializeScript_serializeScript script bytes serialized,
    serializeScript_normalizeSerializedScript, serialized, Except.mapError, bind, Except.bind]
  rfl

/-- Decoding success retains both the original decoder result and exact
    canonical byte binding. -/
theorem decodeCanonicalTapscript_sound
    {bytes : ByteArray} {script : Script}
    (decoded : decodeCanonicalTapscript bytes = .ok script) :
    deserializeScript bytes = .ok script ∧ serializeScript script = .ok bytes := by
  unfold decodeCanonicalTapscript at decoded
  cases parsed : deserializeScript bytes with
  | error error => simp [parsed, Except.mapError, bind, Except.bind] at decoded
  | ok parsedScript =>
      cases encoded : serializeScript parsedScript with
      | error error => simp [parsed, encoded, Except.mapError, bind, Except.bind] at decoded
      | ok encodedBytes =>
          by_cases equal : encodedBytes.data = bytes.data
          · have same : encodedBytes = bytes := by
              cases encodedBytes
              cases bytes
              cases equal
              rfl
            simp [parsed, encoded, Except.mapError, bind, Except.bind, equal] at decoded
            cases decoded
            exact ⟨rfl, same ▸ encoded⟩
          · simp [parsed, encoded, Except.mapError, bind, Except.bind, equal] at decoded

/-- Commitment and setup failures precede all byte and execution checks. -/
theorem verifyCanonicalTapscriptTransaction_setup_error
    (oracle : CryptoOracle) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat)
    {error : TaprootScriptPathError}
    (preparation : prepareCommittedTapscriptTransaction
      fullWitness transaction spentOutputs inputIndex = .error error) :
    verifyCanonicalTapscriptTransaction oracle fullWitness flags transaction spentOutputs inputIndex =
      .error (.setup error) := by
  simp [verifyCanonicalTapscriptTransaction, preparation, Except.mapError, bind, Except.bind]

/-- For a successfully prepared witness carrying an AST's canonical bytes,
    wire verification preserves its complete AST-verification result, including
    execution/acceptance failures and the remaining budget. No oracle agreement
    hypothesis is needed because both sides use the same arbitrary oracle. -/
theorem verifyCanonicalTapscriptTransaction_eq_ast
    (oracle : CryptoOracle) (script : Script) (fullWitness : List ByteArray)
    (flags : ScriptFlags) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat)
    {prepared : PreparedTapscript}
    (preparation : prepareCommittedTapscriptTransaction
      fullWitness transaction spentOutputs inputIndex = .ok prepared)
    (serialized : serializeScript script = .ok prepared.witness.scriptBytes) :
    verifyCanonicalTapscriptTransaction oracle fullWitness flags transaction spentOutputs inputIndex =
      (verifyCommittedTapscriptTransaction oracle script fullWitness flags
        transaction spentOutputs inputIndex).mapError
          CanonicalTapscriptVerificationError.ofVerification := by
  simp [verifyCanonicalTapscriptTransaction, verifyCommittedTapscriptTransaction,
    preparation, Except.mapError, bind, Except.bind, decodeCanonicalTapscript_serializeScript script _ serialized,
    Miniscript.checkTapscriptAcceptance_normalizeSerializedScript]
  cases Miniscript.checkTapscriptAcceptance oracle script prepared.witness flags prepared.context <;>
    rfl

/-- The byte entry point accepts exactly the modeled accepted witnesses under
    the existing cryptographic refinement and canonical-byte hypotheses. -/
theorem verifyCanonicalTapscriptTransaction_iff
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat)
    {prepared : PreparedTapscript}
    (preparation : prepareCommittedTapscriptTransaction
      fullWitness transaction spentOutputs inputIndex = .ok prepared)
    (serialized : serializeScript script = .ok prepared.witness.scriptBytes) :
    (∃ weight, verifyCanonicalTapscriptTransaction oracle fullWitness flags
      transaction spentOutputs inputIndex = .ok weight) ↔
      Miniscript.TapscriptAccepts script prepared.witness flags prepared.context := by
  rw [verifyCanonicalTapscriptTransaction_eq_ast oracle script fullWitness flags
    transaction spentOutputs inputIndex preparation serialized]
  rw [← verifyCommittedTapscriptTransaction_iff agreement script fullWitness flags
    transaction spentOutputs inputIndex preparation]
  cases verifyCommittedTapscriptTransaction oracle script fullWitness flags
    transaction spentOutputs inputIndex <;> simp [Except.mapError]

end LeanMiniscript.Extraction
