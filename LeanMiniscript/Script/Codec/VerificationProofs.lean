import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Extraction.Taproot

/-!
Codec preservation at the final Tapscript acceptance and committed transaction
verification boundaries. The witness and transaction are fixed throughout;
the claims cover the modeled opcode subset and existing verification checks.
-/

namespace LeanMiniscript.Miniscript

open Script

theorem checkTapscriptAcceptance_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (witness : TapscriptWitness)
    (flags : ScriptFlags) (ctx : TxContext) :
    checkTapscriptAcceptance oracle (normalizeSerializedScript script) witness flags ctx =
      checkTapscriptAcceptance oracle script witness flags ctx := by
  simp only [checkTapscriptAcceptance, evaluateTapscript_normalizeSerializedScript]

theorem tapscriptAccepts_normalizeSerializedScript
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    TapscriptAccepts (normalizeSerializedScript script) witness flags ctx ↔
      TapscriptAccepts script witness flags ctx := by
  simp only [TapscriptAccepts, evaluateTapscript_normalizeSerializedScript]

theorem tapscriptDissatisfies_normalizeSerializedScript
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    TapscriptDissatisfies (normalizeSerializedScript script) witness flags ctx ↔
      TapscriptDissatisfies script witness flags ctx := by
  simp only [TapscriptDissatisfies, evaluateTapscript_normalizeSerializedScript]

theorem checkTapscriptAcceptance_deserializeScript_serializeScript
    (oracle : CryptoOracle) (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    (deserializeScript encoded).map (fun decoded =>
        checkTapscriptAcceptance oracle decoded witness flags ctx) =
      .ok (checkTapscriptAcceptance oracle script witness flags ctx) := by
  rw [deserializeScript_serializeScript script encoded serialized]
  simp only [Except.map, checkTapscriptAcceptance_normalizeSerializedScript]

end LeanMiniscript.Miniscript

namespace LeanMiniscript.Extraction

open Script

/-- Preparation uses the same witness and transaction, and normalized execution
    preserves both setup errors and the full weighted execution result. -/
theorem execCommittedTapscriptTransaction_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (fullWitness : List ByteArray)
    (flags : ScriptFlags) (transaction : Bitcoin.Transaction)
    (spentOutputs : Array Bitcoin.TxOutput) (inputIndex : Nat) :
    execCommittedTapscriptTransaction oracle (normalizeSerializedScript script)
        fullWitness flags transaction spentOutputs inputIndex =
      execCommittedTapscriptTransaction oracle script
        fullWitness flags transaction spentOutputs inputIndex := by
  simp only [execCommittedTapscriptTransaction, evaluateTapscript_normalizeSerializedScript]

/-- Normalization preserves commitment/setup failures, execution/acceptance
    failures and the remaining signature budget returned on success. -/
theorem verifyCommittedTapscriptTransaction_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (fullWitness : List ByteArray)
    (flags : ScriptFlags) (transaction : Bitcoin.Transaction)
    (spentOutputs : Array Bitcoin.TxOutput) (inputIndex : Nat) :
    verifyCommittedTapscriptTransaction oracle (normalizeSerializedScript script)
        fullWitness flags transaction spentOutputs inputIndex =
      verifyCommittedTapscriptTransaction oracle script
        fullWitness flags transaction spentOutputs inputIndex := by
  simp only [verifyCommittedTapscriptTransaction,
    Miniscript.checkTapscriptAcceptance_normalizeSerializedScript]

theorem verifyCommittedTapscriptTransaction_deserializeScript_serializeScript
    (oracle : CryptoOracle) (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Bitcoin.Transaction) (spentOutputs : Array Bitcoin.TxOutput)
    (inputIndex : Nat) :
    (deserializeScript encoded).map (fun decoded =>
        verifyCommittedTapscriptTransaction oracle decoded
          fullWitness flags transaction spentOutputs inputIndex) =
      .ok (verifyCommittedTapscriptTransaction oracle script
        fullWitness flags transaction spentOutputs inputIndex) := by
  rw [deserializeScript_serializeScript script encoded serialized]
  simp only [Except.map, verifyCommittedTapscriptTransaction_normalizeSerializedScript]

end LeanMiniscript.Extraction
