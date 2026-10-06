import LeanMiniscript.Extraction.Taproot
import LeanMiniscript.Extraction.RefInterpProofs
import LeanMiniscript.Miniscript.AcceptanceProofs

/-! Oracle refinement and final acceptance after Taproot commitment preparation. -/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin

/-- Deterministic commitment/setup checks preserve the evaluator's existing
conditional oracle-refinement guarantee. This does not prove curve correctness. -/
theorem execCommittedTapscriptTransaction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    execCommittedTapscriptTransaction oracle script fullWitness flags transaction spentOutputs inputIndex =
      execCommittedTapscriptTransaction CryptoOracle.model script fullWitness flags transaction spentOutputs inputIndex := by
  simp only [execCommittedTapscriptTransaction, evaluateTapscript_eq_model agreement]


theorem verifyCommittedTapscriptTransaction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    verifyCommittedTapscriptTransaction oracle script fullWitness flags transaction spentOutputs inputIndex =
      verifyCommittedTapscriptTransaction CryptoOracle.model script fullWitness flags transaction spentOutputs inputIndex := by
  simp only [verifyCommittedTapscriptTransaction, Miniscript.checkTapscriptAcceptance,
    evaluateTapscript_eq_model agreement]

/-- After successful commitment preparation, the public verification entry
    accepts exactly the witnesses satisfying the modeled acceptance predicate.
    A raw PreparedTapscript value alone is not evidence of preparation. -/
theorem verifyCommittedTapscriptTransaction_iff
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat)
    {prepared : PreparedTapscript}
    (preparation : prepareCommittedTapscriptTransaction fullWitness transaction spentOutputs inputIndex =
      .ok prepared) :
    (∃ weight, verifyCommittedTapscriptTransaction oracle script fullWitness flags
      transaction spentOutputs inputIndex = .ok weight) ↔
      Miniscript.TapscriptAccepts script prepared.witness flags prepared.context := by
  rw [← Miniscript.checkTapscriptAcceptance_iff agreement]
  simp only [verifyCommittedTapscriptTransaction, preparation, Except.mapError, bind, Except.bind]
  cases Miniscript.checkTapscriptAcceptance oracle script prepared.witness flags prepared.context <;> simp

end LeanMiniscript.Extraction
