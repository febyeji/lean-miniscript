import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Script.TapscriptExecutionProofs

/-! Oracle refinement for transaction-backed Script entry points. -/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- Transaction-backed execution has the same result under every oracle
    refining the abstract cryptographic boundary. -/
theorem execTapscriptTransaction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags)
    (transaction : Bitcoin.Transaction) (spentOutputs : Array Bitcoin.TxOutput)
    (inputIndex : Nat) :
    execTapscriptTransaction oracle script witness flags transaction spentOutputs inputIndex =
      execTapscriptTransaction CryptoOracle.model script witness flags transaction spentOutputs inputIndex := by
  unfold execTapscriptTransaction
  split
  · rfl
  · exact evaluateTapscript_eq_model agreement script witness flags _

end LeanMiniscript.Extraction
