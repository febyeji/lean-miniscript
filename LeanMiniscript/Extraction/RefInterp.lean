import LeanMiniscript.Script.ValidationWeight

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- Execute a complete script from an empty alternate stack.

    Signature verification is supplied through `CryptoOracle`; the
    `CryptoOracle.pureLeanHashes` constructor provides executable SHA-256,
    HASH256, RIPEMD-160, and HASH160. -/
def execScript (oracle : CryptoOracle) (script : Script)
    (initialStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    ExecResult :=
  evaluate oracle script initialStack [] flags ctx

/-- Execute a Tapscript script-path witness with validation-weight accounting.
    Callers validate the Taproot/control-block commitment separately. -/
def execTapscript (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    WeightedResult :=
  evaluateTapscript oracle script witness flags ctx

/-- Transaction-backed Tapscript execution: hashes are calculated per
    signature, and timelocks and sighashes use the same selected input. -/
def execTapscriptTransaction (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags)
    (transaction : Bitcoin.Transaction) (spentOutputs : Array Bitcoin.TxOutput)
    (inputIndex : Nat) : WeightedResult :=
  match TxContext.fromTaproot { transaction := transaction, spentOutputs := spentOutputs, inputIndex := inputIndex } with
  | .error _ => .failure .schnorrSigHashType
  | .ok ctx => evaluateTapscript oracle script witness flags ctx

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

-- TODO: Extend differential execution to push-encoding, witness, and P2SH rows
-- TODO: Add a secp256k1 oracle for signature-result rows
-- TODO: CLI interface for standalone Script-source execution

end LeanMiniscript.Extraction
