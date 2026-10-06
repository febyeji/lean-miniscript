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
    signature, and timelocks and sighashes use the same selected input. Callers
    validate the control-block commitment separately; the committed entry in
    `Extraction.Taproot` performs that check from the wire witness. -/
def execTapscriptTransaction (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags)
    (transaction : Bitcoin.Transaction) (spentOutputs : Array Bitcoin.TxOutput)
    (inputIndex : Nat) : WeightedResult :=
  match TxContext.fromTaproot { transaction := transaction, spentOutputs := spentOutputs, inputIndex := inputIndex } with
  | .error _ => .failure .schnorrSigHashType
  | .ok ctx => evaluateTapscript oracle script witness flags ctx

-- Extraction.BitcoinCoreFixtures provides concrete ECDSA and original-byte
-- execution for legacy, P2SH and witness rows in the pinned Core fixture.
-- TODO(script-cli): Add a CLI for standalone Script-source execution.

end LeanMiniscript.Extraction
