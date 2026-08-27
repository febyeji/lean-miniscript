import LeanMiniscript.Script.Evaluator

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

-- TODO: Map modeled failures to exact Bitcoin Core Script error tags
-- TODO: Extend differential execution to witness, P2SH, and signature rows
-- TODO: CLI interface for standalone execution

end LeanMiniscript.Extraction
