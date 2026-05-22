import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- Execute a single opcode. Returns the new state or an error. -/
def execOpcode (_state : ExecState) (op : Opcode) : Except String ExecState :=
  -- TODO: Implement each opcode
  .error s!"unimplemented opcode: {repr op}"

/-- Execute a complete script. -/
def execScript (_script : Script) (_initialStack : Stack)
    (_flags : ScriptFlags) (_ctx : TxContext) : Except String Stack :=
  -- TODO: Main interpreter loop
  .error "unimplemented"

-- TODO: JSON parser for Bitcoin Core's script_tests.json format
-- TODO: Differential testing harness
-- TODO: CLI interface for standalone execution

end LeanMiniscript.Extraction
