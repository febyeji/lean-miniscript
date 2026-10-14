import LeanMiniscript.Extraction.RefInterp

namespace LeanMiniscript.Extraction.ScriptCliMain

open LeanMiniscript.Script

private def usage : String :=
  "usage: lake exe script_cli -- SCRIPT_SOURCE"

private def run (source : String) : IO UInt32 := do
  match parseCoreScriptSource source with
  | .error error =>
      IO.eprintln s!"parse error: {repr error}"
      return 2
  | .ok script =>
      let oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
      let flags : ScriptFlags := {}
      let context : TxContext :=
        { version := 2, locktime := 0, sequence := 0xffffffff
          sigHash := ByteArray.empty, sigVersion := .base }
      IO.println s!"script: {toAssembly script}"
      IO.println s!"result: {repr (execScript oracle script [] flags context)}"
      return 0

end LeanMiniscript.Extraction.ScriptCliMain

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--", source] | [source] =>
      LeanMiniscript.Extraction.ScriptCliMain.run source
  | _ =>
      IO.eprintln LeanMiniscript.Extraction.ScriptCliMain.usage
      return 2
