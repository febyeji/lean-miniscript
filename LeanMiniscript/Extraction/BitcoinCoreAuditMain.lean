import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction.BitcoinCoreAuditMain

private structure Config where
  path : System.FilePath
  showUnsupported : Bool := false

private def usage : String :=
  "usage: lake exe core_fixture_audit -- [--show-unsupported] SCRIPT_TESTS_JSON"

private def parseArgs : List String → Except String Config
  | "--" :: rest => parseArgs rest
  | [path] => .ok { path := path }
  | ["--show-unsupported", path] =>
      .ok { path := path, showUnsupported := true }
  | _ => .error usage

private def printMismatch (mismatch : CoreFixtureMismatch) : IO Unit := do
  IO.println s!"mismatch[{mismatch.index}]: expected={mismatch.expectedTag} actual={mismatch.actualTag}"
  IO.println s!"  scriptSig: {repr mismatch.scriptSigSource}"
  IO.println s!"  scriptPubKey: {repr mismatch.scriptPubKeySource}"

private def printUnsupported (row : CoreFixtureUnsupportedRow) : IO Unit := do
  IO.println s!"unsupported[{row.index}]: {repr row.reason}"
  IO.println s!"  scriptSig: {repr row.scriptSigSource}"
  IO.println s!"  scriptPubKey: {repr row.scriptPubKeySource}"

private def run (config : Config) : IO UInt32 := do
  let input ← IO.FS.readFile config.path
  match auditCoreScriptTests rejectingFixtureOracle input with
  | .error error =>
      IO.eprintln s!"failed to parse {config.path}: {repr error}"
      return 2
  | .ok audit =>
      IO.println s!"source={config.path}"
      let summary :=
        s!"tests={audit.testRows} compared={audit.comparedRows} " ++
        s!"matched={audit.matchedRows} mismatched={audit.mismatches.length} " ++
        s!"unsupported={audit.unsupportedRows} " ++
        s!"documentation={audit.documentationRows}"
      IO.println summary
      for (category, count) in audit.unsupportedReasonCounts do
        IO.println s!"unsupported.{category}={count}"
      for mismatch in audit.mismatches do
        printMismatch mismatch
      if config.showUnsupported then
        for row in audit.unsupported do
          printUnsupported row
      return if audit.allComparedRowsMatch then 0 else 1

end LeanMiniscript.Extraction.BitcoinCoreAuditMain

def main (args : List String) : IO UInt32 := do
  match LeanMiniscript.Extraction.BitcoinCoreAuditMain.parseArgs args with
  | .ok config => LeanMiniscript.Extraction.BitcoinCoreAuditMain.run config
  | .error message =>
      IO.eprintln message
      return 2
