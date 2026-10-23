import LeanMiniscript.Psbt.Cli
import LeanMiniscript.CliSupport

open LeanMiniscript.Psbt.Cli

private def readSource (source : String) : IO String := do
  if source == "-" then (← IO.getStdin).readToEnd else pure source

private def readCommand : Command → IO Command
  | .inspect encoding source => return .inspect encoding (← readSource source)
  | .finalize encoding source descriptors =>
      return .finalize encoding (← readSource source) descriptors
  | .extract encoding source => return .extract encoding (← readSource source)
  | .help => pure .help

private def runCommand (command : Command) : IO (Except String String) := do
  try
    return execute (← readCommand command)
  catch error =>
    return .error s!"input error: {error}"

def main (args : List String) : IO UInt32 :=
  LeanMiniscript.CliSupport.runMain usage parseArgs runCommand args
