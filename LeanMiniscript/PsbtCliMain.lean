import LeanMiniscript.Psbt.Cli

open LeanMiniscript.Psbt.Cli

private def readSource (source : String) : IO String := do
  if source == "-" then (← IO.getStdin).readToEnd else pure source

private def readCommand : Command → IO Command
  | .inspect encoding source => return .inspect encoding (← readSource source)
  | .finalize encoding source descriptors =>
      return .finalize encoding (← readSource source) descriptors
  | .extract encoding source => return .extract encoding (← readSource source)
  | .help => pure .help

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error error =>
    IO.eprintln s!"{error}\n{usage}"
    return 2
  | .ok command =>
    try
      match execute (← readCommand command) with
      | .error error => IO.eprintln error; return 2
      | .ok output => IO.println output; return 0
    catch error =>
      IO.eprintln s!"input error: {error}"
      return 2
