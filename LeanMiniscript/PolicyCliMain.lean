import LeanMiniscript.Policy.Cli

open LeanMiniscript.Policy.Cli

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error error =>
      IO.eprintln s!"{error}\n{usage}"
      return 2
  | .ok command =>
      match execute command with
      | .error error =>
          IO.eprintln error
          return 2
      | .ok output =>
          IO.println output
          return 0
