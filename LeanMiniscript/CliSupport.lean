/-!
# CLI support

Shared shell pieces for the executable front-ends: Lake's optional `--`
argument separator and the parse-then-execute exit-code convention.
-/

namespace LeanMiniscript.CliSupport

/-- Drop Lake's optional leading `--` argument separator. -/
def stripSeparator : List String → List String
  | "--" :: rest => rest
  | args => args

/-- Shared CLI shell: argument errors print the message and usage to stderr
    and exit 2; execution errors print to stderr and exit 2; successful
    output goes to stdout with exit 0. -/
def runMain {α : Type} (usage : String) (parse : List String → Except String α)
    (run : α → IO (Except String String)) (args : List String) : IO UInt32 := do
  match parse args with
  | .error error =>
      IO.eprintln s!"{error}\n{usage}"
      return 2
  | .ok command =>
      match ← run command with
      | .error error =>
          IO.eprintln error
          return 2
      | .ok output =>
          IO.println output
          return 0

end LeanMiniscript.CliSupport
