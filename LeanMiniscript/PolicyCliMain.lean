import LeanMiniscript.Policy.Text

namespace LeanMiniscript.PolicyCliMain

open LeanMiniscript.Policy

private def usage : String :=
  "usage: lake exe policy_cli -- POLICY_TEXT"

private def run (source : String) : IO UInt32 := do
  match parsePolicyHex source with
  | .error error =>
      IO.eprintln s!"parse error: {repr error}"
      return 2
  | .ok policy =>
      IO.println s!"ast: {repr policy}"
      IO.println s!"canonical: {prettyPolicy policy}"
      return 0

end LeanMiniscript.PolicyCliMain

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--", source] | [source] =>
      LeanMiniscript.PolicyCliMain.run source
  | _ =>
      IO.eprintln LeanMiniscript.PolicyCliMain.usage
      return 2
