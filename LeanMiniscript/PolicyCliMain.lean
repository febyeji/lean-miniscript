import LeanMiniscript.Policy.Cli
import LeanMiniscript.CliSupport

open LeanMiniscript.Policy.Cli

def main (args : List String) : IO UInt32 :=
  LeanMiniscript.CliSupport.runMain usage parseArgs (fun command => pure (execute command)) args
