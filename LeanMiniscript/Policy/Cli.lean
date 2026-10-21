import LeanMiniscript.Policy.Compiler
import LeanMiniscript.Miniscript.CompileConcreteChecked

namespace LeanMiniscript.Policy.Cli

open LeanMiniscript.Miniscript LeanMiniscript.Script LeanMiniscript.Properties

def usage : String :=
  "usage: lake exe policy_cli -- [parse] POLICY_TEXT\n" ++
  "       lake exe policy_cli -- compile [--context p2wsh|tapscript] POLICY_TEXT\n" ++
  "       lake exe policy_cli -- --help\n" ++
  "The compile command defaults to p2wsh."

inductive Command where
  | parse (source : String)
  | compile (context : ScriptContext) (source : String)
  | help
  deriving Repr, DecidableEq

/-- Preserve the original single-policy invocation and accept Lake's optional
argument separator. Compilation has an explicit context override. -/
def parseArgs (args : List String) : Except String Command :=
  let args := match args with | "--" :: rest => rest | _ => args
  match args with
  | ["--help"] | ["-h"] => .ok .help
  | ["compile", "--context", "p2wsh", source] => .ok (.compile .p2wsh source)
  | ["compile", "--context", "tapscript", source] => .ok (.compile .tapscript source)
  | ["compile", "--context", context, _] =>
      .error s!"unknown context '{context}'; expected p2wsh or tapscript"
  | ["compile", source] => .ok (.compile .p2wsh source)
  | ["parse", source] => .ok (.parse source)
  | ["compile"] | ["parse"] => .error "missing policy text"
  | [source] => .ok (.parse source)
  | _ => .error "invalid arguments"

structure CompilationReport where
  context : ScriptContext
  miniscript : String
  script : ByteArray
  resources : ResourceUsage

/-- Compile through the sane policy boundary, then serialize the concrete
Script so HASH160 key pushes contain executable Bitcoin bytes. -/
def compileReport (ctx : ScriptContext) (source : String) : Except String CompilationReport := do
  let sane ← (compilePolicyHex ctx source).mapError fun
    | .parse error => s!"parse error: {repr error}"
    | .keyContext _ => "key context error: public key encoding is incompatible with the selected context"
    | .sane error => s!"compile error: {repr error}"
  let script ← (serializeScript (compileConcreteChecked sane.checked)).mapError fun error =>
    s!"serialization error: {repr error}"
  return {
    context := ctx
    miniscript := prettyCoreWith prettyPubKey sane.checked.fragment
    script
    resources := resourceUsage sane.checked.fragment }

private def metric {α : Type} [ToString α] (value : Option α) : String :=
  (value.map toString).getD "unavailable"

/-- Cost diagnostics are script bytes and static or worst-path resource
counts. Opcode charge is reported for the P2WSH context that uses it. -/
def CompilationReport.render (report : CompilationReport) : String :=
  let context := match report.context with | .p2wsh => "p2wsh" | .tapscript => "tapscript"
  let lines := [
    s!"context: {context}",
    s!"miniscript: {report.miniscript}",
    s!"script_hex: {byteArrayHex report.script}",
    s!"script_bytes: {report.script.size}",
    s!"static_ops: {report.resources.staticOps}",
    s!"max_initial_stack_items: {metric report.resources.satisfactionInitialStack}",
    s!"max_execution_stack_items: {metric report.resources.satisfactionExecutionStack}"]
  let lines := match report.context with
    | .p2wsh => lines ++ [s!"max_op_charge: {metric report.resources.satisfactionOps}"]
    | .tapscript => lines
  String.intercalate "\n" lines

def execute : Command → Except String String
  | .help => .ok usage
  | .parse source => do
      let policy ← (parsePolicyHex source).mapError (fun error => s!"parse error: {repr error}")
      return s!"ast: {repr policy}\ncanonical: {prettyPolicy policy}"
  | .compile context source => return (← compileReport context source).render

end LeanMiniscript.Policy.Cli
