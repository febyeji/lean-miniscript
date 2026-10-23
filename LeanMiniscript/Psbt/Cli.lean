import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Miniscript.DescriptorParser
import LeanMiniscript.CliSupport

namespace LeanMiniscript.Psbt.Cli

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Script

def usage : String :=
  "usage: lake exe psbt_cli -- inspect [--encoding base64|hex] PSBT\n" ++
  "       lake exe psbt_cli -- finalize [--encoding base64|hex] PSBT INDEX=DESCRIPTOR...\n" ++
  "       lake exe psbt_cli -- extract [--encoding base64|hex] PSBT\n" ++
  "       lake exe psbt_cli -- --help\n" ++
  "Input defaults to Base64; use - to read PSBT text from stdin.\n" ++
  "finalize prints Base64 PSBT; extract prints transaction hex.\n" ++
  "Unspecified inputs are preserved. Descriptors must have resolved keys."

inductive Encoding where
  | base64
  | hex
  deriving Repr, DecidableEq

inductive Command where
  | inspect (encoding : Encoding) (source : String)
  | finalize (encoding : Encoding) (source : String) (descriptors : List (Nat × String))
  | extract (encoding : Encoding) (source : String)
  | help
  deriving Repr, DecidableEq

private def parseBinding (binding : String) : Except String (Nat × String) := do
  match binding.splitOn "=" with
  | [index, descriptor] =>
    let some index := index.toNat? | throw s!"invalid input index in '{binding}'"
    if descriptor.isEmpty then throw s!"input {index}: missing descriptor"
    return (index, descriptor)
  | _ => throw s!"expected INDEX=DESCRIPTOR, got '{binding}'"

private def parseCommand (command : String) (encoding : Encoding) (args : List String) :
    Except String Command := do
  match command, args with
  | "inspect", [source] => return .inspect encoding source
  | "extract", [source] => return .extract encoding source
  | "finalize", source :: bindings =>
    if bindings.isEmpty then throw "finalize requires at least one INDEX=DESCRIPTOR"
    return .finalize encoding source (← bindings.mapM parseBinding)
  | "inspect", [] | "extract", [] | "finalize", [] => throw "missing PSBT text"
  | "inspect", _ | "extract", _ => throw "unexpected arguments after PSBT text"
  | _, _ => throw s!"unknown command '{command}'"

def parseArgs (args : List String) : Except String Command := do
  let args := CliSupport.stripSeparator args
  match args with
  | ["--help"] | ["-h"] => return .help
  | ["inspect", "--help"] | ["finalize", "--help"] | ["extract", "--help"] => return .help
  | command :: "--encoding" :: encoding :: rest =>
    let encoding ← match encoding with
      | "base64" => pure Encoding.base64
      | "hex" => pure Encoding.hex
      | _ => throw s!"unknown encoding '{encoding}'; expected base64 or hex"
    parseCommand command encoding rest
  | [_, "--encoding"] => throw "missing encoding; expected base64 or hex"
  | command :: rest => parseCommand command .base64 rest
  | [] => throw "missing command"

def parsePsbt (encoding : Encoding) (source : String) : Except String Psbt := do
  let source := source.trimAscii.toString
  match encoding with
  | .base64 => (Psbt.parseBase64 source).mapError (fun error => s!"PSBT parse error: {repr error}")
  | .hex =>
    let some bytes := SurfaceParser.decodeHex? source | throw "PSBT parse error: invalid hex"
    (Psbt.parse bytes).mapError (fun error => s!"PSBT parse error: {repr error}")

/-- Validate all assignments before finalizing any input. Missing assignments skip inputs. -/
def resolveDescriptors (count : Nat) (bindings : List (Nat × String)) :
    Except String (List (Option OutputDescriptor)) := do
  let mut descriptors := List.replicate count none
  for (index, source) in bindings do
    if index ≥ count then throw s!"input {index}: index out of range (input count: {count})"
    if ((descriptors[index]?).getD none).isSome then throw s!"input {index}: duplicate descriptor"
    let descriptor ← (parseOutputDescriptor source).mapError (fun error => s!"input {index}: {error}")
    descriptors := descriptors.modify index (fun _ => some descriptor)
  return descriptors

def inspect (psbt : Psbt) : Except String String := do
  let decoded ← psbt.decode.mapError (fun error => s!"PSBT decode error: {repr error}")
  let finalized := decoded.inputs.filter InputFields.isFinalized
  let inputs := decoded.inputs.zipIdx.map fun (input, index) =>
    s!"input[{index}]: {if input.isFinalized then "finalized" else "unfinalized"}"
  return String.intercalate "\n" ([
    s!"psbt_version: {decoded.global.psbtVersion}",
    s!"inputs: {decoded.inputs.length}",
    s!"outputs: {decoded.outputs.length}",
    s!"finalized_inputs: {finalized.length}"] ++ inputs)

def execute : Command → Except String String
  | .help => .ok usage
  | .inspect encoding source => do inspect (← parsePsbt encoding source)
  | .extract encoding source => do
    let psbt ← parsePsbt encoding source
    let tx ← psbt.extract.mapError (fun error => s!"extraction error: {repr error}")
    return byteArrayHex tx
  | .finalize encoding source bindings => do
    let psbt ← parsePsbt encoding source
    let descriptors ← resolveDescriptors psbt.inputs.length bindings
    let result ← descriptors.zipIdx.foldlM (fun stage (descriptor, index) => do
      match descriptor with
      | none => pure stage
      | some descriptor =>
        (stage.finalizeInput {} index descriptor).mapError
          (fun error => s!"input {index}: finalization error: {repr error}")) psbt
    return result.toBase64

end LeanMiniscript.Psbt.Cli
