import LeanMiniscript.Bitcoin.DescriptorChecksum
import LeanMiniscript.Miniscript.DescriptorKey
import LeanMiniscript.Miniscript.OutputDescriptor

namespace LeanMiniscript.Miniscript

/-! Output-descriptor parsing for `wsh`, `sh(wsh(...))` and `tr`.
The checksum is checked on the original text before parsing. Miniscript leaves
use the existing context-aware parser and must have base type B. Taproot trees
retain their binary shape and allow at most 128 branch levels.
-/

private def maxDelimiterDepth : Nat := maxSurfaceRecursionDepth + 132

/-- Split arguments while checking properly nested parentheses, tree braces,
and key-origin brackets. Commas inside any of these delimiters are retained. -/
private def splitArguments (text : String) : Except String (List String) := do
  let mut stack : List Char := []
  let mut current : List Char := []
  let mut arguments : List String := []
  for char in text.toList do
    if char == ',' && stack.isEmpty then
      arguments := String.ofList current.reverse :: arguments
      current := []
    else
      match char with
      | '(' | '{' | '[' =>
          if stack.length ≥ maxDelimiterDepth then
            throw "Descriptor delimiter nesting exceeds the supported depth"
          let closing := if char == '(' then ')' else if char == '{' then '}' else ']'
          stack := closing :: stack
      | ')' | '}' | ']' =>
          match stack with
          | expected :: rest =>
              if char != expected then throw "Mismatched descriptor delimiter"
              stack := rest
          | [] => throw "Unexpected closing descriptor delimiter"
      | _ => pure ()
      current := char :: current
  if !stack.isEmpty then throw "Unclosed descriptor delimiter"
  return (String.ofList current.reverse :: arguments).reverse

private def parseCall (text : String) : Except String (String × String) := do
  let chars := text.toList
  let name := chars.takeWhile (· != '(')
  match chars.drop name.length with
  | '(' :: rest =>
      match rest.reverse with
      | ')' :: reversedBody =>
          return (String.ofList name, String.ofList reversedBody.reverse)
      | _ => throw "Descriptor call must end with a closing parenthesis"
  | _ => throw "Expected an output-descriptor function"

private def parseLeaf (context : ScriptContext) (text : String)
    (wildcardIndex : Option Nat) : Except String SurfaceFragment := do
  let fragment ← match parseSurfaceDescriptor context text wildcardIndex with
    | .ok fragment => pure fragment
    | .error error => throw s!"Invalid Miniscript: {reprStr error}"
  match inferType context (desugar fragment) with
  | some ⟨.B, _⟩ => return fragment
  | _ => throw "An output-descriptor script must have Miniscript base type B"

private def parseTree : Nat → String → Option Nat → Except String DescriptorTree
  | 0, _, _ => .error "Taproot tree exceeds 128 branch levels"
  | fuel + 1, text, wildcardIndex => do
      match text.toList with
      | '{' :: rest =>
          match rest.reverse with
          | '}' :: reversedBody =>
              let arguments ← splitArguments (String.ofList reversedBody.reverse)
              match arguments with
              | [left, right] =>
                  if left.isEmpty || right.isEmpty then throw "Taproot branches require two nonempty children"
                  let left ← parseTree fuel left wildcardIndex
                  let right ← parseTree fuel right wildcardIndex
                  return .branch left right
              | _ => throw "Taproot branches require exactly two children"
          | _ => throw "Taproot branch must end with a closing brace"
      | _ => return .leaf (← parseLeaf .tapscript text wildcardIndex)

private def parseInternalKey (text : String) (wildcardIndex : Option Nat) :
    Except String PubKey := do
  let key ← resolveDescriptorKey wildcardIndex text
  if key.size == 32 then return key
  if validCompressedPubKeyBytes key.bytes then
    return PubKey.ofBytes (key.bytes.extract 1 33)
  throw "Taproot internal keys must use compressed or x-only public keys"

private def parseWsh (body : String) (wildcardIndex : Option Nat) :
    Except String SurfaceFragment := do
  match ← splitArguments body with
  | [script] => parseLeaf .p2wsh script wildcardIndex
  | _ => throw "wsh requires exactly one Miniscript argument"

/-- Parse the supported output-descriptor wrappers and validate every script
and key. A provided wildcard index is shared by all key expressions. Existing
checksums are always verified; `requireChecksum` also rejects an absent one. -/
def parseOutputDescriptor (input : String) (wildcardIndex : Option Nat := none)
    (requireChecksum : Bool := false) : Except String OutputDescriptor := do
  let text ← Bitcoin.DescriptorChecksum.validate input requireChecksum
  let (name, body) ← parseCall text
  match name with
  | "wsh" => return .wsh (← parseWsh body wildcardIndex)
  | "sh" =>
      match ← splitArguments body with
      | [inner] =>
          let (innerName, innerBody) ← parseCall inner
          if innerName != "wsh" then throw "sh requires a wsh Miniscript descriptor"
          return .shWsh (← parseWsh innerBody wildcardIndex)
      | _ => throw "sh requires exactly one wsh descriptor"
  | "tr" =>
      match ← splitArguments body with
      | [key] => return .tr (← parseInternalKey key wildcardIndex) none
      | [key, tree] =>
          let key ← parseInternalKey key wildcardIndex
          let tree ← parseTree 129 tree wildcardIndex
          return .tr key (some tree)
      | _ => throw "tr requires an internal key and an optional script tree"
  | _ => throw "Supported output descriptors are wsh, sh(wsh), and tr"

/-- Parse a descriptor and compile its output and associated spend scripts. -/
def deriveOutputDescriptor (input : String) (wildcardIndex : Option Nat := none)
    (requireChecksum : Bool := false) : Except String CompiledDescriptor := do
  compileOutputDescriptor (← parseOutputDescriptor input wildcardIndex requireChecksum)

end LeanMiniscript.Miniscript
