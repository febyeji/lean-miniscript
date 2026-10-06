import LeanMiniscript.Bitcoin.TaprootControlBlock

namespace LeanMiniscript.Extraction

open LeanMiniscript.Bitcoin

/-- Witness elements and optional output key produced by Core's Script-test
template syntax. Amount parsing belongs to the enclosing fixture boundary. -/
structure ResolvedCoreFixtureTemplates where
  witness : List ByteArray
  outputKey : Option ByteArray := none
  deriving Repr

private def templateHexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def templateHexBytes : List Char → Except String (List UInt8)
  | [] => .ok []
  | [_] => .error "witness hex has odd length"
  | high :: low :: rest => do
      let high ← match templateHexDigit high with
        | some value => pure value
        | none => throw "witness contains invalid hex"
      let low ← match templateHexDigit low with
        | some value => pure value
        | none => throw "witness contains invalid hex"
      return UInt8.ofNat (16 * high + low) :: (← templateHexBytes rest)

private def templateBytes32 (value : Nat) : ByteArray :=
  ⟨(unsignedLE 32 value).reverse.toArray⟩

/-- Core's fixture key0 is the public test scalar 1; its x-only public key is
the generator's x coordinate. This is fixture construction, not key generation. -/
def coreFixtureTemplateInternalKey : ByteArray :=
  templateBytes32 (Secp256k1.generator.getD (0, 0)).1

/-- Build the depth-zero leaf/control/output triple used by script_tests.cpp.
Both output x coordinate and parity are computed from the actual script bytes. -/
def coreFixtureTemplateCommitment (script : ByteArray) :
    Except String (ByteArray × ByteArray) := do
  let internalKey := coreFixtureTemplateInternalKey
  let leafHash := tapleafHash script 0xc0
  let (x, y) ← (taprootTweakPoint internalKey
    (taggedHash "TapTweak" (internalKey ++ leafHash))).mapError
      (fun error => s!"invalid Taproot fixture commitment: {repr error}")
  let control := ⟨#[UInt8.ofNat (0xc0 + y % 2)]⟩ ++ internalKey
  return (control, templateBytes32 x)

private def resolveTemplatesAux (compile : String → Except String ByteArray) :
    List String → List ByteArray → Option ByteArray → Except String ResolvedCoreFixtureTemplates
  | [], reversed, output => .ok { witness := reversed.reverse, outputKey := output }
  | element :: rest, reversed, output => do
      if element.startsWith "#SCRIPT#" then
        let bytes ← compile (String.ofList (element.toList.drop 8))
        resolveTemplatesAux compile rest (bytes :: reversed) output
      else if element == "#CONTROLBLOCK#" then
        if output.isSome then throw "duplicate fixture control-block template"
        match reversed with
        | [] => throw "fixture control-block template has no preceding script"
        | script :: _ =>
            let (control, key) ← coreFixtureTemplateCommitment script
            resolveTemplatesAux compile rest (control :: reversed) (some key)
      else
        let bytes ← templateHexBytes element.toList
        resolveTemplatesAux compile rest (⟨bytes.toArray⟩ :: reversed) output

/-- Expand hex, #SCRIPT# and #CONTROLBLOCK# elements in source order. Script
compilation is injected to avoid a dependency on the fixture importer. -/
def resolveCoreFixtureTemplates (compile : String → Except String ByteArray)
    (elements : List String) : Except String ResolvedCoreFixtureTemplates :=
  resolveTemplatesAux compile elements [] none

/-- Expand Core's generated Taproot output placeholder or compile an ordinary
scriptPubKey using the same source compiler as all other fixture scripts. -/
def resolveCoreFixtureScriptPubKey (compile : String → Except String ByteArray)
    (templates : ResolvedCoreFixtureTemplates) (source : String) : Except String ByteArray :=
  if source == "0x51 0x20 #TAPROOTOUTPUT#" then
    match templates.outputKey with
    | none => .error "Taproot output template has no generated commitment"
    | some key => .ok (⟨#[0x51, 0x20]⟩ ++ key)
  else compile source

end LeanMiniscript.Extraction
