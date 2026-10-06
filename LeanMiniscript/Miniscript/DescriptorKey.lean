import LeanMiniscript.Bitcoin.BIP32
import LeanMiniscript.Miniscript.SurfaceParser

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Bitcoin

/-! Concrete BIP380 key expressions with the BIP386 x-only key extension.
Origin paths describe provenance; only the suffix after an extended key is
derived. Parsing retains hardened xpub paths, whose resolution requires private
material and therefore fails here. `DescriptorParser.lean` adds output wrappers
and checksum validation around this Miniscript key boundary.
-/

/-- Concrete key material retains WIF compression and extended-key metadata. -/
inductive DescriptorKeyMaterial where
  | publicKey (bytes : ByteArray)
  | xOnlyPublicKey (bytes : ByteArray)
  | privateKey (wif : KeyEncoding.WIF)
  | extendedKey (key : BIP32.ExtendedKey)

/-- A parsed descriptor key, before selecting a wildcard child. -/
structure DescriptorKey where
  origin : Option KeyOrigin := none
  material : DescriptorKeyMaterial
  derivation : List DerivationStep := []
  wildcard : ChildWildcard := .none

private def hexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexDigit high
      let low ← hexDigit low
      let tail ← decodeHexChars rest
      return UInt8.ofNat (16 * high + low) :: tail
  | _ => none

private def parseHex (text : String) : Except String ByteArray :=
  match decodeHexChars text.toList with
  | some bytes => .ok ⟨bytes.toArray⟩
  | none => .error "Expected hexadecimal key bytes"

private def parseDerivationStep (text : String) : Except String DerivationStep := do
  let (hardened, digits) := match text.toList.reverse with
    | 'h' :: rest | '\'' :: rest => (true, rest.reverse)
    | _ => (false, text.toList)
  if digits.isEmpty then throw "Empty derivation index"
  let mut index := 0
  for char in digits do
    if char < '0' || char > '9' then throw "Invalid derivation index"
    index := 10 * index + char.toNat - '0'.toNat
    if index ≥ 0x80000000 then throw "Derivation index must be below 2^31"
  return if hardened then .hardened index else .normal index

private def parseOrigin (text : String) : Except String KeyOrigin := do
  match text.splitOn "/" with
  | [] => throw "Missing key origin fingerprint"
  | fingerprint :: path =>
      if fingerprint.length != 8 then throw "Key origin fingerprint must be eight hex digits"
      let fingerprint ← parseHex fingerprint
      let path ← path.mapM parseDerivationStep
      return { fingerprint, path }

private def splitOrigin (text : String) : Except String (Option KeyOrigin × String) := do
  match text.toList with
  | '[' :: rest =>
      let origin := rest.takeWhile (· != ']')
      if origin.length == rest.length then throw "Missing closing key origin bracket"
      let parsed ← parseOrigin (String.ofList origin)
      return (some parsed, String.ofList (rest.drop (origin.length + 1)))
  | _ => return (none, text)

private def parseMaterial (text : String) : Except String DescriptorKeyMaterial := do
  if text.length == 64 || text.length == 66 || text.length == 130 then
    let bytes ← parseHex text
    if bytes.size == 32 then
      if (Secp256k1.liftX (Secp256k1.decodeBE bytes)).isNone then
        throw "Invalid x-only public key"
      return .xOnlyPublicKey bytes
    if !KeyEncoding.validatePublicKey bytes then throw "Invalid SEC public key"
    return .publicKey bytes
  let payload ← KeyEncoding.decodeBase58Check text
  if payload.size == 78 then
    return .extendedKey (← BIP32.parse text)
  return .privateKey (← KeyEncoding.decodeWIF text)

private def parseSuffix (parts : List String) :
    Except String (List DerivationStep × ChildWildcard) := do
  match parts.reverse with
  | "*" :: rest => return (← rest.reverse.mapM parseDerivationStep, .normal)
  | "*h" :: rest | "*'" :: rest =>
      return (← rest.reverse.mapM parseDerivationStep, .hardened)
  | _ => return (← parts.mapM parseDerivationStep, .none)

/-- Parse and validate BIP380 key syntax, encodings, and curve membership.
Hardened derivation from an xpub is syntactically valid; resolution reports the
missing private material. Only extended keys may have a suffix or wildcard. -/
def parseDescriptorKey (text : String) : Except String DescriptorKey := do
  let (origin, body) ← splitOrigin text
  match body.splitOn "/" with
  | [] => throw "Missing descriptor key"
  | token :: suffix =>
      if token.isEmpty then throw "Missing descriptor key"
      let material ← parseMaterial token
      let (derivation, wildcard) ← parseSuffix suffix
      match material with
      | .extendedKey _ => pure ()
      | _ => if !suffix.isEmpty then throw "Only extended keys allow derivation"
      return { origin, material, derivation, wildcard }

private def derivationIndex : DerivationStep → Except String Nat
  | .normal index =>
      if index < 0x80000000 then .ok index
      else .error "Derivation index must be below 2^31"
  | .hardened index =>
      if index < 0x80000000 then .ok (index + 0x80000000)
      else .error "Derivation index must be below 2^31"

private def selectedPath (key : DescriptorKey) (wildcardIndex : Option Nat) :
    Except String (List Nat) := do
  let path ← key.derivation.mapM derivationIndex
  match key.wildcard with
  | .none => return path
  | .normal | .hardened =>
      let some index := wildcardIndex | throw "A wildcard key requires a child index"
      if index ≥ 0x80000000 then throw "Wildcard child index must be below 2^31"
      return path ++ [index + if key.wildcard == .hardened then 0x80000000 else 0]

/-- Resolve exactly the requested derivation path. Origin metadata is retained
but does not change the key. Invalid children produce an error without changing
the requested index. A supplied index is ignored for keys without a wildcard. -/
def DescriptorKey.resolve (key : DescriptorKey) (wildcardIndex : Option Nat := none) :
    Except String PubKey := do
  if let some origin := key.origin then
    if origin.fingerprint.size != 4 then throw "Key origin fingerprint must be four bytes"
    let _ ← origin.path.mapM derivationIndex
  let path ← selectedPath key wildcardIndex
  match key.material with
  | .extendedKey extended =>
      return PubKey.ofBytes (← BIP32.publicKey (← BIP32.derivePath extended path))
  | material =>
      if !key.derivation.isEmpty || key.wildcard != .none then
        throw "Only extended keys allow derivation"
      match material with
      | .publicKey bytes =>
          if !KeyEncoding.validatePublicKey bytes then throw "Invalid SEC public key"
          return PubKey.ofBytes bytes
      | .xOnlyPublicKey bytes =>
          if bytes.size != 32 || (Secp256k1.liftX (Secp256k1.decodeBE bytes)).isNone then
            throw "Invalid x-only public key"
          return PubKey.ofBytes bytes
      | .privateKey wif =>
          return PubKey.ofBytes (← KeyEncoding.publicKeyFromSecret wif.secret wif.compressed)
      | .extendedKey _ => throw "Unexpected extended key"

/-- Strict descriptor key resolver for the existing surface parser. -/
def resolveDescriptorKey (wildcardIndex : Option Nat := none) : KeyResolver :=
  fun token => do (← parseDescriptorKey token).resolve wildcardIndex

-- Descriptor inputs can contain WIF or extended private keys, including in
-- malformed tokens. Retain error categories, positions and static diagnostics
-- while removing every field that can copy text from the input.
private def redactDescriptorError : SurfaceParseError → SurfaceParseError
  | .unexpectedToken position expected _ => .unexpectedToken position expected "[redacted]"
  | .trailingInput position _ => .trailingInput position "[redacted]"
  | .unknownFragment position _ => .unknownFragment position "[redacted]"
  | .unknownWrapper position _ => .unknownWrapper position "[redacted]"
  | .invalidArity position _ expected actual =>
      .invalidArity position "[redacted]" expected actual
  | .invalidNumber position _ => .invalidNumber position "[redacted]"
  | .invalidHex position role _ => .invalidHex position role "[redacted]"
  | .keyResolution position _ message => .keyResolution position "[redacted]" message
  | .keyContext position _ context => .keyContext position "[redacted]" context
  | .contextMismatch position _ context => .contextMismatch position "[redacted]" context
  | error => error

/-- Parse Miniscript with concrete descriptor keys. The selected context checks
compression and normalizes compressed Tapscript keys to their x-only form.
Errors redact input tokens, which may contain private key material. -/
def parseSurfaceDescriptor (context : ScriptContext) (input : String)
    (wildcardIndex : Option Nat := none) : Except SurfaceParseError SurfaceFragment :=
  match parseSurface context (resolveDescriptorKey wildcardIndex) input with
  | .ok fragment => .ok fragment
  | .error error => .error (redactDescriptorError error)

end LeanMiniscript.Miniscript
