import LeanMiniscript.Miniscript.SurfaceParserInternal

/-! Context-aware parsing and canonical hexadecimal key resolution.
Round-trip and successful-parse contracts are proved in SurfaceParserProofs. -/

namespace LeanMiniscript.Miniscript

open SurfaceParser

/-- Whether surface text stays within the public parser recursion boundary. -/
def surfaceTextWithinRecursionLimit (input : String) : Bool :=
  tokensWithinSurfaceRecursionLimit (tokenizeSurface input)


/-- Default key resolver for canonical lowercase or uppercase hexadecimal key
    tokens. Context-specific serialized-shape checks remain in `parseSurface`;
    this byte codec does not validate secp256k1 curve membership. -/
def resolveHexKey (token : String) : Except String PubKey :=
  if token.length = 64 ∨ token.length = 66 then
    match decodeHex? token with
    | some bytes => pure (PubKey.ofBytes bytes)
    | none => .error "expected a 32- or 33-byte hexadecimal public key"
  else
    .error "expected a 32- or 33-byte hexadecimal public key"


/-- Parse one supported Miniscript expression, resolve its keys, normalize its
    surface spelling, and reject fragments invalid in the selected context. -/
def parseSurface (context : ScriptContext) (resolver : KeyResolver)
    (input : String) : Except SurfaceParseError SurfaceFragment := do
  let fragment ← parseSurfaceUnchecked context resolver input
  validateSurface context (normalizeSurface fragment)


/-- Parse canonical surface text whose key tokens are raw hexadecimal public
    keys. -/
def parseSurfaceHex (context : ScriptContext) (input : String) :
    Except SurfaceParseError SurfaceFragment :=
  parseSurface context resolveHexKey input

end LeanMiniscript.Miniscript
