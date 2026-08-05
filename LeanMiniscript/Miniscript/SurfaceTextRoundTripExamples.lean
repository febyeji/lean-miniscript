import LeanMiniscript.Miniscript.SurfaceParser
import LeanMiniscript.Miniscript.SurfacePretty
import LeanMiniscript.Miniscript.SurfaceTextProofs

namespace LeanMiniscript.Miniscript

private def repeatedBytes (count : Nat) (byte : UInt8) : ByteArray :=
  ⟨Array.replicate count byte⟩

private def p2wshKey : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (Array.replicate 32 0x11)⟩

private def tapscriptKey : PubKey :=
  PubKey.ofBytes (repeatedBytes 32 0x22)

private def hash256Text : String :=
  LeanMiniscript.Script.byteArrayHex (repeatedBytes 32 0xaa)

private def hash160Text : String :=
  LeanMiniscript.Script.byteArrayHex (repeatedBytes 20 0xbb)

private structure SurfaceGoldenCase where
  context : ScriptContext
  input : String
  canonical : String

private def checkGoldenCase (test : SurfaceGoldenCase) : Bool :=
  match parseSurfaceHex test.context test.input with
  | .error _ => false
  | .ok parsed =>
      let rendered := prettySurface parsed
      rendered == test.canonical &&
        match parseSurfaceHex test.context rendered with
        | .error _ => false
        | .ok reparsed => prettySurface reparsed == test.canonical

private def checkAllGoldenCases : List SurfaceGoldenCase → Bool
  | [] => true
  | test :: tests => checkGoldenCase test && checkAllGoldenCases tests

/-- One canonical parse/pretty case for every current core constructor and every
    surface-only sugar constructor. -/
private def constructorGoldenCases : List SurfaceGoldenCase :=
  let key := prettyPubKey p2wshKey
  let xkey := prettyPubKey tapscriptKey
  [
    ⟨.p2wsh, "0", "0"⟩,
    ⟨.p2wsh, "1", "1"⟩,
    ⟨.p2wsh, "pk_k(" ++ key ++ ")", "pk_k(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "pk_h(" ++ key ++ ")", "pk_h(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "older(42)", "older(42)"⟩,
    ⟨.p2wsh, "after(500)", "after(500)"⟩,
    ⟨.p2wsh, "sha256(" ++ hash256Text ++ ")",
      "sha256(" ++ hash256Text ++ ")"⟩,
    ⟨.p2wsh, "hash256(" ++ hash256Text ++ ")",
      "hash256(" ++ hash256Text ++ ")"⟩,
    ⟨.p2wsh, "ripemd160(" ++ hash160Text ++ ")",
      "ripemd160(" ++ hash160Text ++ ")"⟩,
    ⟨.p2wsh, "hash160(" ++ hash160Text ++ ")",
      "hash160(" ++ hash160Text ++ ")"⟩,
    ⟨.p2wsh, "and_v(1,0)", "and_v(1,0)"⟩,
    ⟨.p2wsh, "and_b(1,1)", "and_b(1,1)"⟩,
    ⟨.p2wsh, "or_b(1,1)", "or_b(1,1)"⟩,
    ⟨.p2wsh, "or_c(1,1)", "or_c(1,1)"⟩,
    ⟨.p2wsh, "or_d(1,1)", "or_d(1,1)"⟩,
    ⟨.p2wsh, "or_i(1,1)", "or_i(1,1)"⟩,
    ⟨.p2wsh, "andor(1,1,1)", "andor(1,1,1)"⟩,
    ⟨.p2wsh, "a:1", "a:1"⟩,
    ⟨.p2wsh, "s:1", "s:1"⟩,
    ⟨.p2wsh, "c:1", "c:1"⟩,
    ⟨.p2wsh, "d:1", "d:1"⟩,
    ⟨.p2wsh, "v:1", "v:1"⟩,
    ⟨.p2wsh, "j:1", "j:1"⟩,
    ⟨.p2wsh, "n:1", "n:1"⟩,
    ⟨.p2wsh, "thresh(1,1)", "thresh(1,1)"⟩,
    ⟨.p2wsh, "multi(1," ++ key ++ ")", "multi(1," ++ key ++ ")"⟩,
    ⟨.tapscript, "multi_a(1," ++ xkey ++ ")",
      "multi_a(1," ++ xkey ++ ")"⟩,
    ⟨.p2wsh, "pk(" ++ key ++ ")", "pk(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "pkh(" ++ key ++ ")", "pkh(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "and_n(1,1)", "and_n(1,1)"⟩,
    ⟨.p2wsh, "t:1", "t:1"⟩,
    ⟨.p2wsh, "l:1", "l:1"⟩,
    ⟨.p2wsh, "u:1", "u:1"⟩
  ]

/-- Desugared core aliases and noncanonical wrapper separators normalize to the
    documented surface spelling. -/
private def normalizationGoldenCases : List SurfaceGoldenCase :=
  let key := prettyPubKey p2wshKey
  [
    ⟨.p2wsh, "c:pk_k(" ++ key ++ ")", "pk(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "c:pk_h(" ++ key ++ ")", "pkh(" ++ key ++ ")"⟩,
    ⟨.p2wsh, "andor(1,1,0)", "and_n(1,1)"⟩,
    ⟨.p2wsh, "and_v(1,1)", "t:1"⟩,
    ⟨.p2wsh, "or_i(0,1)", "l:1"⟩,
    ⟨.p2wsh, "or_i(1,0)", "u:1"⟩,
    ⟨.p2wsh, "d:v:older(144)", "dv:older(144)"⟩
  ]

example : checkAllGoldenCases constructorGoldenCases = true := by
  native_decide

example : checkAllGoldenCases normalizationGoldenCases = true := by
  native_decide

private inductive SurfaceErrorTag where
  | emptyInput
  | unexpectedEnd
  | unexpectedToken
  | trailingInput
  | unknownFragment
  | unknownWrapper
  | invalidArity
  | expectedAtom
  | invalidNumber
  | invalidHex
  | invalidHashLength
  | keyResolution
  | keyContext
  | contextMismatch
  | validationFailed
  deriving BEq

private def SurfaceParseError.tag : SurfaceParseError → SurfaceErrorTag
  | .emptyInput => .emptyInput
  | .unexpectedEnd .. => .unexpectedEnd
  | .unexpectedToken .. => .unexpectedToken
  | .trailingInput .. => .trailingInput
  | .unknownFragment .. => .unknownFragment
  | .unknownWrapper .. => .unknownWrapper
  | .invalidArity .. => .invalidArity
  | .expectedAtom .. => .expectedAtom
  | .invalidNumber .. => .invalidNumber
  | .invalidHex .. => .invalidHex
  | .invalidHashLength .. => .invalidHashLength
  | .keyResolution .. => .keyResolution
  | .keyContext .. => .keyContext
  | .contextMismatch .. => .contextMismatch
  | .validationFailed .. => .validationFailed

private structure SurfaceErrorCase where
  context : ScriptContext
  input : String
  expected : SurfaceErrorTag

private def checkErrorCase (test : SurfaceErrorCase) : Bool :=
  match parseSurfaceHex test.context test.input with
  | .error error => error.tag == test.expected
  | .ok _ => false

private def checkAllErrorCases : List SurfaceErrorCase → Bool
  | [] => true
  | test :: tests => checkErrorCase test && checkAllErrorCases tests

private def hexadecimalErrorCases : List SurfaceErrorCase :=
  let key32 := prettyPubKey tapscriptKey
  [
    ⟨.p2wsh, "", .emptyInput⟩,
    ⟨.p2wsh, "and_v(1", .unexpectedEnd⟩,
    ⟨.p2wsh, "(", .unexpectedToken⟩,
    ⟨.p2wsh, "1 0", .trailingInput⟩,
    ⟨.p2wsh, "mystery(1)", .unknownFragment⟩,
    ⟨.p2wsh, "q:1", .unknownWrapper⟩,
    ⟨.p2wsh, "and_v(1)", .invalidArity⟩,
    ⟨.p2wsh, "older(pk())", .expectedAtom⟩,
    ⟨.p2wsh, "older(nope)", .invalidNumber⟩,
    ⟨.p2wsh, "sha256(not-hex)", .invalidHex⟩,
    ⟨.p2wsh, "sha256(aa)", .invalidHashLength⟩,
    ⟨.p2wsh, "pk(" ++ key32 ++ ")", .keyContext⟩,
    ⟨.p2wsh, "multi_a(1," ++ key32 ++ ")", .contextMismatch⟩,
    ⟨.p2wsh, "thresh(2,1)", .validationFailed⟩
  ]

example : checkAllErrorCases hexadecimalErrorCases = true := by
  native_decide

private def namedKeyResolver : KeyResolver
  | "alice" => pure p2wshKey
  | token => .error ("unknown key: " ++ token)

example :
    (match parseSurface .p2wsh namedKeyResolver "pk(bob)" with
    | .error error => error.tag == .keyResolution
    | .ok _ => false) = true := by
  native_decide

end LeanMiniscript.Miniscript
