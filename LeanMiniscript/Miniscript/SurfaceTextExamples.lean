import LeanMiniscript.Miniscript.SurfaceParser
import LeanMiniscript.Miniscript.SurfacePretty
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Miniscript

private def repeatedBytes (count : Nat) (byte : UInt8) : ByteArray :=
  ⟨Array.replicate count byte⟩

private def p2wshKey : PubKey :=
  PubKey.ofBytes (repeatedBytes 33 0x02)

private def tapscriptKey : PubKey :=
  PubKey.ofBytes (repeatedBytes 32 0x03)

private def hash256Value : Hash256 :=
  Hash256.ofBytes (repeatedBytes 32 0xaa)

private def canonicalRoundTrip
    (context : ScriptContext) (fragment : SurfaceFragment) : Bool :=
  match parseSurfaceHex context (prettySurface fragment) with
  | .ok parsed => prettySurface parsed == prettySurface fragment
  | .error _ => false

private def parsesCanonically
    (context : ScriptContext) (input expected : String) : Bool :=
  match parseSurfaceHex context input with
  | .ok parsed => prettySurface parsed == expected
  | .error _ => false

private def parsesSuccessfully
    (context : ScriptContext) (input : String) : Bool :=
  match parseSurfaceHex context input with
  | .ok _ => true
  | .error _ => false

private def allParseSuccessfully
    (context : ScriptContext) : List String → Bool
  | [] => true
  | input :: inputs =>
      parsesSuccessfully context input && allParseSuccessfully context inputs

private def isInvalidArity : Except SurfaceParseError SurfaceFragment → Bool
  | .error (.invalidArity ..) => true
  | _ => false

private def isInvalidHex : Except SurfaceParseError SurfaceFragment → Bool
  | .error (.invalidHex ..) => true
  | _ => false

private def isInvalidHashLength :
    Except SurfaceParseError SurfaceFragment → Bool
  | .error (.invalidHashLength ..) => true
  | _ => false

private def isKeyResolution :
    Except SurfaceParseError SurfaceFragment → Bool
  | .error (.keyResolution ..) => true
  | _ => false

private def isKeyContext : Except SurfaceParseError SurfaceFragment → Bool
  | .error (.keyContext ..) => true
  | _ => false

private def isContextMismatch :
    Except SurfaceParseError SurfaceFragment → Bool
  | .error (.contextMismatch ..) => true
  | _ => false

private def isValidationFailed :
    Except SurfaceParseError SurfaceFragment → Bool
  | .error (.validationFailed ..) => true
  | _ => false

private def isTrailingInput :
    Except SurfaceParseError SurfaceFragment → Bool
  | .error (.trailingInput ..) => true
  | _ => false

example : canonicalRoundTrip .p2wsh (.pk p2wshKey) = true := by
  native_decide

example :
    canonicalRoundTrip .p2wsh
      (.and_n (.pk p2wshKey) (.core (.older 42))) = true := by
  native_decide

example :
    canonicalRoundTrip .p2wsh
      (.core (.a (.c (.pk_k p2wshKey)))) = true := by
  native_decide

example :
    canonicalRoundTrip .p2wsh
      (.core (.sha256 hash256Value)) = true := by
  native_decide

example :
    canonicalRoundTrip .p2wsh
      (.core (.multi 1 [p2wshKey])) = true := by
  native_decide

example :
    canonicalRoundTrip .tapscript
      (.core (.multi_a 1 [tapscriptKey])) = true := by
  native_decide

private def p2wshConstructorInputs : List String :=
  let key := prettyPubKey p2wshKey
  let hash256 := LeanMiniscript.Script.byteArrayHex hash256Value.bytes
  let hash160 := LeanMiniscript.Script.byteArrayHex (repeatedBytes 20 0xbb)
  [
    "0",
    "1",
    "pk_k(" ++ key ++ ")",
    "pk_h(" ++ key ++ ")",
    "older(42)",
    "after(500)",
    "sha256(" ++ hash256 ++ ")",
    "hash256(" ++ hash256 ++ ")",
    "ripemd160(" ++ hash160 ++ ")",
    "hash160(" ++ hash160 ++ ")",
    "and_v(1,1)",
    "and_b(1,1)",
    "or_b(1,1)",
    "or_c(1,1)",
    "or_d(1,1)",
    "or_i(1,1)",
    "andor(1,1,1)",
    "a:1",
    "s:1",
    "c:1",
    "d:1",
    "v:1",
    "j:1",
    "n:1",
    "thresh(1,1)",
    "multi(1," ++ key ++ ")",
    "pk(" ++ key ++ ")",
    "pkh(" ++ key ++ ")",
    "and_n(1,1)",
    "t:1",
    "l:1",
    "u:1"
  ]

example :
    allParseSuccessfully .p2wsh p2wshConstructorInputs = true := by
  native_decide

example :
    parsesSuccessfully .tapscript
      ("multi_a(1," ++ prettyPubKey tapscriptKey ++ ")") = true := by
  native_decide

example :
    (match parseSurfaceHex .tapscript
      ("pk(" ++ prettyPubKey p2wshKey ++ ")") with
    | .ok fragment =>
        match compileSurface fragment with
        | [.pushData key, .op .OP_CHECKSIG] =>
            key.size == 32 &&
              key.data == p2wshKey.bytes.data.extract 1 33
        | _ => false
    | .error _ => false) = true := by
  native_decide

example :
    isKeyContext
      (parseSurfaceHex .tapscript
        ("pk(" ++ prettyPubKey
          (PubKey.ofBytes (repeatedBytes 33 0x04)) ++ ")")) = true := by
  native_decide

example : ¬ (CoreFragment.pk_k p2wshKey).WellFormed .tapscript := by
  native_decide

example :
    parsesCanonically .p2wsh
      ("c:pk_k(" ++ prettyPubKey p2wshKey ++ ")")
      ("pk(" ++ prettyPubKey p2wshKey ++ ")") = true := by
  native_decide

example :
    parsesCanonically .p2wsh "  and_v( 1 , older(42) )  "
      "and_v(1,older(42))" = true := by
  native_decide

example :
    parsesCanonically .p2wsh "d:v:older(144)" "dv:older(144)" = true := by
  native_decide

example :
    parsesCanonically .p2wsh "dv:older(144)" "dv:older(144)" = true := by
  native_decide

example :
    parsesCanonically .p2wsh
      ("a:t:pk(" ++ prettyPubKey p2wshKey ++ ")")
      ("at:pk(" ++ prettyPubKey p2wshKey ++ ")") = true := by
  native_decide

example :
    isInvalidArity (parseSurfaceHex .p2wsh "and_v(1)") = true := by
  native_decide

example :
    isInvalidHashLength (parseSurfaceHex .p2wsh "sha256(aa)") = true := by
  native_decide

example :
    isInvalidHex (parseSurfaceHex .p2wsh "sha256(not-hex)") = true := by
  native_decide

example :
    isContextMismatch
      (parseSurfaceHex .p2wsh
        ("multi_a(1," ++ prettyPubKey tapscriptKey ++ ")")) = true := by
  native_decide

example :
    isKeyContext
      (parseSurfaceHex .p2wsh
        ("pk(" ++ prettyPubKey tapscriptKey ++ ")")) = true := by
  native_decide

example :
    isValidationFailed (parseSurfaceHex .p2wsh "thresh(2,1)") = true := by
  native_decide

example :
    isTrailingInput (parseSurfaceHex .p2wsh "1 0") = true := by
  native_decide

private def namedKeyResolver : KeyResolver
  | "alice" => pure p2wshKey
  | token => .error ("unknown key: " ++ token)

example :
    isKeyResolution
      (parseSurface .p2wsh namedKeyResolver "pk(bob)") = true := by
  native_decide

example :
    (match parseSurface .p2wsh namedKeyResolver "pk(alice)" with
    | .ok (.pk key) => key.bytes.data == p2wshKey.bytes.data
    | _ => false) = true := by
  native_decide

end LeanMiniscript.Miniscript
