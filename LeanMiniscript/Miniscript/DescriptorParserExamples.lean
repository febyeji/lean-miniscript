import LeanMiniscript.Miniscript.DescriptorParser

namespace LeanMiniscript.Miniscript.DescriptorParserExamples

open Bitcoin

private def succeeds {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private def compressed : String :=
  "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def xOnly : String :=
  "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def uncompressed : String :=
  "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"

private def extended : String :=
  "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL"

private def valid : Array String := #[
  "wsh(1)", "wsh(0)", "sh(wsh(1))", "wsh( 1 )",
  "wsh(pk(" ++ compressed ++ "))",
  "sh(wsh(pk([deadbeef/0h/1']" ++ compressed ++ ")))",
  "wsh(and_v(v:pk(" ++ compressed ++ "),older(10)))",
  "tr(" ++ compressed ++ ")", "tr(" ++ xOnly ++ ")",
  "tr(" ++ xOnly ++ ",pk(" ++ xOnly ++ "))",
  "tr(" ++ xOnly ++ ",{pk(" ++ xOnly ++ "),{1,0}})",
  "tr(" ++ xOnly ++ ",{and_v(v:pk(" ++ xOnly ++ "),older(10)),pkh(" ++ xOnly ++ ")})",
  "tr(" ++ xOnly ++ ",multi_a(1," ++ xOnly ++ "," ++ xOnly ++ "))"]

example : valid.all (fun text => succeeds (parseOutputDescriptor text)) = true := by
  native_decide

private def malformed : Array String := #[
  "", "wsh", "wsh(", "wsh()", "wsh(1", "wsh(1))", "wsh(1)extra",
  "wsh(1)()", "wsh(1)(0)", "wsh((1))", "wsh(1,0)", "wsh(1,)",
  "wsh({1,0})", "wsh(1]", "sh()", "sh(wsh())", "sh(wsh(1),wsh(0))",
  "sh(wsh(1))extra", "sh(sh(wsh(1)))", "sh(wsh(1)())", "sh(wsh(1),)",
  "tr()", "tr(,)", "tr(" ++ xOnly ++ ",)", "tr(" ++ xOnly ++ ",1,0)",
  "tr(" ++ xOnly ++ ",{1})", "tr(" ++ xOnly ++ ",{})",
  "tr(" ++ xOnly ++ ",{,1})", "tr(" ++ xOnly ++ ",{1,})",
  "tr(" ++ xOnly ++ ",{1,0,1})", "tr(" ++ xOnly ++ ",{{1,0},})",
  "tr(" ++ xOnly ++ ",{1,0])", "tr(" ++ xOnly ++ ",{{1,0},1))",
  "tr(" ++ xOnly ++ ",1})", "tr(" ++ xOnly ++ ",{1,0})extra",
  "tr(" ++ xOnly ++ ",{1,0}{1,0})", "tr(" ++ xOnly ++ ",{1,0},)",
  "wsh(pk([deadbeef/0h)" ++ compressed ++ "))",
  "wsh(pk([deadbeef,0]" ++ compressed ++ "))",
  "tr([deadbeef/0h]" ++ xOnly ++ ",[1,0])"]

example : malformed.all (fun text => !succeeds (parseOutputDescriptor text)) = true := by
  native_decide

private def unsupported : Array String := #[
  "pk(" ++ compressed ++ ")", "sh(pk(" ++ compressed ++ "))",
  "wpkh(" ++ compressed ++ ")", "sh(wpkh(" ++ compressed ++ "))",
  "wsh(tr(" ++ xOnly ++ "))", "tr(" ++ xOnly ++ ",wsh(1))",
  "tr(" ++ xOnly ++ ",tr(" ++ xOnly ++ "))", "raw(51)", "addr(address)",
  "WSH(1)", "wsh (1)"]

example : unsupported.all (fun text => !succeeds (parseOutputDescriptor text)) = true := by
  native_decide

-- Well-typed V, K and W fragments still cannot be complete output scripts.
private def nonBaseScripts : Array String := #[
  "v:pk(" ++ compressed ++ ")", "pk_k(" ++ compressed ++ ")",
  "a:pk(" ++ compressed ++ ")"]

example : nonBaseScripts.all (fun script =>
    !succeeds (parseOutputDescriptor ("wsh(" ++ script ++ ")"))) = true := by native_decide
example : nonBaseScripts.all (fun script =>
    !succeeds (parseOutputDescriptor ("sh(wsh(" ++ script ++ "))"))) = true := by native_decide
example : nonBaseScripts.all (fun script =>
    !succeeds (parseOutputDescriptor ("tr(" ++ xOnly ++ "," ++ script ++ ")"))) = true := by
  native_decide

example : !succeeds (parseOutputDescriptor ("tr(" ++ uncompressed ++ ")")) = true := by
  native_decide
example : !succeeds (parseOutputDescriptor
    "tr(0000000000000000000000000000000000000000000000000000000000000000)") = true := by
  native_decide
example : !succeeds (parseOutputDescriptor ("wsh(pk(" ++ xOnly ++ "))")) = true := by
  native_decide
example : !succeeds (parseOutputDescriptor
    ("tr(" ++ xOnly ++ ",multi(1," ++ compressed ++ "))")) = true := by native_decide

-- Compressed internal keys are normalized at the parse boundary itself.
example :
    (match parseOutputDescriptor ("tr([deadbeef/0h]" ++ compressed ++ ")") with
    | .ok (.tr key none) => Script.byteArrayHex key.bytes == xOnly
    | _ => false) = true := by native_decide

private def sharedWildcard : String :=
  let ranged := extended ++ "/3/4/5/*"
  "tr(" ++ ranged ++ ",{pk(" ++ ranged ++ "),pk([deadbeef/99h]" ++ ranged ++ ")})"

-- Frozen public key independently derived using Python HMAC-SHA512 and
-- cryptography/OpenSSL in DescriptorKeyReviewExamples.lean.
example :
    (match parseOutputDescriptor sharedWildcard (some 7) with
    | .ok (.tr key (some (.branch (.leaf left) (.leaf right)))) =>
        let expected := "3853242d8e41d3e5aa7ab185d260eed57a38b0155340a06eeb36af80092a02b5"
        Script.byteArrayHex key.bytes == expected &&
          prettySurface left == "pk(" ++ expected ++ ")" &&
          prettySurface right == "pk(" ++ expected ++ ")"
    | _ => false) = true := by native_decide

example : !succeeds (parseOutputDescriptor sharedWildcard) = true := by native_decide
example : !succeeds (parseOutputDescriptor sharedWildcard (some 2147483648)) = true := by
  native_decide
example : !succeeds (parseOutputDescriptor
    ("tr(" ++ extended ++ "/0h)") (some 0)) = true := by native_decide
example : !succeeds (parseOutputDescriptor
    ("tr(" ++ xOnly ++ ",pk(" ++ extended ++ "/*h))") (some 0)) = true := by native_decide

private def parsesChecksummed : Bool :=
  match DescriptorChecksum.addChecksum "sh(wsh(1))" with
  | .error _ => false
  | .ok text => succeeds (parseOutputDescriptor text none true)

example : parsesChecksummed = true := by native_decide
example : !succeeds (parseOutputDescriptor "wsh(1)" none true) = true := by native_decide
example : !succeeds (parseOutputDescriptor "wsh(1)#aaaaaaaa") = true := by native_decide
example : !succeeds (parseOutputDescriptor "wsh(1)#") = true := by native_decide
example : !succeeds (parseOutputDescriptor "wsh(1)##aaaaaaaa") = true := by native_decide
example : !succeeds (parseOutputDescriptor "wsh(☃)") = true := by native_decide

-- Checksum verification happens before wrapper parsing and observes whitespace.
example :
    (match parseOutputDescriptor "unsupported(1)#aaaaaaaa" with
    | .error message => message == "descriptor checksum mismatch"
    | .ok _ => false) = true := by native_decide

private def checksumBindsText : Bool :=
  match DescriptorChecksum.checksum "wsh(1)" with
  | .error _ => false
  | .ok checksum => !succeeds (parseOutputDescriptor ("wsh( 1)#" ++ checksum))

example : checksumBindsText = true := by native_decide

private def skewTree (depth : Nat) : String :=
  (List.range depth).foldl (fun text _ => "{" ++ text ++ ",1}") "1"

example : succeeds (parseOutputDescriptor ("tr(" ++ xOnly ++ "," ++ skewTree 128 ++ ")")) =
    true := by native_decide
example : !succeeds (parseOutputDescriptor ("tr(" ++ xOnly ++ "," ++ skewTree 129 ++ ")")) =
    true := by native_decide
example : !succeeds (parseOutputDescriptor
    ("wsh(" ++ String.ofList (List.replicate 2000 '(') ++ "1)")) = true := by native_decide
example : !succeeds (parseOutputDescriptor
    ("wsh(" ++ String.ofList (List.replicate 403 'n') ++ ":1)")) = true := by native_decide

end LeanMiniscript.Miniscript.DescriptorParserExamples
