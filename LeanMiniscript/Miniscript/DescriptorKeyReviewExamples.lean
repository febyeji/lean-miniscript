import LeanMiniscript.Miniscript.DescriptorKey

namespace LeanMiniscript.Miniscript.DescriptorKeyReview

open LeanMiniscript.Miniscript

/-! BIP 380 key-expression vectors from
https://github.com/bitcoin/bips/blob/master/bip-0380.mediawiki
Source SHA-256: 34e6510bb2eba9445a68eacf3d24d5a4e5f24481477488d5552f674ac81dd5fe.
The parser accepts hardened xpub paths as syntax; resolution requires private material. -/

private def succeeds {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private def validExpressions : Array String := #[
  "0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "04a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd5b8dec5235a0fa8722476c7709c02559e3aa73aa03918ba2d492eea75abea235",
  "[deadbeef/0h/0h/0h]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0'/0'/0']0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0'/0h/0']0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "5KYZdUEo39z3FPrtuX2QbbwGnNP5zTd7yyr2SC1j299sBCnWjss",
  "L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1",
  "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL",
  "[deadbeef/0h/1h/2h]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL",
  "[deadbeef/0h/1h/2h]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/3/4/5",
  "[deadbeef/0h/1h/2h]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/3/4/5/*",
  "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/3h/4h/5h/*",
  "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/3h/4h/5h/*h",
  "[deadbeef/0h/1h/2]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/3h/4h/5h/*h",
  "xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc",
  "[deadbeef/0h/1h/2h]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc",
  "[deadbeef/0h/1h/2h]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3/4/5",
  "[deadbeef/0h/1h/2h]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3/4/5/*",
  "xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3h/4h/5h/*",
  "xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3h/4h/5h/*h",
  "[deadbeef/0h/1h/2]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3h/4h/5h/*h"]

private def invalidExpressions : Array String := #[
  "[deadbeef/0h/0h/0h/*]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0h/0h/0h/]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbef/0h/0h/0h]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeeef/0h/0h/0h]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0f/0f/0f]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/-0/-0/-0]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0H/0H/0H]0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600",
  "[deadbeef/0h/1h/2]xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc/3H/4h/5h/*H",
  "L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1/0",
  "L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1/*",
  "xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U/2147483648",
  "xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U/1aa",
  "[aaaaaaaa][aaaaaaaa]xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U/2147483647'/0",
  "aaaaaaaa]xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U/2147483647'/0",
  "[gaaaaaaa]xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U/2147483647'/0",
  "[deadbeef]"]

example : validExpressions.size = 21 := by native_decide
example : invalidExpressions.size = 16 := by native_decide
example : validExpressions.all (fun text => succeeds (parseDescriptorKey text)) = true := by
  native_decide
example : invalidExpressions.all (fun text => !succeeds (parseDescriptorKey text)) = true := by
  native_decide

private def extendedPublic : String := "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL"
private def extendedPrivate : String := "xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc"
private def compressed : String := "0260b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600"
private def uncompressed : String := "04a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd5b8dec5235a0fa8722476c7709c02559e3aa73aa03918ba2d492eea75abea235"
private def uncompressedWIF : String := "5KYZdUEo39z3FPrtuX2QbbwGnNP5zTd7yyr2SC1j299sBCnWjss"
private def compressedWIF : String := "L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1"

private def resolvesTo (text expected : String) (index : Option Nat := none) : Bool :=
  match resolveDescriptorKey index text with
  | .ok key => LeanMiniscript.Script.byteArrayHex key.bytes == expected
  | .error _ => false

private def parsesTo (context : ScriptContext) (input expected : String)
    (index : Option Nat := none) : Bool :=
  match parseSurfaceDescriptor context input index with
  | .ok fragment => prettySurface fragment == expected
  | .error _ => false

-- Origins describe the supplied key and do not trigger another derivation.
example : resolvesTo ("[DEADBEEF/2147483647h/1']" ++ compressed) compressed = true := by
  native_decide
example :
    (match parseDescriptorKey ("[DEADBEEF/2147483647h/1']" ++ compressed) with
    | .ok key => match key.origin with
      | some origin =>
          LeanMiniscript.Script.byteArrayHex origin.fingerprint == "deadbeef" &&
          origin.path == [.hardened 2147483647, .hardened 1]
      | none => false
    | .error _ => false) = true := by native_decide

private def malformedOrigins : Array String := #[
  "[]", "[", "[deadbeef", "deadbeef]", "[[deadbeef]]", "[deadbeef][deadbeef]",
  "[deadbeef/]", "[deadbeef//0]", "[deadbeef/*h]", "[deadbeef/2147483648h]",
  "[deadbeef/4294967295]", "[deadbeef/+1]", "[deadbeef/-1]", "[deadbeef/1_0]",
  "[deadbeef/1.0]", "[deadbeef/0x10]", "[deadbeef/1hh]", "[deadbeef/1'h]",
  "[deadbeef/١]", "[deadbeef/１]", "[deadbeef/0\n]", "[deadbeef/0 ]"]
example : malformedOrigins.all (fun origin =>
    !succeeds (parseDescriptorKey (origin ++ compressed))) = true := by native_decide

private def malformedSuffixes : Array String := #[
  "/", "//0", "/0/", "/*/0", "/*/*", "/*h/1", "/*hh", "/*H", "/**",
  "/2147483648", "/2147483648h", "/4294967295h", "/-1", "/+1", "/0x10",
  "/1_0", "/1.0", "/h", "/'", "/1H", "/1'h", "/1hh", "/١", "/１", "/0\n"]
example : malformedSuffixes.all (fun suffix =>
    !succeeds (parseDescriptorKey (extendedPublic ++ suffix))) = true := by native_decide

example : !succeeds (parseDescriptorKey (compressed ++ "/0")) = true := by native_decide
example : !succeeds (parseDescriptorKey (compressed ++ "/*")) = true := by native_decide
example : !succeeds (parseDescriptorKey (uncompressedWIF ++ "/0h")) = true := by native_decide
example : !succeeds (parseDescriptorKey (" " ++ compressed)) = true := by native_decide
example : !succeeds (parseDescriptorKey (compressed ++ "\t")) = true := by native_decide

-- SEC1 shape alone does not establish curve membership. Hybrid encodings are
-- excluded from descriptor syntax even when they describe a valid curve point.
private def invalidCurveKeys : Array String := #[
  "020000000000000000000000000000000000000000000000000000000000000007",
  "02fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
  "0000000000000000000000000000000000000000000000000000000000000000",
  "0679be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8",
  "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b9"]
example : invalidCurveKeys.all (fun key => !succeeds (parseDescriptorKey key)) = true := by
  native_decide

example : succeeds (parseDescriptorKey (extendedPublic ++ "/0h/*'")) = true := by
  native_decide
example : !succeeds (resolveDescriptorKey (some 0) (extendedPublic ++ "/0h/*'")) = true := by
  native_decide
example : !succeeds (resolveDescriptorKey none (extendedPublic ++ "/*")) = true := by
  native_decide
example : !succeeds (resolveDescriptorKey (some 2147483648) (extendedPublic ++ "/*")) = true := by
  native_decide
example : !succeeds (resolveDescriptorKey (some 2147483648) (extendedPrivate ++ "/*h")) = true := by
  native_decide

-- Frozen cross-checks from Python's HMAC-SHA512 and cryptography/OpenSSL's
-- secp256k1 point generation, starting from the published BIP 380 xprv.
example : resolvesTo (extendedPublic ++ "/3/4/5/*")
    "023853242d8e41d3e5aa7ab185d260eed57a38b0155340a06eeb36af80092a02b5"
    (some 7) = true := by native_decide
example : resolvesTo (extendedPrivate ++ "/3/4/5/*")
    "023853242d8e41d3e5aa7ab185d260eed57a38b0155340a06eeb36af80092a02b5"
    (some 7) = true := by native_decide
example : resolvesTo (extendedPrivate ++ "/3h/4/5'/*h")
    "02ca2a63a599bde5c9aaa0bd5942186e381e1bb25269aa4e397165162947e4ca90"
    (some 11) = true := by native_decide
example : resolvesTo (extendedPublic ++ "/*")
    "0399b07863efb2d8f9db864289a2c1dd4fa0f44951801cd04b81d49e6376c8df95"
    (some 2147483647) = true := by native_decide
example : resolvesTo (extendedPrivate ++ "/*'")
    "0274b642a20ba12e83d280168c35dd6ab05336dded33892dbe927c5ae272997560"
    (some 2147483647) = true := by native_decide

-- Descriptor resolution feeds the existing surface context boundary.
example : parsesTo .p2wsh ("pk([deadbeef/0h]" ++ compressed ++ ")")
    ("pk(" ++ compressed ++ ")") = true := by native_decide
example : parsesTo .tapscript ("pk(" ++ compressed ++ ")")
    "pk(60b2003c386519fc9eadf2b5cf124dd8eea4c4e68d5e154050a9346ea98ce600)" = true := by
  native_decide
example : parsesTo .tapscript ("pk(" ++ compressedWIF ++ ")")
    "pk(a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd)" = true := by
  native_decide
example : parsesTo .p2wsh ("pk(" ++ extendedPublic ++ "/3/4/5/*)")
    "pk(023853242d8e41d3e5aa7ab185d260eed57a38b0155340a06eeb36af80092a02b5)"
    (some 7) = true := by native_decide
example : parsesTo .tapscript ("pk(" ++ extendedPublic ++ "/3/4/5/*)")
    "pk(3853242d8e41d3e5aa7ab185d260eed57a38b0155340a06eeb36af80092a02b5)"
    (some 7) = true := by native_decide

private def contextRejects (context : ScriptContext) (key : String) : Bool :=
  match parseSurfaceDescriptor context ("pk(" ++ key ++ ")") with
  | .error (.keyContext ..) => true
  | _ => false

example : contextRejects .p2wsh uncompressed = true := by native_decide
example : contextRejects .tapscript uncompressed = true := by native_decide
example : contextRejects .p2wsh uncompressedWIF = true := by native_decide
example : contextRejects .tapscript uncompressedWIF = true := by native_decide
example : contextRejects .p2wsh
    "a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd" = true := by
  native_decide

example : parsesTo .tapscript
    "pk(A34B99F22C790C4E36B2B3C2C35A36DB06226E41C692FC82B8B56AC1C540C5BD)"
    "pk(a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd)" = true := by
  native_decide

-- Public AST constructors also pass through validation at resolution time.
private def rejectsInvalidConstructedKeys : Bool :=
  match parseDescriptorKey compressed with
  | .error _ => false
  | .ok key =>
      !succeeds ({ key with derivation := [.normal 0] }.resolve) &&
      !succeeds ({ key with wildcard := .normal }.resolve (some 0)) &&
      !succeeds ({ key with origin := some { fingerprint := ⟨#[0, 1, 2]⟩ } }.resolve) &&
      !succeeds ({ key with origin := some {
        fingerprint := ⟨#[0, 1, 2, 3]⟩, path := [.normal 2147483648] } }.resolve) &&
      !succeeds ({ key with material := .xOnlyPublicKey ⟨#[2]⟩ }.resolve)

example : rejectsInvalidConstructedKeys = true := by native_decide

-- A range index has no effect on a fixed key, including an out-of-range value.
example : resolvesTo compressed compressed (some 2147483648) = true := by native_decide

end LeanMiniscript.Miniscript.DescriptorKeyReview
