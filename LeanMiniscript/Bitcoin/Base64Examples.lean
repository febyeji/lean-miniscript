import LeanMiniscript.Bitcoin.Base64

namespace LeanMiniscript.Bitcoin.Base64

/-! RFC4648 section 10 test vectors and strict-decoding rejections. The PSBT
examples additionally check every BIP174/BIP370/BIP371 Base64 string. -/

private def vectors : List (String × String) :=
  [("", ""), ("f", "Zg=="), ("fo", "Zm8="), ("foo", "Zm9v"), ("foob", "Zm9vYg=="),
   ("fooba", "Zm9vYmE="), ("foobar", "Zm9vYmFy")]

example : vectors.all (fun (plain, encoded) =>
    encode plain.toUTF8 == encoded && decode encoded == some plain.toUTF8) = true := by
  native_decide

-- All byte values survive encoding, including both non-alphanumeric symbols.
example : decode (encode ⟨(List.range 256).toArray.map UInt8.ofNat⟩) ==
    some ⟨(List.range 256).toArray.map UInt8.ofNat⟩ := by native_decide
example : encode ⟨#[0xfb, 0xff]⟩ = "+/8=" := by native_decide

-- Missing padding, misplaced padding, nonzero pad bits, whitespace and
-- characters outside the alphabet are rejected.
example : ["Zg", "Zg=", "Z===", "Zg==Zg==", "Zh==", "Zm9=", "Zm9v\n", "Zm-v", "Zm_v", "===="].all
    (fun text => (decode text).isNone) = true := by native_decide

end LeanMiniscript.Bitcoin.Base64
