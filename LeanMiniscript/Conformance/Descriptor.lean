import LeanMiniscript.Miniscript.DescriptorParser
import LeanMiniscript.Miniscript.OutputDescriptor

namespace LeanMiniscript.Conformance.Descriptor

open LeanMiniscript.Miniscript

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87

private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []

private def hex (text : String) : ByteArray :=
  ⟨(decodeHex text.toUTF8.data.toList).toArray⟩

private def compressed : PubKey := PubKey.ofBytes
  (hex "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")

private def uncompressed : PubKey := PubKey.ofBytes
  (hex "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")

private def matchesScript (descriptor : OutputDescriptor) (script : String) : Bool :=
  match compileOutputDescriptor descriptor with
  | .ok result => result.scriptPubKey == hex script
  | .error _ => false

example : matchesScript (.pk compressed)
    "210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798ac" = true := by
  native_decide

example : matchesScript (.pkh compressed)
    "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac" = true := by
  native_decide

example : matchesScript (.pk uncompressed)
    "410479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8ac" = true := by
  native_decide

example : matchesScript (.wpkh compressed)
    "0014751e76e8199196d454941c45d1b3a323f1433bd6" = true := by
  native_decide

example : matchesScript (.sh (.pk compressed))
    "a91423b0ad3477f2178bc0b3eed26e4e6316f4e83aa187" = true := by
  native_decide

example : matchesScript (.sh (.pkh compressed))
    "a914cd7b44d0b03f2d026d1e586d7ae18903b0d385f687" = true := by
  native_decide

example : matchesScript (.raw (hex "51")) "51" = true := by
  native_decide

example : (match deriveOutputDescriptor s!"sh(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798))" with
    | .ok result => result.scriptPubKey == hex "a91423b0ad3477f2178bc0b3eed26e4e6316f4e83aa187"
    | .error _ => false) = true := by
  native_decide

end LeanMiniscript.Conformance.Descriptor
