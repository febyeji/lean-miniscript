import Lean

namespace LeanMiniscript.TestSupport

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48
  else if byte.toNat ≤ 70 then byte.toNat - 55 else byte.toNat - 87

private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []

/-- Decode trusted, even-length fixture hex in either letter case. -/
def hex (text : String) : ByteArray :=
  ⟨(decodeHex text.toUTF8.data.toList).toArray⟩

end LeanMiniscript.TestSupport
