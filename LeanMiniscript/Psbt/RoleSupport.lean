import LeanMiniscript.Psbt.Roles
import LeanMiniscript.Psbt.Fixtures

namespace LeanMiniscript.Psbt.RoleSupport

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open LeanMiniscript.Psbt.Fixtures

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87

private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []

/-- Decode fixture hex shared by the PSBT role conformance modules. -/
def hex (text : String) : ByteArray :=
  ⟨(decodeHex text.toUTF8.data.toList).toArray⟩

/-- Decode a serialized PSBT fixture. -/
def psbtOf (bytes : String) : Psbt :=
  match Psbt.parse (hex bytes) with
  | .ok psbt => psbt
  | .error _ => default

/-- Decode one BIP174 role vector by index. -/
def role (index : Nat) : Psbt :=
  psbtOf bip174Roles[index]!.2.1

/-- Serialized bytes for one BIP174 role vector by index. -/
def roleBytes (index : Nat) : ByteArray :=
  hex bip174Roles[index]!.2.1

/-- Decode a PSBT into the role-finalizer representation. -/
def decodedOf (psbt : Psbt) : DecodedPsbt :=
  match psbt.decode with
  | .ok decoded => decoded
  | .error _ => default

end LeanMiniscript.Psbt.RoleSupport
