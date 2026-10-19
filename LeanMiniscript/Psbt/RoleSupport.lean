import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Psbt.Roles
import LeanMiniscript.Psbt.Fixtures

namespace LeanMiniscript.Psbt.RoleSupport

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open LeanMiniscript.Psbt.Fixtures

/-- Decode fixture hex shared by the PSBT role conformance modules. -/
def hex (text : String) : ByteArray := TestSupport.hex text

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
