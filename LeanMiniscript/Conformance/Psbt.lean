import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Psbt.RoleSupport

namespace LeanMiniscript.Conformance.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Psbt
open LeanMiniscript.Psbt.RoleSupport

private def legacyMultisigKeys : List PubKey :=
  [PubKey.ofBytes (hex "029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f"),
   PubKey.ofBytes (hex "02dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d7")]

private def shLegacyMultisig : OutputDescriptor :=
  .sh (.core (.multi 2 legacyMultisigKeys))

/-! The official BIP174 legacy P2SH input remains a byte-for-byte conformance
for descriptor finalization and legacy signature hashing. -/

example : (match (role 5).finalizeInput {} 0 shLegacyMultisig with
    | .ok psbt => psbt.inputs[0]! == (role 6).inputs[0]! && psbt.inputs[1]! == (role 5).inputs[1]!
    | .error _ => false) = true := by
  native_decide

end LeanMiniscript.Conformance.Psbt
