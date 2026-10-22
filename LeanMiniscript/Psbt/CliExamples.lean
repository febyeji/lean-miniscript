import LeanMiniscript.Psbt.Cli
import LeanMiniscript.Psbt.RoleSupport

namespace LeanMiniscript.Psbt.CliExamples

open LeanMiniscript.Bitcoin LeanMiniscript.Script RoleSupport

private def descriptors : List (Nat × String) := [
  (0, "sh(multi(2,029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f,02dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d7))"),
  (1, "sh(wsh(multi(2,03089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc,023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e73)))")]

-- Move the BIP174 role vector's signed inputs to a v2 PSBT of the same
-- transaction. Its signatures must still verify after v2 reconstruction.
private def signedV2 : Except String Psbt := do
  let tx ← (decodedOf (role 5)).unsignedTransaction.mapError (fun error => s!"{repr error}")
  let base ← (Psbt.createV2 tx).mapError (fun error => s!"{repr error}")
  return { base with inputs := base.inputs.zipWith (· ++ ·) (role 5).inputs }

private def finalizeV2 : Except String Bool := do
  let psbt ← signedV2
  let encoded ← Cli.execute (.finalize .hex (byteArrayHex psbt.serialize) descriptors)
  let result ← Cli.parsePsbt .base64 encoded
  let before ← psbt.decode.mapError (fun error => s!"{repr error}")
  let after ← result.decode.mapError (fun error => s!"{repr error}")
  let originalTx ← before.unsignedTransaction.mapError (fun error => s!"{repr error}")
  let finalTx ← after.unsignedTransaction.mapError (fun error => s!"{repr error}")
  let originalUtxos ← before.spentOutputs.mapError (fun error => s!"{repr error}")
  let finalUtxos ← after.spentOutputs.mapError (fun error => s!"{repr error}")
  let tx ← Cli.execute (.extract .base64 encoded)
  return after.global.psbtVersion == 2 &&
    serializeTransaction originalTx == serializeTransaction finalTx &&
    originalUtxos.map serializeTxOutput == finalUtxos.map serializeTxOutput &&
    tx == byteArrayHex (roleBytes 7)

example : (match finalizeV2 with | .ok success => success | .error _ => false) = true := by
  native_decide

end LeanMiniscript.Psbt.CliExamples
