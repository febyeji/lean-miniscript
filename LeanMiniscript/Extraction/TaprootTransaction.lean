import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Script.SignatureChecks

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin

private def checkNativeTaprootKeyPath (oracle : CryptoOracle)
    (context : TaprootSigHashContext) : CoreKeyPathChecker :=
  fun signature outputKey annex => do
    (checkSchnorrSignatureEncoding signature).mapError .script
    let signingContext := { context with annex, spendPath := .keyPath }
    let hashType := if signature.size == 65 then signature[64]! else 0
    let digest ← (taprootSignatureHash signingContext hashType).mapError
      (fun _ => CoreVerificationError.script .schnorrSigHashType)
    if oracle.checkSchnorrSig (signature.extract 0 64) outputKey digest then
      return ()
    throw (.script .schnorrSig)

/-- Verify a native P2TR input from its serialized scriptPubKey and witness.

The transaction-backed entry point follows Core's witness-program boundary. It
accepts key-path and script-path witnesses, removes and hashes annexes, checks
Taproot control blocks, honors OP_SUCCESSx and upgradeable leaf versions, and
executes version-`0xc0` Tapscript with the existing raw Script interpreter.
Transaction validity and prevout provenance remain caller obligations, as they
do for the underlying signature-hash context. -/
def verifyNativeTaprootTransaction (oracle : CryptoOracle)
    (flags : CoreVerificationFlags) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray) :
    Except CoreVerificationError Unit := do
  if scriptPubKey.size ≠ 34 || scriptPubKey[0]! ≠ 0x51 || scriptPubKey[1]! ≠ 0x20 then
    throw .witnessProgramMismatch
  let context : TaprootSigHashContext := {
    transaction, spentOutputs, inputIndex }
  let txContext ← (TxContext.fromTaproot context).mapError
    (fun _ => CoreVerificationError.script .schnorrSigHashType)
  let execute := executeCoreScript flags txContext (fun _ _ => oracle)
  let verifyWitness : CoreWitnessVerifier := fun witness version program isP2SH =>
    verifyCoreWitnessProgram execute flags witness version program isP2SH
      (checkNativeTaprootKeyPath oracle context)
  verifyCoreScripts execute verifyWitness flags scriptSig scriptPubKey witness

end LeanMiniscript.Extraction
