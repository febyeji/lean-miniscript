import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Extraction.TaprootTransaction
import LeanMiniscript.Bitcoin.TaprootSighashExamples

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin
open LeanMiniscript.TestSupport (hex)

private def scriptPathOutput :=
  hex "5120bf6cf4c0026f57cab510d2014e34e8bad549e5370ed343b1e333fc5a3b066413"
private def scriptPathControl :=
  hex "c02f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"
private def scriptPathScript :=
  hex "20f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9ac"
private def scriptPathSignature :=
  hex "8c05c0ee555979c2de9025bc3664cb322783a198339d3d458c3d73b4364f235444e98c7661e6010ac1ffbb07a2c68f87a407ac4f089a5dd1ff88574524a53a48"
private def annexScriptPathSignature :=
  hex "35cc69fbeb571616eff22e2372add7bc7f9028744431757baeb6dd257a41e17a6f2d66a4bf532402c964fdee6728664cffb963159121a76ea648dbb232677ccd"
private def scriptPathPrevouts := sighashFixtureSpentOutputs.modify 0
  (fun output => { output with scriptPubKey := scriptPathOutput })
private def taprootFlags : CoreVerificationFlags :=
  { witness := true, taproot := true, cleanStack := true }

private def acceptSchnorr : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)

private def rejectSchnorr : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => false)

private def keyPathSignature : ByteArray := ⟨Array.replicate 64 1⟩

private def verify (oracle : CryptoOracle) (witness : List ByteArray)
    (scriptPubKey : ByteArray := scriptPathOutput)
    (spentOutputs : Array TxOutput := scriptPathPrevouts)
    (flags : CoreVerificationFlags := taprootFlags) :
    Except CoreVerificationError Unit :=
  verifyNativeTaprootTransaction oracle flags sighashFixtureTransaction
    spentOutputs 0 ByteArray.empty scriptPubKey witness

-- Key-path spends use the transaction-backed BIP341 digest and the output key
-- as the Schnorr public key. The callback is accepting here so the dispatch and
-- sighash path can be tested without introducing another signing fixture.
example : verify acceptSchnorr [keyPathSignature] = .ok () := by native_decide
example : verify acceptSchnorr [keyPathSignature, hex "500102"] = .ok () := by native_decide
example : verify rejectSchnorr [keyPathSignature] = .error (.script .schnorrSig) := by
  native_decide
example : verify acceptSchnorr [keyPathSignature.extract 0 63] =
    .error (.script .schnorrSigSize) := by native_decide
example : verify acceptSchnorr [keyPathSignature ++ hex "00"] =
    .error (.script .schnorrSigHashType) := by native_decide

-- Script-path spends share the same entry point and retain the real BIP340,
-- control-block, annex, and Tapscript execution checks.
example : verify CryptoOracle.pureLeanSchnorr
    [scriptPathSignature, scriptPathScript, scriptPathControl] = .ok () := by
  native_decide
example : verify CryptoOracle.pureLeanSchnorr
    [annexScriptPathSignature, scriptPathScript, scriptPathControl, hex "500102"] =
    .ok () := by native_decide

private def encodeBE32 (value : Nat) : ByteArray :=
  ⟨((List.range 32).map (fun i => UInt8.ofNat (value / 256 ^ (31 - i) % 256))).toArray⟩

private def futureInternalKey :=
  hex "2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"

private def committedFixture (leafVersion : UInt8) (script : ByteArray) : ByteArray × ByteArray :=
  match taprootTweakPoint futureInternalKey
      (taggedHash "TapTweak" (futureInternalKey ++ tapleafHash script leafVersion)) with
  | .ok (x, y) =>
      (hex "5120" ++ encodeBE32 x,
        ⟨#[UInt8.ofNat (leafVersion.toNat + y % 2)]⟩ ++ futureInternalKey)
  | .error _ => (ByteArray.empty, ByteArray.empty)

-- The raw witness entry point accepts upgradeable leaf versions according to
-- Core's policy flags and treats OP_SUCCESSx as immediate success.
example : let (output, control) := committedFixture 0xfa (hex "51")
  verify acceptSchnorr [hex "51", control] output
    (scriptPathPrevouts.modify 0 (fun item => { item with scriptPubKey := output })) = .ok () := by
  native_decide
example : let (output, control) := committedFixture 0xc0 (hex "50")
  verify acceptSchnorr [hex "50", control] output
    (scriptPathPrevouts.modify 0 (fun item => { item with scriptPubKey := output })) = .ok () := by
  native_decide
example : let (output, control) := committedFixture 0xc0 (hex "50")
  verify acceptSchnorr [hex "50", control] output
    (scriptPathPrevouts.modify 0 (fun item => { item with scriptPubKey := output }))
    { taprootFlags with discourageOpSuccess := true } = .error .discourageOpSuccess := by
  native_decide

end LeanMiniscript.Extraction
