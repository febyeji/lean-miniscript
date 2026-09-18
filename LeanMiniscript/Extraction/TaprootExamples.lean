import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Extraction.Taproot

namespace LeanMiniscript.Extraction
open LeanMiniscript.Script LeanMiniscript.Bitcoin
private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def key := hex "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9"
private def control := hex "c02f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"
private def program := hex "5120bf6cf4c0026f57cab510d2014e34e8bad549e5370ed343b1e333fc5a3b066413"
private def signature := hex "8c05c0ee555979c2de9025bc3664cb322783a198339d3d458c3d73b4364f235444e98c7661e6010ac1ffbb07a2c68f87a407ac4f089a5dd1ff88574524a53a48"
private def script : Script := [.pushData key, .op .OP_CHECKSIG]
private def scriptBytes := hex "20" ++ key ++ hex "ac"
private def prevouts := sighashFixtureSpentOutputs.modify 0 (fun output => { output with scriptPubKey := program })
private def fullWitness := [signature, scriptBytes, control]
private def run (witness : List ByteArray) (spent : Array TxOutput := prevouts)
    (tx : Transaction := sighashFixtureTransaction) : Except TaprootScriptPathError WeightedResult :=
  execCommittedTapscriptTransaction CryptoOracle.pureLeanSchnorr script witness {} tx spent 0
private def success : Except TaprootScriptPathError WeightedResult → Bool
  | .ok (.success [top] _ _) => top.data == trueElement.data
  | _ => false
private def errorIs (expected : TaprootScriptPathError) : Except TaprootScriptPathError WeightedResult → Bool
  | .error error => error == expected
  | _ => false
private def scriptErrorIs (expected : ScriptError) : Except TaprootScriptPathError WeightedResult → Bool
  | .ok (.failure error) => error == expected
  | _ => false
private def flip (bytes : ByteArray) (index : Nat) : ByteArray :=
  ⟨bytes.data.set! index (bytes[index]! ^^^ 1)⟩
-- Complete wire-witness commitment, actual transaction digest and real signature.
example : success (run fullWitness) = true := by native_decide
example : (match run fullWitness with
  | .ok (.success _ _ remaining) => remaining == initialValidationWeight fullWitness - 50
  | _ => false) = true := by native_decide
example : (match parseTapscriptWitness fullWitness with
  | .ok witness => witness.fullWitness == fullWitness
  | _ => false) = true := by native_decide
private def annexWitness := [hex "35cc69fbeb571616eff22e2372add7bc7f9028744431757baeb6dd257a41e17a6f2d66a4bf532402c964fdee6728664cffb963159121a76ea648dbb232677ccd", scriptBytes, control, hex "500102"]
example : success (run annexWitness) = true := by native_decide
example : (match parseTapscriptWitness annexWitness with
  | .ok witness => witness.fullWitness == annexWitness && witness.annex.isSome
  | _ => false) = true := by native_decide
example : (match parseTapscriptWitness [hex "50"] with
  | .error .keyPathUnsupported => true
  | _ => false) = true := by native_decide
example : errorIs .keyPathUnsupported (run [signature, hex "50"]) = true := by native_decide
example : errorIs .emptyWitness (run []) = true := by native_decide
example : errorIs (.control .controlSize) (run [signature, scriptBytes, control.extract 0 32]) = true := by native_decide
example : errorIs (.control .commitmentMismatch) (run [signature, scriptBytes, flip control 0]) = true := by native_decide
example : errorIs (.control .commitmentMismatch) (run [signature, scriptBytes ++ hex "00", control]) = true := by native_decide
example : errorIs (.control .commitmentMismatch) (run fullWitness
  (prevouts.modify 0 (fun output => { output with scriptPubKey := flip program 5 }))) = true := by native_decide
example : scriptErrorIs .schnorrSig (run [flip signature 40, scriptBytes, control]) = true := by native_decide
example : scriptErrorIs .schnorrSig (run fullWitness prevouts
  { sighashFixtureTransaction with locktime := sighashFixtureTransaction.locktime + 1 }) = true := by native_decide
example : scriptErrorIs .schnorrSig (run (fullWitness ++ [hex "500102"])) = true := by native_decide
example : errorIs .notNativeP2TR (run fullWitness
  (prevouts.modify 0 (fun output => { output with scriptPubKey := hex "0020" ++ program.extract 2 34 }))) = true := by native_decide
example : errorIs .nonemptyScriptSig (run fullWitness prevouts
  { sighashFixtureTransaction with
    inputs := sighashFixtureTransaction.inputs.modify 0
      (fun input => { input with scriptSig := hex "51" }) }) = true := by native_decide
example : errorIs (.context .spentOutputCount) (run fullWitness #[]) = true := by native_decide
example : (match execCommittedTapscriptTransaction CryptoOracle.pureLeanSchnorr [.pushNum 1] fullWitness {}
    sighashFixtureTransaction prevouts 0 with
  | .ok (.failure .tapscriptWitnessScript) => true
  | _ => false) = true := by native_decide
private def futureControl := hex "fa2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"
private def futurePrevouts := prevouts.modify 0 (fun output => { output with scriptPubKey := hex "5120e4d8be4b287860f791051fc10f316c45926819a97b070f238c68758b6dba5e7b" })
example : errorIs (.leafVersionUnsupported 0xfa) (run [hex "51", futureControl] futurePrevouts) = true := by native_decide
example : errorIs (.control .commitmentMismatch) (run [hex "51", flip futureControl 0] futurePrevouts) = true := by native_decide

-- Final acceptance uses the same real commitment, digest and Schnorr signature.
local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := by
  intro a b
  cases a <;> cases b
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)
private def verify (witness : List ByteArray) (flags : ScriptFlags := {}) :
    Except TaprootVerificationError Nat :=
  verifyCommittedTapscriptTransaction CryptoOracle.pureLeanSchnorr script witness flags
    sighashFixtureTransaction prevouts 0
example : verify fullWitness = .ok (initialValidationWeight fullWitness - 50) := by native_decide
example : verify annexWitness = .ok (initialValidationWeight annexWitness - 50) := by native_decide
example : verify [ByteArray.empty, scriptBytes, control] = .error (.script .evalFalse) := by native_decide
example : verify (ByteArray.empty :: fullWitness) = .error (.script .cleanStack) := by native_decide
example : verify [flip signature 40, scriptBytes, control] = .error (.script .schnorrSig) := by native_decide
example : verify fullWitness { minimalIf := false } = .error (.script .tapscriptFlags) := by native_decide
private def oversized : ByteArray := ⟨Array.replicate 521 1⟩
private def tooMany := List.replicate 1001 oversized ++ [scriptBytes, control]
-- Initial limits precede signatures; count precedes element size.
example : verify [oversized, scriptBytes, control] = .error (.script .pushSize) := by native_decide
example : verify tooMany = .error (.script .stackSize) := by native_decide
example : scriptErrorIs .stackSize (run tooMany) = true := by native_decide
-- Commitment errors precede flag-contract and initial-limit errors.
example : verify [oversized, scriptBytes, flip control 0] =
    .error (.setup (.control .commitmentMismatch)) := by native_decide
example : verify [signature, scriptBytes, flip control 0] { minimalIf := false } =
    .error (.setup (.control .commitmentMismatch)) := by native_decide
example : (match verifyCommittedTapscriptTransaction CryptoOracle.pureLeanSchnorr [.pushNum 1]
    (List.replicate 1001 oversized ++ [hex "51", futureControl]) {}
    sighashFixtureTransaction futurePrevouts 0 with
  | .error (.setup (.leafVersionUnsupported 0xfa)) => true
  | _ => false) = true := by native_decide
end LeanMiniscript.Extraction
