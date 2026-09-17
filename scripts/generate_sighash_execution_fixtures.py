from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode = True
import json

import argparse
parser=argparse.ArgumentParser(description='Regenerate transaction-backed Script sighash execution fixtures from the same pinned official/Core sources.')
parser.add_argument('--wallet-vectors', type=Path, required=True)
parser.add_argument('--core-script', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args=parser.parse_args()
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('fixture_generator', root/'scripts/generate_taproot_sighash_fixtures.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.generate(args.wallet_vectors, args.core_script)  # Verify source digests and official vectors.
group=json.loads(args.wallet_vectors.read_text())['keyPathSpending'][0]
tx=g.parse_transaction(group['given']['rawUnsignedTx'])
spent=[g.make_output(u['amountSats'],bytes.fromhex(u['scriptPubKey'])) for u in group['given']['utxosSpent']]
ref=g.reference_functions(args.core_script.read_text())
leaf=b'\x20'+bytes([2])*32+b'\xac'
twice=leaf+b'\x6b'+leaf
expected={mode:ref['TaprootSignatureHash'](tx,spent,mode,0,scriptpath=True,leaf_script=leaf,codeseparator_pos=0xffffffff).hex() for mode in [0,1,2,3,129,130,131]}
double={mode:ref['TaprootSignatureHash'](tx,spent,mode,0,scriptpath=True,leaf_script=twice,codeseparator_pos=0xffffffff).hex() for mode in [1,2]}
annex=ref['TaprootSignatureHash'](tx,spent,0,0,scriptpath=True,leaf_script=leaf,codeseparator_pos=0xffffffff,annex=b'\x50\x01\x02').hex()
path=args.output
text='''import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Extraction.RefInterp

namespace LeanMiniscript.Script
open LeanMiniscript.Bitcoin

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def key : ByteArray := ⟨Array.replicate 32 2⟩
private def sig (mode : UInt8) (marker : UInt8 := 3) : ByteArray :=
  ⟨Array.replicate 64 marker⟩ ++ if mode == 0 then ByteArray.empty else ⟨#[mode]⟩
private def script : Script := [.pushData key, .op .OP_CHECKSIG]
private def witness (mode : UInt8) : TapscriptWitness :=
  { arguments := [sig mode], scriptBytes := ⟨#[32]⟩ ++ key ++ ⟨#[0xac]⟩,
    controlBlock := ⟨Array.replicate 33 0xc0⟩ }
private def flags : ScriptFlags := {}
private def success : WeightedResult → Bool
  | .success [top] _ _ => top.data == trueElement.data
  | _ => false
private def errorIs (expected : ScriptError) : WeightedResult → Bool
  | .failure error => error == expected
  | _ => false
private def hashErrorIs (expected : SighashError) : Except SighashError ByteArray → Bool
  | .error error => error == expected
  | _ => false
private def digestEqual (a b : Except SighashError ByteArray) : Bool :=
  match a, b with
  | .ok x, .ok y => x.data == y.data
  | _, _ => false
private def expectedOracle (digest : String) : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false)
    (fun signature pubkey message => signature.size == 64 && pubkey.size == 32 && message.data == (hex digest).data)

-- Constants generated from the pinned Core signing-message function.
private def executionFixtures : List (UInt8 × String) := [
'''
text+='\n'.join(f'  ({mode}, "{digest}"),' for mode,digest in expected.items())+'\n]\n'
text+='''example : executionFixtures.all (fun (mode, digest) => success
  (LeanMiniscript.Extraction.execTapscriptTransaction (expectedOracle digest) script
    (witness mode) flags sighashFixtureTransaction sighashFixtureSpentOutputs 0)) = true := by native_decide

-- The full witness overrides stale caller annex/leaf/codesep metadata.
'''
text+=f'''example : success (match TxContext.fromTaproot {{ sighashFixtureContext with
    annex := some ⟨#[0x50]⟩, spendPath := .scriptPath ⟨#[0]⟩ 0xc0 7 }} with
  | .error _ => .failure .schnorrSigHashType
  | .ok ctx => evaluateTapscript (expectedOracle "{expected[0]}") script (witness 0) flags
      {{ ctx with version := -1, locktime := 0, sequence := 0, sigHash := ⟨#[0xff]⟩ }}) = true := by native_decide
example : success (LeanMiniscript.Extraction.execTapscriptTransaction
  (expectedOracle "{annex}") script {{ witness 0 with annex := some ⟨#[0x50, 1, 2]⟩ }}
  flags sighashFixtureTransaction sighashFixtureSpentOutputs 0) = true := by native_decide

-- Two signatures in the same script select different transaction hashes.
private def twiceScript : Script := script ++ [.op .OP_TOALTSTACK] ++ script
private def twiceWitness : TapscriptWitness :=
  {{ arguments := [sig 2 4, sig 1 3], scriptBytes := (witness 0).scriptBytes ++ ⟨#[0x6b]⟩ ++ (witness 0).scriptBytes,
    controlBlock := (witness 0).controlBlock }}
private def twiceOracle : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
  (fun signature _ message => signature.size == 64 &&
    if signature[0]! == 3 then message.data == (hex "{double[1]}").data
    else message.data == (hex "{double[2]}").data)
example : (match LeanMiniscript.Extraction.execTapscriptTransaction twiceOracle twiceScript twiceWitness
    flags sighashFixtureTransaction sighashFixtureSpentOutputs 0 with
  | .success [top] [saved] remaining => top = trueElement && saved = trueElement && remaining == 187
  | _ => false) = true := by native_decide
'''
text+='''
example : (List.range 256).all (fun n =>
  validTaprootHashType (UInt8.ofNat n) == ([0, 1, 2, 3, 129, 130, 131].contains n)) = true := by native_decide
example : (List.range 256).all (fun n => validTaprootHashType (UInt8.ofNat n) ||
  hashErrorIs .invalidHashType (taprootSignatureHash sighashFixtureContext (UInt8.ofNat n))) = true := by native_decide
example : hashErrorIs .inputIndex (taprootSignatureHash
  { sighashFixtureContext with inputIndex := 100 } 0) = true := by native_decide
example : hashErrorIs .spentOutputCount (taprootSignatureHash
  { sighashFixtureContext with spentOutputs := #[] } 0) = true := by native_decide
example : hashErrorIs .invalidAnnex (taprootSignatureHash
  { sighashFixtureContext with annex := some ByteArray.empty } 0) = true := by native_decide
example : hashErrorIs .invalidAnnex (taprootSignatureHash
  { sighashFixtureContext with annex := some ⟨#[0]⟩ } 0) = true := by native_decide
example : hashErrorIs .invalidLeafVersion (taprootSignatureHash
  { sighashFixtureContext with spendPath := .scriptPath ⟨#[0x51]⟩ 0xc1 4294967295 } 0) = true := by native_decide
private def noOutputs : Transaction := { sighashFixtureTransaction with outputs := #[] }
example : hashErrorIs .missingSingleOutput (taprootSignatureHash
  { sighashFixtureContext with transaction := noOutputs } 3) = true := by native_decide
example : hashErrorIs .missingSingleOutput (taprootSignatureHash
  { sighashFixtureContext with transaction := noOutputs } 0x83) = true := by native_decide
example : errorIs .schnorrSigHashType (LeanMiniscript.Extraction.execTapscriptTransaction
  (CryptoOracle.pureLeanHashes (fun _ _ _ => true) (fun _ _ _ => true)) script (witness 3)
  flags noOutputs sighashFixtureSpentOutputs 0) = true := by native_decide
-- Unknown key versions bypass signature hashing and SINGLE availability.
example : success (LeanMiniscript.Extraction.execTapscriptTransaction
  (CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => false))
  [.pushNum 2, .op .OP_CHECKSIG]
  { arguments := [sig 3], scriptBytes := ⟨#[0x52, 0xac]⟩, controlBlock := (witness 3).controlBlock }
  flags noOutputs sighashFixtureSpentOutputs 0) = true := by native_decide
-- A rejected verifier is distinct from a hashing error.
example : errorIs .schnorrSig (LeanMiniscript.Extraction.execTapscriptTransaction
  (CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => false)) script (witness 0)
  flags sighashFixtureTransaction sighashFixtureSpentOutputs 0) = true := by native_decide
-- NONE excludes outputs; ALL includes them. scriptSig is never committed.
example : digestEqual (taprootSignatureHash sighashFixtureContext 2)
  (taprootSignatureHash { sighashFixtureContext with transaction := noOutputs } 2) = true := by native_decide
example : digestEqual (taprootSignatureHash sighashFixtureContext 1)
  (taprootSignatureHash { sighashFixtureContext with transaction := noOutputs } 1) = false := by native_decide
example : digestEqual (taprootSignatureHash sighashFixtureContext 0)
  (taprootSignatureHash sighashFixtureContext 1) = false := by native_decide
private def changedScriptSig : Transaction := { sighashFixtureTransaction with
  inputs := sighashFixtureTransaction.inputs.modify 0 (fun input => { input with scriptSig := ⟨#[0x51]⟩ }) }
example : digestEqual (taprootSignatureHash sighashFixtureContext 0)
  (taprootSignatureHash { sighashFixtureContext with transaction := changedScriptSig } 0) = true := by native_decide
private def changedOtherInput : Transaction := { sighashFixtureTransaction with
  inputs := sighashFixtureTransaction.inputs.modify 1 (fun input => { input with sequence := 0 }) }
private def changedOtherSpent : Array TxOutput := sighashFixtureSpentOutputs.modify 1
  (fun output => { output with amount := output.amount + 1 })
example : digestEqual (taprootSignatureHash sighashFixtureContext 0x81)
  (taprootSignatureHash { sighashFixtureContext with
    transaction := changedOtherInput
    spentOutputs := changedOtherSpent } 0x81) = true := by native_decide
example : digestEqual (taprootSignatureHash sighashFixtureContext 1)
  (taprootSignatureHash { sighashFixtureContext with
    transaction := changedOtherInput
    spentOutputs := changedOtherSpent } 1) = false := by native_decide
example : ({ sighashFixtureTransaction with version := 4294967295 }).signedVersion = -1 := by native_decide
example : (match TxContext.fromTaproot sighashFixtureContext with
  | .error _ => false
  | .ok ctx => ctx.version == sighashFixtureTransaction.signedVersion &&
      ctx.locktime == sighashFixtureTransaction.locktime.toNat &&
      ctx.sequence == (sighashFixtureTransaction.inputs[0]!).sequence.toNat && ctx.taproot.isSome) = true := by native_decide

end LeanMiniscript.Script
'''
path.write_text(text)
