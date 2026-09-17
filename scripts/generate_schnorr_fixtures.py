#!/usr/bin/env python3
"""Reproduce offline BIP340 and transaction-backed Schnorr execution fixtures.

Public BIP340 sources are pinned at BIPs commit
55083d36ddebcd2a039135a2f4ee74917a5803d3, paths
bip-0340/test-vectors.csv and bip-0340/reference.py.
Only public, fixed test keys are used to generate signatures; no signing API
is added to Lean. Wallet/Core pins are verified by the existing hash generator.
"""
import argparse
import csv
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

VECTORS_SHA256 = '34c9d1d9c3a88d524bc80778540dc43f8306ec249a7485293063c376db851c2d'
REFERENCE_SHA256 = '4b1d4ad9e60820df4a6d239733d52b014bc03e4c47afd757a2fe4d3b586d892c'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

HEX = """private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
"""

def generate(args):
    assert hashlib.sha256(args.bip340_vectors.read_bytes()).hexdigest() == VECTORS_SHA256
    assert hashlib.sha256(args.bip340_reference.read_bytes()).hexdigest() == REFERENCE_SHA256
    ref = load('bip340_reference', args.bip340_reference)
    rows = list(csv.DictReader(io.StringIO(args.bip340_vectors.read_text())))
    assert [int(row['index']) for row in rows] == list(range(19))
    for row in rows:
        assert ref.schnorr_verify(bytes.fromhex(row['message']), bytes.fromhex(row['public key']),
                                  bytes.fromhex(row['signature'])) == (row['verification result'] == 'TRUE')
    text = 'import LeanMiniscript.Bitcoin.Schnorr\n\nnamespace LeanMiniscript.Bitcoin\n' + HEX
    text += '\n-- All 19 official BIP340 verification vectors, including variable-size messages.\n'
    text += 'private def vectors : List (Nat × String × String × String × Bool) := [\n'
    for row in rows:
        expected = str(row['verification result'] == 'TRUE').lower()
        text += f'  ({row["index"]}, "{row["signature"].lower()}", "{row["public key"].lower()}", "{row["message"].lower()}", {expected}),\n'
    text += ']\nexample : vectors.all (fun (_, signature, key, message, expected) =>\n  Schnorr.verify (hex signature) (hex key) (hex message) == expected) = true := by native_decide\n'
    row = rows[0]
    text += f'private def validSig := hex "{row["signature"].lower()}"\nprivate def validKey := hex "{row["public key"].lower()}"\nprivate def validMessage := hex "{row["message"].lower()}"\n'
    text += """
-- Length guards are part of the standalone API, independent of Script encoding.
example : Schnorr.verify (validSig.extract 0 63) validKey validMessage = false := by native_decide
example : Schnorr.verify (validSig ++ hex "00") validKey validMessage = false := by native_decide
example : Schnorr.verify validSig (validKey.extract 0 31) validMessage = false := by native_decide
example : Schnorr.verify validSig (validKey ++ hex "00") validMessage = false := by native_decide
example : Schnorr.verify ByteArray.empty ByteArray.empty validMessage = false := by native_decide
end LeanMiniscript.Bitcoin
"""
    args.vectors_output.write_text(text)

    base = load('sighash_fixture_generator', Path(__file__).with_name('generate_taproot_sighash_fixtures.py'))
    base.generate(args.wallet_vectors, args.core_script)
    group = json.loads(args.wallet_vectors.read_text())['keyPathSpending'][0]
    tx = base.parse_transaction(group['given']['rawUnsignedTx'])
    spent = [base.make_output(u['amountSats'], bytes.fromhex(u['scriptPubKey'])) for u in group['given']['utxosSpent']]
    core = base.reference_functions(args.core_script.read_text())
    secret = (3).to_bytes(32, 'big')  # Public test key from official vector zero.
    key = ref.pubkey_gen(secret)
    leaf = b'\x20' + key + b'\xac'
    def sign(mode=0, script=leaf, annex=None):
        digest = core['TaprootSignatureHash'](tx, spent, mode, 0, scriptpath=True,
                    leaf_script=script, codeseparator_pos=0xffffffff, annex=annex)
        signature = ref.schnorr_sign(digest, secret, bytes(32))
        assert ref.schnorr_verify(digest, key, signature)
        return (signature + (bytes([mode]) if mode else b'')).hex()
    signatures = [(mode, sign(mode)) for mode in [0,1,2,3,129,130,131]]
    text = 'import LeanMiniscript.Bitcoin.TaprootSighashExamples\nimport LeanMiniscript.Extraction.RefInterp\n\nnamespace LeanMiniscript.Script\nopen LeanMiniscript.Bitcoin\n' + HEX
    text += f'private def key := hex "{key.hex()}"\n'
    text += """private def script : Script := [.pushData key, .op .OP_CHECKSIG]
private def witness (signature : ByteArray) : TapscriptWitness :=
  { arguments := [signature], scriptBytes := hex "20" ++ key ++ hex "ac",
    controlBlock := ⟨Array.replicate 33 0xc0⟩ }
private def success : WeightedResult → Bool
  | .success [top] _ _ => top.data == trueElement.data
  | _ => false
private def errorIs (expected : ScriptError) : WeightedResult → Bool
  | .failure error => error == expected
  | _ => false
private def run (w : TapscriptWitness) (tx : Transaction := sighashFixtureTransaction) : WeightedResult :=
  LeanMiniscript.Extraction.execTapscriptTransaction CryptoOracle.pureLeanSchnorr script w {}
    tx sighashFixtureSpentOutputs 0

-- Independent Core hashing plus the pinned BIP340 reference signer.
private def signatures : List (UInt8 × String) := [
"""
    text += ''.join(f'  ({mode}, "{sig}"),\n' for mode, sig in signatures) + ']\n'
    text += 'example : signatures.all (fun (_, sig) => success (run (witness (hex sig)))) = true := by native_decide\n'
    text += f'private def defaultSig := hex "{signatures[0][1]}"\n'
    text += f'example : success (run {{ witness (hex "{sign(annex=bytes.fromhex("500102"))}") with annex := some (hex "500102") }}) = true := by native_decide\n'
    add_script = b'\x00\x20' + key + b'\xba'
    text += f'example : success (LeanMiniscript.Extraction.execTapscriptTransaction CryptoOracle.pureLeanSchnorr\n  [.pushNum 0, .pushData key, .op .OP_CHECKSIGADD]\n  {{ arguments := [hex "{sign(script=add_script)}"], scriptBytes := hex "{add_script.hex()}", controlBlock := (witness defaultSig).controlBlock }}\n  {{}} sighashFixtureTransaction sighashFixtureSpentOutputs 0) = true := by native_decide\n'
    text += """
-- Mutating the signature, committed transaction, or annex rejects real crypto.
private def corrupted : ByteArray := ⟨defaultSig.data.set! 40 (defaultSig[40]! ^^^ 1)⟩
example : errorIs .schnorrSig (run (witness corrupted)) = true := by native_decide
example : errorIs .schnorrSig (run (witness defaultSig)
  { sighashFixtureTransaction with locktime := sighashFixtureTransaction.locktime + 1 }) = true := by native_decide
example : errorIs .schnorrSig (run { witness defaultSig with annex := some (hex "500102") }) = true := by native_decide
example : errorIs .schnorrSigHashType (run (witness (defaultSig ++ hex "00"))) = true := by native_decide
example : errorIs .schnorrSigSize (run (witness (defaultSig.extract 0 63))) = true := by native_decide
example : (match run (witness ByteArray.empty) with
  | .success [top] _ _ => top.data == falseElement.data
  | _ => false) = true := by native_decide
-- Standalone BIP340 rejects 65 bytes; Script strips its valid explicit type byte.
example : signatures.all (fun (mode, sig) => mode == 0 ||
  !Schnorr.verify (hex sig) key ByteArray.empty) = true := by native_decide
-- ECDSA remains explicitly supplied, with rejection as the default.
example : CryptoOracle.pureLeanSchnorr.checkSig defaultSig key ByteArray.empty = false := by native_decide
end LeanMiniscript.Script
"""
    args.execution_output.write_text(text)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['bip340-vectors', 'bip340-reference', 'wallet-vectors', 'core-script', 'vectors-output', 'execution-output']:
        parser.add_argument('--' + name, type=Path, required=True)
    generate(parser.parse_args())
