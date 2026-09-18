#!/usr/bin/env python3
"""Reproduce offline Taproot control-block and committed-execution fixtures.

Use the same pinned BIP340 reference, BIP341 wallet vectors and Core script
sources as generate_schnorr_fixtures.py. All source hashes are checked. Public
test keys only; verification is checked against every official control block.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import generate_schnorr_fixtures as schnorr

def leaves(tree):
    if tree is None:
        return []
    if isinstance(tree, dict):
        return [tree]
    return leaves(tree[0]) + leaves(tree[1])

def generate(args):
    assert hashlib.sha256(args.bip340_reference.read_bytes()).hexdigest() == schnorr.REFERENCE_SHA256
    ref = schnorr.load('control_bip340_reference', args.bip340_reference)
    base = schnorr.load('control_sighash_generator', Path(__file__).with_name('generate_taproot_sighash_fixtures.py'))
    base.generate(args.wallet_vectors, args.core_script)
    wallet = json.loads(args.wallet_vectors.read_text())
    def root_for(script, control):
        leaf = base.tagged_hash('TapLeaf', bytes([control[0] & 254]) + base.ser_string(script))
        root = leaf
        for i in range(33, len(control), 32):
            sibling = control[i:i+32]
            root = base.tagged_hash('TapBranch', min(root, sibling) + max(root, sibling))
        return leaf, root
    def output(internal, root):
        tweak = int.from_bytes(base.tagged_hash('TapTweak', internal + root), 'big')
        assert tweak < ref.n
        point = ref.point_add(ref.lift_x(int.from_bytes(internal, 'big')), ref.point_mul(ref.G, tweak))
        assert point is not None
        return point[0].to_bytes(32, 'big'), point[1] & 1
    fixtures = []
    for group in wallet['scriptPubKey']:
        tree = sorted(leaves(group['given']['scriptTree']), key=lambda leaf: leaf['id'])
        controls = group['expected'].get('scriptPathControlBlocks', [])
        assert len(tree) == len(controls)
        for leaf, control_hex in zip(tree, controls):
            script, control = bytes.fromhex(leaf['script']), bytes.fromhex(control_hex)
            leaf_hash, root = root_for(script, control)
            assert leaf_hash.hex() == group['intermediary']['leafHashes'][leaf['id']]
            assert root.hex() == group['intermediary']['merkleRoot']
            key, parity = output(control[1:33], root)
            assert key.hex() == group['intermediary']['tweakedPubkey']
            assert parity == control[0] & 1
            assert (b'\x51\x20' + key).hex() == group['expected']['scriptPubKey']
            fixtures.append((script.hex(), control.hex(), key.hex(), leaf['leafVersion'], leaf_hash.hex(), root.hex()))
    assert len(fixtures) == 12
    text = 'import LeanMiniscript.Bitcoin.TaprootControlBlock\n\nnamespace LeanMiniscript.Bitcoin\n' + schnorr.HEX
    text += '\n-- Every script-path control block from the pinned official BIP341 wallet vectors.\n'
    text += 'private def fixtures : List (String × String × String × UInt8 × String × String) := [\n'
    text += ''.join(f'  ("{s}", "{c}", "{q}", {v}, "{h}", "{r}"),\n' for s,c,q,v,h,r in fixtures) + ']\n'
    text += """example : fixtures.all (fun (script, control, output, version, leaf, root) =>
  match verifyTaprootControlBlock (hex output) (hex script) (hex control) with
  | .error _ => false
  | .ok commitment => commitment.leafVersion == version && commitment.leafHash.data == (hex leaf).data &&
      commitment.merkleRoot.data == (hex root).data) = true := by native_decide
private def errorIs {α : Type} (expected : TaprootControlError) (result : Except TaprootControlError α) : Bool :=
  match result with
  | .error error => error == expected
  | .ok _ => false
"""
    s,c,q,_,_,_ = fixtures[-1]  # Depth-two path.
    text += f'def controlFixtureScript := hex "{s}"\ndef controlFixtureControl := hex "{c}"\ndef controlFixtureOutput := hex "{q}"\n'
    text += """
example : [0, 1, 32, 34, 64, 4128, 4130, 4161].all (fun n => errorIs .controlSize
  (parseTaprootControlBlock ⟨Array.replicate n 0⟩)) = true := by native_decide
example : (List.range 129).all (fun depth => match parseTaprootControlBlock
    ⟨Array.replicate (33 + 32 * depth) 0xc1⟩ with
  | .ok control => control.merklePath.length == depth && control.leafVersion == 0xc0 && control.outputParity
  | .error _ => false) = true := by native_decide
private def flip (bytes : ByteArray) (index : Nat) : ByteArray :=
  ⟨bytes.data.set! index (bytes[index]! ^^^ 1)⟩
example : errorIs .commitmentMismatch (verifyTaprootControlBlock controlFixtureOutput controlFixtureScript
  (flip controlFixtureControl 0)) = true := by native_decide
example : errorIs .commitmentMismatch (verifyTaprootControlBlock controlFixtureOutput controlFixtureScript
  (flip controlFixtureControl 33)) = true := by native_decide
example : errorIs .commitmentMismatch (verifyTaprootControlBlock controlFixtureOutput
  (controlFixtureScript ++ hex "00") controlFixtureControl) = true := by native_decide
example : errorIs .commitmentMismatch (verifyTaprootControlBlock (flip controlFixtureOutput 0)
  controlFixtureScript controlFixtureControl) = true := by native_decide
-- Reversing proof nodes must not accidentally preserve a depth-two root.
private def reversedPath := controlFixtureControl.extract 0 33 ++
  controlFixtureControl.extract 65 97 ++ controlFixtureControl.extract 33 65
example : errorIs .commitmentMismatch (verifyTaprootControlBlock controlFixtureOutput controlFixtureScript
  reversedPath) = true := by native_decide
example : errorIs .internalKey (verifyTaprootControlBlock controlFixtureOutput controlFixtureScript
  (controlFixtureControl.extract 0 1 ++ ⟨Array.replicate 32 0xff⟩ ++ controlFixtureControl.extract 33 97)) = true := by native_decide
example : errorIs .outputKeySize (verifyTaprootControlBlock ByteArray.empty controlFixtureScript
  controlFixtureControl) = true := by native_decide
private def generatorKey := hex "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
private def zero : ByteArray := ⟨Array.replicate 32 0⟩
example : (match taprootTweakPoint generatorKey zero with
  | .ok (x, y) => x == Secp256k1.decodeBE generatorKey && y % 2 == 0
  | .error _ => false) = true := by native_decide
example : errorIs .tweakRange (taprootTweakPoint generatorKey
  (hex "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141")) = true := by native_decide
example : errorIs .tweakRange (taprootTweakPoint generatorKey ⟨Array.replicate 32 0xff⟩) = true := by native_decide
example : errorIs .infiniteOutput (taprootTweakPoint generatorKey
  (hex "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140")) = true := by native_decide
example : errorIs .tweakSize (taprootTweakPoint generatorKey ByteArray.empty) = true := by native_decide
example : errorIs .internalKey (taprootTweakPoint zero zero) = true := by native_decide
example : TaprootControlError.controlSize.coreTag = "TAPROOT_WRONG_CONTROL_SIZE" := rfl
example : [TaprootControlError.internalKey, .tweakRange, .infiniteOutput, .commitmentMismatch].all
  (fun error => error.coreTag == "WITNESS_PROGRAM_MISMATCH") = true := by native_decide
"""
    internal = ref.pubkey_gen((5).to_bytes(32, 'big'))
    siblings = [base.sha256(f'public test sibling {i}'.encode()) for i in range(128)]
    control = b'\xc0' + internal + b''.join(siblings)
    _, root = root_for(b'\x51', control)
    key, parity = output(internal, root)
    control = bytes([192 | parity]) + control[1:]
    text += f'private def maxDepthControl := hex "{control.hex()}"\n'
    text += f'example : (verifyTaprootControlBlock (hex "{key.hex()}") (hex "51") maxDepthControl).isOk = true := by native_decide\n'
    text += 'example : errorIs .controlSize (verifyTaprootControlBlock controlFixtureOutput (hex "51")\n  (maxDepthControl ++ zero)) = true := by native_decide\nend LeanMiniscript.Bitcoin\n'
    args.control_output.write_text(text)

    group = wallet['keyPathSpending'][0]
    tx = base.parse_transaction(group['given']['rawUnsignedTx'])
    spent = [base.make_output(u['amountSats'], bytes.fromhex(u['scriptPubKey'])) for u in group['given']['utxosSpent']]
    core = base.reference_functions(args.core_script.read_text())
    secret = (3).to_bytes(32, 'big')
    signing_key = ref.pubkey_gen(secret)
    script = b'\x20' + signing_key + b'\xac'
    leaf, root = root_for(script, b'\xc0' + internal)
    key, parity = output(internal, root)
    control = bytes([192 | parity]) + internal
    program = b'\x51\x20' + key
    spent[0] = base.make_output(spent[0].nValue, program)
    def sign(annex=None):
        digest = core['TaprootSignatureHash'](tx,spent,0,0,scriptpath=True,leaf_script=script,
                                           codeseparator_pos=0xffffffff,annex=annex)
        return ref.schnorr_sign(digest,secret,bytes(32)).hex()
    signature = sign()
    annex_signature = sign(bytes.fromhex('500102'))
    future_leaf, future_root = root_for(b'\x51', b'\xfa' + internal)
    future_key, future_parity = output(internal, future_root)
    future_control = bytes([250 | future_parity]) + internal
    text = 'import LeanMiniscript.Bitcoin.TaprootSighashExamples\nimport LeanMiniscript.Extraction.Taproot\n\nnamespace LeanMiniscript.Extraction\nopen LeanMiniscript.Script LeanMiniscript.Bitcoin\n' + schnorr.HEX
    text += f'private def key := hex "{signing_key.hex()}"\nprivate def control := hex "{control.hex()}"\nprivate def program := hex "{program.hex()}"\nprivate def signature := hex "{signature}"\n'
    text += """private def script : Script := [.pushData key, .op .OP_CHECKSIG]
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
"""
    text += f'private def annexWitness := [hex "{annex_signature}", scriptBytes, control, hex "500102"]\n'
    text += 'example : success (run annexWitness) = true := by native_decide\n'
    text += """example : (match parseTapscriptWitness annexWitness with
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
"""
    text += f'private def futureControl := hex "{future_control.hex()}"\nprivate def futurePrevouts := prevouts.modify 0 (fun output => {{ output with scriptPubKey := hex "5120{future_key.hex()}" }})\n'
    text += 'example : errorIs (.leafVersionUnsupported 0xfa) (run [hex "51", futureControl] futurePrevouts) = true := by native_decide\n'
    text += 'example : errorIs (.control .commitmentMismatch) (run [hex "51", flip futureControl 0] futurePrevouts) = true := by native_decide\n'
    text += """
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
"""
    text += 'end LeanMiniscript.Extraction\n'
    args.execution_output.write_text(text)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['bip340-reference', 'wallet-vectors', 'core-script', 'control-output', 'execution-output']:
        parser.add_argument('--' + name, type=Path, required=True)
    generate(parser.parse_args())
