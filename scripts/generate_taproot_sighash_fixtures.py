#!/usr/bin/env python3
"""Generate offline Lean fixtures from official BIP341 and pinned Core sources.

Use --wallet-vectors and --core-script to provide these exact public files:
https://raw.githubusercontent.com/bitcoin/bips/55083d36ddebcd2a039135a2f4ee74917a5803d3/bip-0341/wallet-test-vectors.json
https://raw.githubusercontent.com/bitcoin/bitcoin/9be056a8a72b624dae9623b2f7bded92c2a21c91/test/functional/test_framework/script.py

Only named signature-message/hash functions are extracted from Core's AST.
Small transaction adapters serialize bounded fields in Bitcoin wire order.
The adapters/reference functions are first checked against every official
signing message, digest and component hash before generating additional cases.
Core's helper zero-fills missing SINGLE outputs; those invalid cases are NOT
used as valid fixtures. Lean must reject them as required by BIP341.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace


def compact(n):
    if n < 253:
        return bytes([n])
    if n <= 65535:
        return b'\xfd' + n.to_bytes(2, 'little')
    if n <= 4294967295:
        return b'\xfe' + n.to_bytes(4, 'little')
    return b'\xff' + n.to_bytes(8, 'little')


def ser_string(data):
    return compact(len(data)) + data


def sha256(data):
    return hashlib.sha256(data).digest()


def tagged_hash(tag, data):
    prefix = sha256(tag.encode())
    return sha256(prefix + prefix + data)


def parse_transaction(raw):
    data = bytes.fromhex(raw)
    cursor = 0

    def read(n):
        nonlocal cursor
        value = data[cursor:cursor + n]
        assert len(value) == n
        cursor += n
        return value

    def number(n):
        return int.from_bytes(read(n), 'little')

    def count():
        n = number(1)
        return number({253: 2, 254: 4, 255: 8}[n]) if n >= 253 else n

    version = number(4)
    inputs = []
    for _ in range(count()):
        txid, index = read(32), number(4)
        script, sequence = read(count()), number(4)
        wire = txid + index.to_bytes(4, 'little')
        prevout = SimpleNamespace(txid=txid, index=index, serialize=lambda wire=wire: wire)
        inputs.append(SimpleNamespace(prevout=prevout, scriptSig=script, nSequence=sequence))
    outputs = [make_output(number(8), read(count())) for _ in range(count())]
    locktime = number(4)
    assert cursor == len(data)
    return SimpleNamespace(version=version, nLockTime=locktime, vin=inputs, vout=outputs)


def make_output(amount, script):
    wire = amount.to_bytes(8, 'little') + ser_string(script)
    return SimpleNamespace(nValue=amount, scriptPubKey=script, serialize=lambda: wire)


def reference_functions(source):
    names = {'BIP341_sha_prevouts', 'BIP341_sha_amounts', 'BIP341_sha_scriptpubkeys',
             'BIP341_sha_sequences', 'BIP341_sha_outputs', 'TaprootSignatureMsg', 'TaprootSignatureHash'}
    selected = [node for node in ast.parse(source).body
                if isinstance(node, ast.FunctionDef) and node.name in names]
    assert {node.name for node in selected} == names
    namespace = dict(sha256=sha256, ser_string=ser_string, TaggedHash=tagged_hash,
                     SIGHASH_ALL=1, SIGHASH_NONE=2, SIGHASH_SINGLE=3,
                     SIGHASH_ANYONECANPAY=128, LEAF_VERSION_TAPSCRIPT=192)
    exec(compile(ast.Module(body=selected, type_ignores=[]), '<pinned-core-sighash>', 'exec'), namespace)
    return namespace


def generate(wallet_path, core_path):
    wallet_raw, core_raw = wallet_path.read_bytes(), core_path.read_bytes()
    # Verify source digests recorded when this generator was added.
    assert sha256(wallet_raw).hex() == WALLET_SHA256, 'Unexpected wallet-vector source'
    assert sha256(core_raw).hex() == CORE_SHA256, 'Unexpected Core reference source'
    group = json.loads(wallet_raw)['keyPathSpending'][0]
    tx = parse_transaction(group['given']['rawUnsignedTx'])
    spent = [make_output(u['amountSats'], bytes.fromhex(u['scriptPubKey']))
             for u in group['given']['utxosSpent']]
    ref = reference_functions(core_raw.decode())
    components = [('hashPrevouts', 'BIP341_sha_prevouts', tx),
                  ('hashAmounts', 'BIP341_sha_amounts', spent),
                  ('hashScriptPubkeys', 'BIP341_sha_scriptpubkeys', spent),
                  ('hashSequences', 'BIP341_sha_sequences', tx),
                  ('hashOutputs', 'BIP341_sha_outputs', tx)]
    for name, function, value in components:
        assert ref[function](value).hex() == group['intermediary'][name]
    for item in group['inputSpending']:
        index, mode = item['given']['txinIndex'], item['given']['hashType']
        assert ref['TaprootSignatureMsg'](tx, spent, mode, index).hex() == item['intermediary']['sigMsg']
        assert ref['TaprootSignatureHash'](tx, spent, mode, index).hex() == item['intermediary']['sigHash']

    lines = ['import LeanMiniscript.Bitcoin.TaprootSighash', '',
             'namespace LeanMiniscript.Bitcoin', '',
             '/-! Generated by scripts/generate_taproot_sighash_fixtures.py.',
             'BIP341 wallet vectors: 55083d36ddebcd2a039135a2f4ee74917a5803d3.',
             'Core reference: 9be056a8a72b624dae9623b2f7bded92c2a21c91.',
             'Seven official cases plus 56 Core-generated valid cases; all checked offline. -/', '',
             'private def digit (byte : UInt8) : Nat :=',
             '  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87',
             'private def decodeHex : List UInt8 → List UInt8',
             '  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest',
             '  | _ => []',
             'private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩', '',
             'def sighashFixtureTransaction : Transaction where', f'  version := {tx.version}',
             f'  locktime := {tx.nLockTime}', '  inputs := #[']
    for i in tx.vin:
        lines.append(f'    {{ previousOutput := {{ txid := hex "{i.prevout.txid.hex()}", index := {i.prevout.index} }}, scriptSig := hex "{i.scriptSig.hex()}", sequence := {i.nSequence} }},')
    lines += ['  ]', '  outputs := #[']
    for o in tx.vout:
        lines.append(f'    {{ amount := {o.nValue}, scriptPubKey := hex "{o.scriptPubKey.hex()}" }},')
    lines += ['  ]', '', 'def sighashFixtureSpentOutputs : Array TxOutput := #[']
    for o in spent:
        lines.append(f'  {{ amount := {o.nValue}, scriptPubKey := hex "{o.scriptPubKey.hex()}" }},')
    lines += [']', '', 'def sighashFixtureContext : TaprootSigHashContext :=',
              '  { transaction := sighashFixtureTransaction, spentOutputs := sighashFixtureSpentOutputs, inputIndex := 0 }', '',
              f'example : (serializeTransaction sighashFixtureTransaction).data = (hex "{group["given"]["rawUnsignedTx"]}").data := by native_decide']
    for name, _, _ in components:
        expression = {'hashScriptPubkeys': 'hashScriptPubKeys sighashFixtureSpentOutputs',
                      'hashAmounts': 'hashAmounts sighashFixtureSpentOutputs'}.get(name, f'{name} sighashFixtureTransaction')
        lines.append(f'example : ({expression}).data = (hex "{group["intermediary"][name]}").data := by native_decide')
    lines += ['', 'private def bytesMatch (expected : String) : Except SighashError ByteArray → Bool',
              '  | .ok bytes => bytes.data == (hex expected).data', '  | .error _ => false', '',
              'private def officialFixtures : List (Nat × UInt8 × String × String) := [']
    for item in group['inputSpending']:
        lines.append(f'  ({item["given"]["txinIndex"]}, {item["given"]["hashType"]}, "{item["intermediary"]["sigMsg"]}", "{item["intermediary"]["sigHash"]}"),')
    lines += [']', '', 'example : officialFixtures.all (fun (index, mode, message, digest) =>',
              '  let ctx := { sighashFixtureContext with inputIndex := index }',
              '  bytesMatch message (taprootSignatureMessage ctx mode) && bytesMatch digest (taprootSignatureHash ctx mode)) = true := by native_decide', '',
              'private def coreFixtures : List (UInt8 × Bool × Nat × String × String) := [']
    leaf = bytes.fromhex('200202020202020202020202020202020202020202020202020202020202020202ac')
    for mode in [0, 1, 2, 3, 129, 130, 131]:
        for annex in [None, b'\x50\x01\x02']:
            for path in range(4):
                kwargs = dict(annex=annex)
                if path:
                    kwargs.update(scriptpath=True, leaf_script=leaf, codeseparator_pos=[0xffffffff, 0, 7][path - 1])
                msg = ref['TaprootSignatureMsg'](tx, spent, mode, 0, **kwargs)
                digest = ref['TaprootSignatureHash'](tx, spent, mode, 0, **kwargs)
                lines.append(f'  ({mode}, {str(annex is not None).lower()}, {path}, "{msg.hex()}", "{digest.hex()}"),')
    lines += [']', '', 'example : coreFixtures.all (fun (mode, annexPresent, path, message, digest) =>',
              '  let ctx := { sighashFixtureContext with',
              '    annex := if annexPresent then some (hex "500102") else none',
              f'    spendPath := if path = 0 then .keyPath else .scriptPath (hex "{leaf.hex()}") 0xc0',
              '      (if path = 1 then 4294967295 else if path = 2 then 0 else 7) }',
              '  bytesMatch message (taprootSignatureMessage ctx mode) && bytesMatch digest (taprootSignatureHash ctx mode)) = true := by native_decide', '',
              'end LeanMiniscript.Bitcoin', '']
    return '\n'.join(lines)


WALLET_SHA256 = '403e19fb81dd1f31e745699216308f61fb403774b2aafa87b631b8f7c042d37f'
CORE_SHA256 = '24bdbfc18cfa1084c1c985218c0067c2e4c06cbd83488e5c08f2167a12bf3abf'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wallet-vectors', type=Path, required=True)
    parser.add_argument('--core-script', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(generate(args.wallet_vectors, args.core_script))
