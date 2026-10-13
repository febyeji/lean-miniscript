#!/usr/bin/env python3
"""Reproduce the official BIP174/BIP370/BIP371 PSBT test vectors as Lean data.

Sources are the BIP mediawiki files at bitcoin/bips commit
927b6de9915c9262615a6399de51b200f81e5aa4:
  bip-0174.mediawiki, bip-0370.mediawiki, bip-0371.mediawiki
All source hashes are checked. Every PSBT vector appears in each BIP both as
hex and as Base64; the two encodings are required to agree byte-for-byte, so
a transcription error in either one stops generation. Vector order and counts
are asserted. No expected value is computed here.

Usage:
  generate_psbt_fixtures.py BIP174 BIP370 BIP371 OUTPUT.lean
"""
import argparse
import base64
from decimal import Decimal
import hashlib
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

SHA256 = {
    'bip-0174.mediawiki': 'f2a8e1a9c9e31cc7f607b3c7e2419c63eeccc4bd5b725968cde54ab8cfa1d410',
    'bip-0370.mediawiki': 'b2b6e9099592fa04179383f9a1fd8b201fbeef4470f4c3f1c050d25589979c57',
    'bip-0371.mediawiki': 'c2e8143a3c9aee0ee38d863cf40947ddf8ee67b4f40a748fb6925ccc5ad4b791',
}
BIPS_COMMIT = '927b6de9915c9262615a6399de51b200f81e5aa4'


def payload(text, start):
    """Text of a <pre> block beginning at or after `start`, across lines."""
    begin = text.index('<pre>', start) + len('<pre>')
    end = text.index('</pre>', begin)
    return re.sub(r'\s+', '', text[begin:end]).lstrip('<')


def entries(text):
    """(heading, case name, hex, base64 or None) in document order.

    The heading is the last non-bullet prose line before the entry; case
    names come from '* Case:' bullets and are empty for role vectors."""
    section = text[text.index('==Test Vectors=='):text.index('==Rationale==')]
    result = []
    heading, case = '', ''
    lines = section.split('\n')
    offsets = []
    position = 0
    for line in lines:
        offsets.append(position)
        position += len(line) + 1
    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('* Case:'):
            case = re.sub(r'<[^>]+>', '', stripped[len('* Case:'):]).strip()
        elif re.match(r'^\*\*? Bytes in Hex:', stripped, re.IGNORECASE):
            hex_text = payload(section, offsets[index]).lower()
            b64 = None
            following = '\n'.join(lines[index + 1:index + 4])
            match = re.search(r'Base64 String:', following)
            if match:
                b64 = payload(section, offsets[index + 1] + match.start())
                if base64.b64decode(b64, validate=True).hex() != hex_text:
                    raise SystemExit(f'hex/base64 mismatch: {heading!r} {case!r}')
            bytes.fromhex(hex_text)
            result.append((heading, case, hex_text, b64))
            case = ''
        elif stripped and not stripped.startswith('*') and not stripped.startswith('<') \
                and not stripped.startswith('='):
            heading = stripped
    return result


def role_inputs(text):
    """Creator transaction description and updater data of the BIP174 roles."""
    section = text[text.index('The private keys in the tests below'):
                   text.index('Given the above updated PSBT, a signer that supports')]
    master = re.search(r'Extended Private Key: <pre>(\w+)', section).group(1)
    outputs = [(spk, int(Decimal(amount) * 100000000)) for spk, amount in
               re.findall(r'scriptPubKey: <tt>([0-9a-f]+)</tt>, Amount: <tt>([\d.]+)</tt>', section)]
    inputs = [(txid, int(index)) for txid, index in
              re.findall(r'TXID: <tt>([0-9a-f]+)</tt>, Index: <tt>(\d+)</tt>', section)]
    updater = section[section.index('an updater with only the following'):
                      section.index('Must create this PSBT')]
    def block(start, end):
        return updater[updater.index(start):updater.index(end)]
    redeem = re.findall(r'\*\* <tt>([0-9a-f]+)</tt>', block('* Redeem Scripts:', '* Witness Scripts:'))
    witness = re.findall(r'\*\* <tt>([0-9a-f]+)</tt>', block('* Witness Scripts:', '* Previous Transactions:'))
    previous = re.findall(r'\*\* <pre>([0-9a-f]+)</pre>', block('* Previous Transactions:', '* Public Keys'))
    keys = re.findall(r"Key: <tt>([0-9a-f]+)</tt>, Derivation Path: <tt>([0-9m/']+)</tt>", updater)
    assert (len(outputs), len(inputs), len(redeem), len(witness), len(previous), len(keys)) == (2, 2, 2, 1, 2, 6)
    for item in redeem + witness + previous + [k for k, _ in keys]:
        bytes.fromhex(item)
    return master, outputs, inputs, redeem, witness, previous, keys


def lean_string(value):
    return '"' + value.replace('\\', '\\\\').replace('"', '\\"') + '"'


def emit_list(name, doc, items):
    text = f'\n/-- {doc} -/\ndef {name} : List (String × String × String) := [\n'
    text += ''.join(f'  ({lean_string(case)}, {lean_string(hex_text)}, {lean_string(b64 or "")}),\n'
                    for (_, case, hex_text, b64) in items)
    return text + ']\n'


def generate(args):
    sources = {}
    for path in (args.bip174, args.bip370, args.bip371):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == SHA256[path.name], f'{path.name}: unexpected SHA256 {digest}'
        sources[path.name] = entries(path.read_text())

    bip174 = sources['bip-0174.mediawiki']
    invalid174 = [e for e in bip174 if e[0].startswith('The following are invalid')]
    valid174 = [e for e in bip174 if e[0].startswith('The following are valid')]
    signer174 = [e for e in bip174 if e[0] == 'Fails Signer checks']
    roles174 = bip174[len(invalid174) + len(valid174) + len(signer174):]
    assert (len(invalid174), len(valid174), len(signer174), len(roles174)) == (20, 10, 4, 14)
    # Every role vector except the extracted transaction is a PSBT.
    assert [e[3] is None for e in roles174] == [False] * 7 + [True] + [False] * 6

    bip370 = sources['bip-0370.mediawiki']
    invalid370 = [e for e in bip370 if e[0].startswith('The following are invalid')]
    valid370 = [e for e in bip370 if e[0].startswith('The following are valid')]
    locktime370 = [e for e in bip370 if e[0].startswith('The timelock for')]
    assert (len(invalid370), len(valid370), len(locktime370)) == (24, 14, 10)
    expected = {'0': 'some 0', '10000': 'some 10000', '1657048460': 'some 1657048460'}
    locktimes = []
    for heading, case, hex_text, b64 in locktime370:
        match = re.search(r'computed to be (\d+)', heading)
        locktimes.append((case, hex_text, b64, expected[match.group(1)] if match else 'none'))
    assert [l[3] for l in locktimes] == ['some 0'] * 2 + ['some 10000'] * 4 + \
        ['some 1657048460'] * 3 + ['none']

    bip371 = sources['bip-0371.mediawiki']
    invalid371 = [e for e in bip371 if e[0].startswith('The following are invalid')]
    valid371 = [e for e in bip371 if e[0].startswith('The following are valid')]
    assert (len(invalid371), len(valid371)) == (11, 6)

    text = f'''/-! Generated by scripts/generate_psbt_fixtures.py from bitcoin/bips commit
{BIPS_COMMIT} (bip-0174, bip-0370 and bip-0371 mediawiki
test-vector sections). Each PSBT's hex and Base64 forms were checked to agree.
Entries are `(case name, hex, Base64)`; role vectors have empty names. -/

namespace LeanMiniscript.Psbt.Fixtures
'''
    text += emit_list('bip174Invalid', 'BIP174 invalid PSBTs.', invalid174)
    text += emit_list('bip174Valid', 'BIP174 valid PSBTs.', valid174)
    text += emit_list('bip174SignerFailures', 'BIP174 valid PSBTs that fail signer checks.', signer174)
    text += emit_list('bip174Roles', 'BIP174 role vectors in document order: creator, updater, '
                      'updater with SIGHASH_ALL, two signers, combiner, finalizer, extracted '
                      'transaction, two PSBTs with unknown records and their combination, '
                      'two PSBTs and their combination.', roles174)
    master, outputs, inputs, redeem, witness, previous, keys = role_inputs(
        args.bip174.read_text())
    strings = lambda items: '[' + ', '.join(lean_string(item) for item in items) + ']'
    text += '\n/-- BIP174 master key from which the role-vector keys derive. -/\n'
    text += f'def bip174MasterKey : String := {lean_string(master)}\n'
    text += '\n/-- BIP174 creator outputs: (scriptPubKey, amount in satoshis). -/\n'
    text += 'def bip174CreatorOutputs : List (String × Nat) := [' + \
        ', '.join(f'({lean_string(s)}, {a})' for s, a in outputs) + ']\n'
    text += '\n/-- BIP174 creator inputs: (TXID in display order, index). -/\n'
    text += 'def bip174CreatorInputs : List (String × Nat) := [' + \
        ', '.join(f'({lean_string(t)}, {i})' for t, i in inputs) + ']\n'
    text += '\n/-- BIP174 updater data. -/\n'
    text += f'def bip174UpdaterRedeemScripts : List String := {strings(redeem)}\n'
    text += f'def bip174UpdaterWitnessScripts : List String := {strings(witness)}\n'
    text += f'def bip174UpdaterPreviousTransactions : List String := {strings(previous)}\n'
    text += '/-- (public key, derivation path) -/\n'
    text += 'def bip174UpdaterKeys : List (String × String) := [\n' + \
        ''.join(f'  ({lean_string(k)}, {lean_string(p)}),\n' for k, p in keys) + ']\n'
    text += emit_list('bip370Invalid', 'BIP370 invalid PSBTs.', invalid370)
    text += emit_list('bip370Valid', 'BIP370 valid PSBTs.', valid370)
    text += '\n/-- BIP370 lock time determination vectors with the expected lock time. -/\n'
    text += 'def bip370Locktimes : List (String × String × String × Option Nat) := [\n'
    text += ''.join(f'  ({lean_string(case)}, {lean_string(hex_text)}, {lean_string(b64 or "")}, {value}),\n'
                    for case, hex_text, b64, value in locktimes)
    text += ']\n'
    text += emit_list('bip371Invalid', 'BIP371 invalid PSBTs.', invalid371)
    text += emit_list('bip371Valid', 'BIP371 valid PSBTs.', valid371)
    text += '\nend LeanMiniscript.Psbt.Fixtures\n'
    args.output.write_text(text)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('bip174', type=Path)
    parser.add_argument('bip370', type=Path)
    parser.add_argument('bip371', type=Path)
    parser.add_argument('output', type=Path)
    generate(parser.parse_args())
