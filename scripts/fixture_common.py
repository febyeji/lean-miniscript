#!/usr/bin/env python3
"""Shared helpers for the pinned-source fixture generators.

Each helper preserves the exact behavior of the code it replaces; generated
Lean output is unchanged.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re

BIP340_REFERENCE_SHA256 = '4b1d4ad9e60820df4a6d239733d52b014bc03e4c47afd757a2fe4d3b586d892c'
BIP143_SHA256 = '62bc71351563e68baeb12643c68355d217953ae9eb6a6e68b2b0323275b6beec'


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_sighash_generator(name='sighash_fixture_generator'):
    return load_module(name, Path(__file__).with_name('generate_taproot_sighash_fixtures.py'))


def check_sha256(path, expected):
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected


def require_sha256(path, expected):
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit('Source checksum mismatch; expected SHA-256 ' + expected)


def bip341_keypath_group(base, wallet_path, core_path):
    """Return (group, transaction, spent outputs, Core reference functions)
    for keyPathSpending[0] of the pinned BIP341 wallet vectors."""
    group = json.loads(wallet_path.read_text())['keyPathSpending'][0]
    tx = base.parse_transaction(group['given']['rawUnsignedTx'])
    spent = [base.make_output(u['amountSats'], bytes.fromhex(u['scriptPubKey']))
             for u in group['given']['utxosSpent']]
    reference = base.reference_functions(core_path.read_text())
    return group, tx, spent, reference


def rewrite_generated_block(path, block):
    content = path.read_text()
    if '-- VECTOR_DATA' in content:
        content = content.replace('-- VECTOR_DATA', block)
    else:
        content = re.sub(r'-- BEGIN GENERATED VECTORS.*?-- END GENERATED VECTORS', lambda _: block, content, flags=re.S)
    path.write_text(content)
