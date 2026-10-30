<p align="center">
  <img src="assets/lean-miniscript-logo.svg" alt="lean-miniscript logo" width="180">
</p>

# lean-miniscript

`lean-miniscript` models Bitcoin Miniscript and the surrounding Bitcoin execution and data boundaries in Lean 4. The repository combines executable models, proofs, and conformance checks against pinned external fixtures.

## Quick start

Install the Lean version selected by `lean-toolchain`, then run:

```sh
lake build
```

The build checks the library, proofs, executable examples, and tests.

### Policy CLI

Parse a policy and print its canonical form:

```sh
lake exe policy_cli -- \
  'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
```

Compile a Miniscript policy for P2WSH or Tapscript:

```sh
lake exe policy_cli -- compile --context tapscript \
  'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
```

The `compile` output includes canonical Miniscript, Script hex, script size, static opcode count, and the maximum satisfaction-stack bound. Run `lake exe policy_cli -- --help` for all commands.

### PSBT CLI

Inspect a PSBT, finalize an input from a descriptor, and extract the final transaction:

```sh
lake exe psbt_cli -- inspect --encoding hex "$PSBT_HEX"
lake exe psbt_cli -- finalize "$SIGNED_PSBT_BASE64" "0=$DESCRIPTOR" \
  | lake exe psbt_cli -- extract -
```

Input descriptors use the zero-based `INDEX=DESCRIPTOR` form. Use `--encoding hex` for hex input and `-` for standard input.

```sh
python3 scripts/test_psbt_cli.py
```

This check uses pinned BIP174 and BIP370 fixtures.

### Bitcoin Core fixture audit

Download and run the Script fixture from a pinned Bitcoin Core revision:

```sh
curl --fail --location \
  https://raw.githubusercontent.com/bitcoin/bitcoin/f13ae519de94394314cd63a27924b0998ac65d45/src/test/data/script_tests.json \
  --output /tmp/script_tests.json
lake exe core_fixture_audit -- --show-details /tmp/script_tests.json
```

The pinned fixture contains 1,258 executable rows and 60 documentation rows. The audit reports matching rows and rows outside the model scope separately. The fixture source is pinned to [Bitcoin Core commit `f13ae519de94394314cd63a27924b0998ac65d45`](https://github.com/bitcoin/bitcoin/commit/f13ae519de94394314cd63a27924b0998ac65d45). Regenerate the PSBT fixtures from the pinned BIP174, BIP370, and BIP371 sources with `scripts/generate_psbt_fixtures.py`.

### Equivalence obligations

After `lake build`, count the open opcode equivalence obligations:

```sh
lake env lean --run scripts/equivalence_obligations.lean
```

The command prints one integer: the number of (opcode, signature version) pairs in `equivalenceObligations` whose theorem is missing or depends on `sorry`. Each pair covers one opcode of `Script.Opcode` under BASE, witness v0, or Tapscript, and its theorem states `OpcodeAgreement opcode version`: Core's byte-level step `coreRawStep` and the typed `runtimeStep` return the same runtime state or Script error. The statement assumes both timelock opcodes are enabled, CONST_SCRIPTCODE is off, the signature oracle does not depend on the FindAndDelete script code, and the step does not stop at the BASE/witness-v0 operation limit. Add `--list` to print each pair's status and theorem name before the count. The command exits with an error when the list misses or repeats a pair or names a declaration of another type. The obligations are in `LeanMiniscript/Extraction/EquivalenceObligations.lean`.

## Scope and layers

These sections describe different abstractions. Miniscript describes spending policies, Bitcoin Script executes bytecode, Taproot defines a spending protocol around a P2TR output and Tapscript, and descriptors, transactions, and PSBT connect these pieces to wallet data.

### Miniscript and policy

- Miniscript syntax, surface parsing, pretty-printing, and normalization
- Type inference, validation, and context checks
- Concrete compilation and compilation-agreement proofs
- Satisfaction and dissatisfaction candidates, availability, and resource bounds
- Malleability analysis and BIP379-related properties
- Policy parsing, denotational semantics, and cost-based policy compilation

Miniscript is the policy language layer. It can compile a policy into Bitcoin Script or Tapscript, but it does not define Taproot's output commitment or transaction rules.

### Bitcoin Script and Tapscript execution

- Legacy Script and witness-v0 execution
- Conditional flow, numeric and indexed stack operations, timelocks, and signature encoding
- Script serialization and deserialization
- Tapscript initial and runtime resource limits and validation weight

This layer defines how script bytes execute once a spending path has selected a script and witness.

### Taproot protocol

- Native P2TR output keys and key-path/script-path spending
- BIP341 signature hashing
- Annex handling, control-block commitments, Merkle paths, and leaf versions
- `OP_SUCCESSx` and future-leaf semantics at the modeled Bitcoin Core witness boundary

Transaction-backed native Taproot verification uses [`verifyNativeTaprootTransaction`](LeanMiniscript/Extraction/TaprootTransaction.lean). This entry point handles key-path and script-path witnesses at the same Core witness boundary.

For canonical byte-to-AST checking, use [`verifyCanonicalTapscriptTransaction`](LeanMiniscript/Extraction/TaprootBytes.lean). This API checks canonical encoding together with the current model's `0xc0` Tapscript AST.

Taproot is a Bitcoin spending protocol, not a Miniscript language. Miniscript can provide a policy for a Taproot script path, while Taproot also supports key-path spending and defines the output, commitment, witness, and signature-hash rules around both paths.

### Descriptors and transaction data

- `raw`, `pk`, `pkh`, `wpkh`, `multi`, and `sortedmulti`
- `sh`, `wsh`, `sh(wpkh)`, `sh(wsh)`, and `tr`
- Taproot tree compilation, Merkle paths, control blocks, and descriptor satisfactions
- Transaction, sighash, ECDSA, Schnorr, and Taproot serialization utilities
- PSBT BIP174, BIP370, and BIP371 codecs and role transitions
- Descriptor-based PSBT finalization and transaction extraction

This layer carries the serialized keys, scripts, transactions, and PSBT state used by the policy, Script, and Taproot layers.

### Executables and conformance

- `core_fixture_audit` — Bitcoin Core Script fixture audit
- `script_cli` — Script parsing and execution-boundary checks
- `policy_cli` — policy parsing and compilation
- `psbt_cli` — PSBT inspection, finalization, and extraction
- `LeanMiniscript/Conformance/` — cross-module policy, descriptor, and PSBT checks

## How to read the verification results

Lean theorems prove the contracts stated by their declarations. A theorem implementation is considered complete when `lake build` succeeds and the declaration contains no `sorry`, `admit`, placeholder axiom, or hidden assumption.

The current verification results include:

- Matching results for the executable rows in the pinned Bitcoin Core Script fixture
- Theorems that PSBT finalization preserves the unsigned transaction, UTXO data, v2 transaction fields, and locktime
- CompactSize witness-length checks for generated final inputs
- Commitment and execution checks for Taproot script-path witnesses generated by descriptor satisfaction
- Transaction-backed Core witness verification for native Taproot key-path and script-path spending

These results do not establish general Bitcoin consensus equivalence or cryptographic correctness. Transaction validity and prevout provenance are caller-provided premises of the transaction-backed API. Private-key derivation uses variable-time arithmetic.

## Current roadmap

The repository has no separate roadmap file or open issues. Based on the current code, the next items are:

1. Add standard `combo()` and `addr()` descriptor support, then connect the parser, compiler, CLI, and conformance checks.
2. Expand raw fixture and BIP341/BIP342 vector coverage for the native Taproot verifier.
3. Move the partial semantics and theorem targets under `Experimental.lean` into stable APIs where appropriate.

## Repository structure

- `LeanMiniscript/` — Lean library, executable models, examples, and proofs
- `LeanMiniscript/Conformance/` — cross-module conformance checks
- `LeanMiniscript.lean` — stable library surface
- `LeanMiniscript/Experimental.lean` — extraction and proof-oriented modules under active change
- `scripts/` — pinned-source fixture generators and CLI checks
- `assets/` — repository artwork

## License

[MIT](LICENSE)
