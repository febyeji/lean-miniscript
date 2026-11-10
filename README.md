<p align="center">
  <img src="assets/lean-miniscript-logo.svg" alt="lean-miniscript logo" width="180">
</p>

# lean-miniscript

Lean models of Bitcoin Miniscript, Script, Taproot, descriptors, transactions, and PSBT, with proofs and checks against pinned fixtures.

## Build

Install the Lean version in [lean-toolchain](lean-toolchain), then run from the repository root:

```sh
lake build
```

This checks the library, proofs, and tests, and builds the CLIs below.

## Policy CLI

Parse a policy and print its canonical form:

```sh
lake exe policy_cli -- \
  'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
```

Compile it for Tapscript, or use `--context p2wsh` for P2WSH:

```sh
lake exe policy_cli -- compile --context tapscript \
  'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
```

Output includes Miniscript, Script hex, script size, static opcode count, and stack bounds.

Print a descriptor's scriptPubKeys. `combo()` prints each output; `--index N` resolves `*` wildcards:

```sh
lake exe policy_cli -- descriptor \
  'combo(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798)'
lake exe policy_cli -- --help
```

## PSBT CLI

Set the variables to your PSBT text and a descriptor with resolved keys. Bindings use zero-based `INDEX=DESCRIPTOR`; include each input that needs finalization before extraction:

```sh
lake exe psbt_cli -- inspect --encoding hex "$PSBT_HEX"
lake exe psbt_cli -- finalize "$SIGNED_PSBT_BASE64" "0=$DESCRIPTOR" \
  | lake exe psbt_cli -- extract -
```

`inspect` reports input finalization status. Input defaults to Base64; `--encoding hex` selects hex and `-` reads stdin. `finalize` prints a Base64 PSBT; `extract` requires all inputs finalized and prints transaction hex.

After the build, run the CLI checks with Python 3:

```sh
python3 scripts/test_psbt_cli.py
```

## Bitcoin Core fixture audit

Download the fixture pinned in [CI](.github/workflows/ci.yml), then compare its expected results with the model:

```sh
curl --fail --location \
  https://raw.githubusercontent.com/bitcoin/bitcoin/f13ae519de94394314cd63a27924b0998ac65d45/src/test/data/script_tests.json \
  --output /tmp/script_tests.json
lake exe core_fixture_audit -- --show-details /tmp/script_tests.json
```

Check `mismatched` and `unsupported` in the summary. Unsupported rows are excluded from comparison; the command succeeds when all compared rows match. Add `--show-unsupported` to inspect excluded rows.

## Equivalence checks

After `lake build`, run:

```sh
lake env lean --run scripts/equivalence_obligations.lean
lake env lean --run scripts/script_equivalence_obligations.lean
lake env lean --run scripts/core_loop_fallbacks.lean
```

- `equivalence_obligations.lean` counts unproved opcode/version obligations.
- `script_equivalence_obligations.lean` counts unproved Script and VerifyScript obligations.
- `core_loop_fallbacks.lean` counts instruction kinds whose representative scripts have no typed reading. `decodeTypedScript?_isSome` proves that every script has one, so the typed executor never runs the modeled Core raw loop.

A zero obligation count means every listed theorem has the expected type and uses only standard Lean axioms. Read the count even when the command succeeds. Add `--list` for `proved`/`missing`/`sorry` or `typed`/`fallback` entries. The fallback check fails if a Script or VerifyScript obligation is unproved.

Proofs concern the Lean models and their stated assumptions. Fixture matches and obligation counts do not establish general Bitcoin consensus equivalence or cryptographic correctness. Transaction-backed APIs assume valid transactions and correct prevout data; private-key derivation uses variable-time arithmetic. See [AI_USAGE.md](AI_USAGE.md) for proof verification rules.

## Source

- [LeanMiniscript.lean](LeanMiniscript.lean) — stable library exports
- [LeanMiniscript/Experimental.lean](LeanMiniscript/Experimental.lean) — extraction and proof modules under active development
- [LeanMiniscript/Conformance/](LeanMiniscript/Conformance/) — cross-module checks
- [scripts/](scripts/) — fixture generators and CLI checks

## License

[MIT](LICENSE)
