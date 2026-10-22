<p align="center">
  <img src="assets/lean-miniscript-logo.svg" alt="lean-miniscript logo" width="180">
</p>

# lean-miniscript

- Lean 4 models, executable verification, and proofs for Bitcoin Miniscript.
- The codebase covers:
  - Miniscript syntax, parsing, pretty-printing, normalization, type inference, and validation.
  - Miniscript compilation, concrete compilation, malleability analysis, satisfaction availability, and metrics.
  - Spending policies: parsing and printing, denotational semantics, and a cost-based policy-to-Miniscript compiler whose output provably preserves the policy's meaning.
  - Bitcoin Script execution, control flow, signatures, Taproot, timelocks, and runtime limits.
  - Bitcoin transaction, descriptor, ECDSA, Schnorr, and Taproot serialization utilities.
  - PSBT (BIP174, BIP370, BIP371) parsing, serialization, roles, and descriptor-based finalization.

## Getting started

- Install the Lean version pinned in [`lean-toolchain`](lean-toolchain).
- Build the libraries, proofs, examples, and tests:

  ```sh
  lake build
  ```

- Run the Bitcoin Core fixture audit:

  ```sh
  curl --fail --location \
    https://raw.githubusercontent.com/bitcoin/bitcoin/f13ae519de94394314cd63a27924b0998ac65d45/src/test/data/script_tests.json \
    --output /tmp/script_tests.json
  lake exe core_fixture_audit -- --show-details /tmp/script_tests.json
  ```

- The audit downloads the fixture from the pinned Bitcoin Core revision and checks all 1,258 cases.
- The pinned `script_tests.json` comes from Bitcoin Core commit
  [`f13ae519de94394314cd63a27924b0998ac65d45`](https://github.com/bitcoin/bitcoin/commit/f13ae519de94394314cd63a27924b0998ac65d45),
  dated 2026-10-14, and contains 1,258 executable tests plus 60 documentation rows.
- PSBT test vectors are generated from pinned BIP174, BIP370, and BIP371 sources by
  `scripts/generate_psbt_fixtures.py`.

- Parse a hexadecimal-key policy into its Lean AST and print canonical text:

  ```sh
  lake exe policy_cli -- \
    'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
  ```

- Compile a policy for P2WSH or Tapscript:

  ```sh
  lake exe policy_cli -- compile --context tapscript \
    'and(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),older(100))'
  ```

- `compile` defaults to `p2wsh`. Its output includes canonical Miniscript,
  concrete Script hex, script size in bytes, static opcode count, and maximum
  satisfaction stack bounds. P2WSH also reports the maximum opcode charge.
- `lake exe policy_cli -- --help` lists the commands; `parse POLICY_TEXT` and the
  original single-policy invocation print the AST and canonical policy text.

- Inspect, finalize, or extract a PSBT:

  ```sh
  lake exe psbt_cli -- inspect --encoding hex "$PSBT_HEX"
  lake exe psbt_cli -- finalize "$SIGNED_PSBT_BASE64" "0=$DESCRIPTOR" |
    lake exe psbt_cli -- extract -
  ```

- Set the variables above to PSBT text and a descriptor with resolved keys.
  Input defaults to Base64; `--encoding hex` selects hex and `-` reads stdin.
  `finalize` uses existing signatures and accepts zero-based `INDEX=DESCRIPTOR`
  assignments. Unspecified inputs and existing final fields are preserved.
  Its output is a Base64 PSBT; `extract` requires final fields for every input
  and prints transaction hex. `inspect` reports PSBT version, input/output
  counts, and final-field presence. It does not verify existing final fields.
- `lake exe psbt_cli -- --help` lists the commands.
  Run `python3 scripts/test_psbt_cli.py` after building to check the executable
  against the pinned BIP174 and BIP370 vectors.

- Focused cross-module conformance checks live under `LeanMiniscript/Conformance/`,
  split by policy, descriptor, and PSBT behavior.

## Repository layout

- `LeanMiniscript/` — Lean libraries, executable models, examples, and proofs.
- `LeanMiniscript/Conformance/` — focused cross-module conformance checks.
- `LeanMiniscript.lean` — public module that imports the main library surface.
- `scripts/` — fixture generation helpers and CLI checks.
- `assets/` — project artwork, including the repository logo.

## Verification scope

- Proofs establish the contracts stated by their Lean declarations.
- PSBT finalization preserves the decoded unsigned transaction and resolved
  UTXOs, including v2 transaction fields and locktime. Generated final inputs
  pass a CompactSize length check; `finalizeAndExtract_spec` and
  `finalizeAndExtract_preserves` require no caller-supplied witness length bound.
- Fixture matches provide conformance coverage against the pinned Bitcoin Core data.
- General consensus equivalence and cryptographic correctness are outside those results.
- Private-key derivation uses variable-time arithmetic.

## License

- [MIT](LICENSE)
