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

- Focused cross-module conformance checks live under `LeanMiniscript/Conformance/`,
  split by policy, descriptor, and PSBT behavior.

## Repository layout

- `LeanMiniscript/` — Lean libraries, executable models, examples, and proofs.
- `LeanMiniscript/Conformance/` — focused cross-module conformance checks.
- `LeanMiniscript.lean` — public module that imports the main library surface.
- `scripts/` — fixture generation helpers.
- `assets/` — project artwork, including the repository logo.

## Verification scope

- Proofs establish the contracts stated by their Lean declarations.
- Fixture matches provide conformance coverage against the pinned Bitcoin Core data.
- General consensus equivalence and cryptographic correctness are outside those results.
- Private-key derivation uses variable-time arithmetic.

## License

- [MIT](LICENSE)
