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

## Getting started

- Install the Lean version pinned in [`lean-toolchain`](lean-toolchain).
- Build the libraries, proofs, examples, and tests:

  ```sh
  lake build
  ```

- Run the Bitcoin Core fixture audit:

  ```sh
  python3 scripts/check_core_fixture_audit.py
  ```

- The audit downloads checksum-pinned Bitcoin Core fixtures and checks all 1,222 cases.

## Repository layout

- `LeanMiniscript/` — Lean libraries, executable models, examples, and proofs.
- `LeanMiniscript.lean` — public module that imports the main library surface.
- `scripts/` — fixture generation and audit helpers.
- `assets/` — project artwork, including the repository logo.

## Verification scope

- Proofs establish the contracts stated by their Lean declarations.
- Fixture matches provide regression coverage against the pinned Bitcoin Core data.
- General consensus equivalence and cryptographic correctness are outside those results.
- Private-key derivation uses variable-time arithmetic.

## License

- [MIT](LICENSE)
