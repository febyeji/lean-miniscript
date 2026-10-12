# lean-miniscript

Lean 4 models, executable verification, and proofs for Bitcoin Miniscript.

Install the Lean version in `lean-toolchain`, then run:

```sh
lake build
python3 scripts/check_core_fixture_audit.py
```

The build checks proofs and regression tests. The audit downloads checksum-pinned
Bitcoin Core fixtures and requires all 1,222 tests to match.

Proofs establish the contracts stated in their Lean declarations. Fixture
matches provide regression coverage; general consensus equivalence and
cryptographic correctness remain outside those results. Private-key derivation
uses variable-time arithmetic.

Licensed under [MIT](LICENSE).
