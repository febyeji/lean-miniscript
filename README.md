# lean-miniscript

Lean 4 models, executable verification, and proofs for Bitcoin Miniscript.

## Build and check

Install the Lean version in `lean-toolchain`, then run:

```sh
lake build
python3 scripts/check_core_fixture_audit.py
```

The build checks all proofs and regression examples. The audit downloads a
checksum-pinned Bitcoin Core fixture and requires all 1,222 tests to match.
Use `--fixture <script_tests.json>` for an offline audit.

## Entry points

- `LeanMiniscript`: syntax, parsing, typing, compilation, and validation.
- `LeanMiniscript.Proofs`: semantic, satisfaction, and resource proofs.
- `LeanMiniscript.Experimental`: interpreters and evolving verification APIs.
- `LeanMiniscript.Miniscript.DescriptorParser`: WSH and Taproot descriptors with
  checksums and BIP32 key derivation.
- `LeanMiniscript.Extraction.TaprootBytes`: canonical Tapscript verification.
- `LeanMiniscript.Extraction.BitcoinCoreFixtures`: Core fixture preparation and execution.

Proofs establish the contracts stated in their Lean declarations. Fixture
matches provide regression coverage; general consensus equivalence and
cryptographic correctness remain outside those results. Private-key derivation
uses variable-time arithmetic.

Licensed under [MIT](LICENSE).
