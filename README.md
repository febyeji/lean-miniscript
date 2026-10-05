# lean-miniscript

**Lean 4 proof-of-work for Bitcoin Miniscript semantics and type soundness.**

lean-miniscript is a small Lean 4 codebase for modeling the part of Bitcoin
Script used by Miniscript, then stating the proof obligations needed to connect
compiled fragments to the stack behavior promised by the Miniscript type system.

## Building

Requires [Lean 4](https://lean-lang.org/) (see `lean-toolchain` for version).

```bash
lake build
```

## Canonical Tapscript verification

Import `LeanMiniscript.Extraction.TaprootBytes` to use
`LeanMiniscript.Extraction.verifyCanonicalTapscriptTransaction`. Pass a crypto
oracle, full wire-order witness, Script flags, transaction, spent outputs, and
input index. The verifier checks the native P2TR commitment, decodes the script
from the witness, and performs modeled final acceptance. Success returns the
remaining signature-validation budget.

The API supports canonical encodings of the modeled opcode subset. Its errors
distinguish setup/commitment failures, decoding failures, non-canonical script
encodings, and execution/acceptance failures. Unsupported opcodes (including
OP_SUCCESSx) and non-canonical encodings indicate the API's support boundary.
Key paths, future leaf versions, transaction validity, and prevout provenance
retain the existing extraction boundary's limits.

`LeanMiniscript.Extraction.TaprootBytesProofs` proves agreement with the AST
verifier for successfully prepared witnesses carrying that AST's canonical
bytes. Its acceptance theorem additionally requires the oracle to refine the
abstract cryptographic model. `TaprootBytesExamples` contains executable
signature, annex, resource, decoding, and error-precedence regressions.

## Bitcoin Core fixture audit

`lake exe core_fixture_audit --show-details <script_tests.json>` compares
supported fixtures against the result tags in the pinned Bitcoin Core fixture
file. The report retains unsupported rows and their reasons.

CI runs `python3 scripts/check_core_fixture_audit.py` after `lake build`. The
script downloads `src/test/data/script_tests.json` at Bitcoin Core revision
`9be056a8a72b624dae9623b2f7bded92c2a21c91` and verifies SHA-256
`bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5` before
execution. It requires 1,222 test rows, 51 documentation rows, zero mismatches,
and at least 977 matching fixtures. CI retains the complete report, including
unsupported categories and details, in the `core-fixture-audit` artifact. Raise
`MINIMUM_MATCHED` in the script when support expands.

For an offline run, build `lake build core_fixture_audit`, then pass a local
copy with `python3 scripts/check_core_fixture_audit.py --fixture <script_tests.json>`.
The local copy must have the same checksum. Run the gate's failure-path tests
with `python3 -B -m unittest discover -s scripts -p 'test_check_core_fixture_audit.py' -v`.

A legacy byte interpreter handles reserved and disabled opcodes, invalid bytes,
and truncated pushes in source order. Fixture execution checks the original
10,000-byte script limit, the 201-operation limit (including active multisig key
counts and inactive opcodes), 520-byte pushes, and 1,000 combined stack items.
Original push encodings enforce MINIMALDATA in active branches after the
push-size check; inactive pushes retain their branch behavior. Preparation
excludes witness and P2SH evaluation, unmodeled operations and flags, and
execution paths that reach a signature verifier. Zero-signature multisig and failures before a verifier call are
compared. Admission and execution use the same concrete Lean hash functions;
caller-supplied signature callbacks remain outside admitted paths. These fixture
extensions preserve the canonical Tapscript API's OP_SUCCESSx boundary.

## Related Work

- [Simplicity](https://github.com/BlockstreamResearch/simplicity) — Coq-formalized blockchain language (Blockstream)
- [dgpv Alloy spec](https://github.com/dgpv/miniscript-alloy-spec) — Alloy model of Miniscript (model checking, not theorem proving)
- [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) — Reference implementation

## License

MIT.
