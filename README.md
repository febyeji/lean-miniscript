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

`lake exe core_fixture_audit --show-details <script_tests.json>` compares all
1,222 executable rows against the exact result tags in the pinned Bitcoin Core
fixture. The report also retains 51 documentation rows and reports unsupported
syntax, flags, or malformed witness metadata in other input documents.

CI runs `python3 scripts/check_core_fixture_audit.py` after `lake build`. The
script downloads `src/test/data/script_tests.json` at Bitcoin Core revision
`9be056a8a72b624dae9623b2f7bded92c2a21c91` and verifies SHA-256
`bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5` before
execution. Every test row must match: 1,222 matches, zero mismatches and zero
unsupported rows. CI retains the complete report in the `core-fixture-audit`
artifact.

For an offline run, build `lake build core_fixture_audit`, then pass a local
copy with `python3 scripts/check_core_fixture_audit.py --fixture <script_tests.json>`.
The local copy must have the same checksum. Run the gate's failure-path tests
with `python3 -B -m unittest discover -s scripts -p 'test_check_core_fixture_audit.py' -v`.

Fixture preparation preserves original script bytes, exact satoshi amounts,
and wire-order witness elements. It constructs Core's crediting and spending
transactions and expands the generated Taproot script/control/output templates.
Expected result tags are used only after execution, when comparing outcomes.

The raw execution boundary supports SHA1 and CODESEPARATOR, legacy resource
limits, conditional execution, minimal pushes, timelock activation flags, P2SH,
SIGPUSHONLY and CLEANSTACK. Native and P2SH-wrapped witness-v0 verification
checks program commitments, witness shape, public-key policy and final stack
acceptance. Taproot verification handles script commitments, annexes, signature
budgets, OP_SUCCESS and key-path signatures. Each reached ECDSA or Schnorr check
uses the transaction-derived digest for that signature's hash type. BASE
FindAndDelete and separator handling preserve the original byte boundaries.

The ECDSA, SHA1, legacy/BIP143 sighash and full verification implementations
have executable vector and boundary coverage. The 1,222 fixture matches do not
establish general consensus equivalence or cryptographic correctness. Existing
AST and legacy-preflight theorems retain their stated scope. Four new general
theorems cover script-size rejection and the precedence of SIGPUSHONLY,
scriptSig and scriptPubKey failures. The canonical Tapscript API above retains
its separate input and proof boundaries.

## Related Work

- [Simplicity](https://github.com/BlockstreamResearch/simplicity) — Coq-formalized blockchain language (Blockstream)
- [dgpv Alloy spec](https://github.com/dgpv/miniscript-alloy-spec) — Alloy model of Miniscript (model checking, not theorem proving)
- [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) — Reference implementation

## License

MIT.
