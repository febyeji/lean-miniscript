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

A separate legacy byte interpreter handles reserved and disabled opcodes,
invalid bytes, and truncated pushes in source order. Its raw fallback excludes
witness and P2SH evaluation, decoded signature operations, scripts over 10,000
bytes or 201 counted opcodes, and nonminimal pushes under MINIMALDATA. Typed
fixture execution retains its existing resource-free boundary. These fixture
extensions preserve the canonical Tapscript API's OP_SUCCESSx boundary.

## Related Work

- [Simplicity](https://github.com/BlockstreamResearch/simplicity) — Coq-formalized blockchain language (Blockstream)
- [dgpv Alloy spec](https://github.com/dgpv/miniscript-alloy-spec) — Alloy model of Miniscript (model checking, not theorem proving)
- [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) — Reference implementation

## License

MIT.
