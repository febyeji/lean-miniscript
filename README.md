# lean-miniscript

**Lean 4 proof-of-work for Bitcoin Miniscript semantics and type soundness.**

lean-miniscript is a small Lean 4 codebase for modeling the part of Bitcoin
Script used by Miniscript, then stating the proof obligations needed to connect
compiled fragments to the stack behavior promised by the Miniscript type system.

## Current status

- Core syntax, context-indexed correctness typing, and compilation cover every
  current `CoreFragment`; typing has constructor-complete BIP 379 fixtures, and
  compilation has constructor-complete assembly/byte fixtures plus a general
  relational conformance theorem.
- Surface compilation covers every current `SurfaceFragment` constructor via
  explicit desugaring; policy lowering is not implemented.
- Canonical surface parsing and pretty-printing are executable with structured
  errors and an explicit key resolver. Constructor-exhaustive golden fixtures
  and normalization/desugaring proofs are present, together with a general
  parser/pretty-printer round-trip theorem for context-valid fragments.
- Compiler output is proved to use the model's closed opcode universe and to
  have balanced conditional control flow.
- Executable `pk_h`/`pkh` compilation uses the commit-pinned, pure Lean
  [`lean-hash160`](https://github.com/febyeji/lean-hash160) package while the
  general formal semantics retain an abstract hash boundary.
- Basic metrics and resource accounting are implemented, but not proved.
- The modeled big-step relation includes depth-aware conditional selection plus
  explicit stack-underflow, Script-number, unbalanced-conditional, and
  variable-frame `CHECKMULTISIG` failures; Core-aligned BIP 65 and
  BIP 68/112 transaction-context checks cover CLTV and CSV, together with
  global theorems that every modeled initial state has exactly one result.
  An oracle-parameterized `evaluate` function executes that same modeled
  subset; its model-oracle result is proved equivalent to `Eval`, while the
  executable oracle uses the pinned pure-Lean hashes and accepts injected
  signature checks. A conservative importer parses Bitcoin Core's positional
  `script_tests.json` format and fixture Script syntax; 16 pinned positive
  non-signature rows exercise pushes, control flow, stack operations, and all
  four executable hash operations without silently accepting unsupported
  flags or execution modes. Thirteen pinned rejection rows additionally compare
  final-false behavior and exact Core tags for the modeled failure classes;
  unclosed conditionals preserve Core's active-branch runtime-error precedence.
  A checked-in audit command runs a complete fixture file, compares every
  supported row, and reports each unsupported row by structured reason.
  Execution behavior targets
  [Bitcoin Core v31.1](https://github.com/bitcoin/bitcoin/tree/9be056a8a72b624dae9623b2f7bded92c2a21c91)
  at the pinned commit recorded in the coverage baseline; `Eval` remains a
  documented subset rather than a complete Bitcoin Core interpreter.
- General soundness, satisfaction, non-malleability, small-step semantics,
  production secp256k1 bindings, unsupported Core failure classes, and the
  full semantic coverage of the Bitcoin Core differential suite are unfinished.

See [`MINISCRIPT_COVERAGE.md`](MINISCRIPT_COVERAGE.md) for the constructor-level
coverage matrix, proof-status legend, semantic conventions, and subsystem pins.

## Building

Requires [Lean 4](https://lean-lang.org/) (see `lean-toolchain` for version).

```bash
lake build
```

## Auditing Bitcoin Core fixtures

Run the pinned Bitcoin Core v31.1
[`script_tests.json`](https://github.com/bitcoin/bitcoin/blob/9be056a8a72b624dae9623b2f7bded92c2a21c91/src/test/data/script_tests.json)
through the supported comparison boundary:

```bash
lake exe core_fixture_audit -- path/to/script_tests.json
```

The pinned file currently reports 1,222 tests: 268 compared and matched, zero
mismatches, and 954 explicitly unsupported. Pass `--show-details` before the
path to split source failures by scriptSig/scriptPubKey and their first
unsupported textual opcode or raw opcode byte. Pass `--show-unsupported` to
print every excluded row and its structured reason; the two options can be
combined. Parse failures return exit code 2 and supported-row mismatches return
exit code 1; unsupported rows alone do not make the command fail.

## Related Work

- [Simplicity](https://github.com/BlockstreamResearch/simplicity) — Coq-formalized blockchain language (Blockstream)
- [dgpv Alloy spec](https://github.com/dgpv/miniscript-alloy-spec) — Alloy model of Miniscript (model checking, not theorem proving)
- [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) — Reference implementation

## License

MIT.
