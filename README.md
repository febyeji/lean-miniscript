# lean-miniscript

**Lean 4 proof-of-work for Bitcoin Miniscript semantics and type soundness.**

lean-miniscript is a small Lean 4 codebase for modeling the part of Bitcoin
Script used by Miniscript, then stating the proof obligations needed to connect
compiled fragments to the stack behavior promised by the Miniscript type system.

## Current status

- Core syntax, typing, and compilation cover every current `CoreFragment`;
  compilation also has constructor-complete assembly/byte fixtures and a
  general relational conformance theorem.
- Surface compilation covers every current `SurfaceFragment` constructor via
  explicit desugaring; policy lowering remains a placeholder.
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
- Partial big-step semantics and a few soundness lemmas are implemented.
- General soundness, satisfaction, non-malleability, small-step semantics, and
  the interpreter are unfinished.

See [`MINISCRIPT_COVERAGE.md`](MINISCRIPT_COVERAGE.md) for the constructor-level
coverage matrix, proof-status legend, semantic conventions, and subsystem pins.

## Building

Requires [Lean 4](https://lean-lang.org/) (see `lean-toolchain` for version).

```bash
lake build
```

## Related Work

- [Simplicity](https://github.com/BlockstreamResearch/simplicity) — Coq-formalized blockchain language (Blockstream)
- [dgpv Alloy spec](https://github.com/dgpv/miniscript-alloy-spec) — Alloy model of Miniscript (model checking, not theorem proving)
- [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) — Reference implementation

## License

MIT — same as Bitcoin Core and rust-miniscript.
