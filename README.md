# lean-miniscript

**Lean 4 proof-of-work for Bitcoin Miniscript semantics and type soundness.**

lean-miniscript is a small Lean 4 codebase for modeling the part of Bitcoin
Script used by Miniscript, then stating the proof obligations needed to connect
compiled fragments to the stack behavior promised by the Miniscript type system.

## Current status

- Core syntax, typing, and compilation cover every current `CoreFragment`.
- Surface syntax and policy lowering are partial.
- Basic metrics and resource accounting are implemented, but not proved.
- Partial big-step semantics and a few soundness lemmas are implemented.
- General soundness, satisfaction, non-malleability, small-step semantics, and
  the interpreter are unfinished.

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
