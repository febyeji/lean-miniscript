# lean-miniscript

**Lean 4 proof-of-work for Bitcoin Miniscript semantics and type soundness.**

lean-miniscript is a small Lean 4 codebase for modeling the part of Bitcoin
Script used by Miniscript, then stating the proof obligations needed to connect
compiled fragments to the stack behavior promised by the Miniscript type system.

## Current scope

- Lean models of Miniscript syntax and the Bitcoin Script fragment it compiles
  to.
- Surface-to-core Miniscript desugaring, partial typing, and compilation.
- Big-step semantics for the target Script fragment, with theorem skeletons for
  soundness and related properties.

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
