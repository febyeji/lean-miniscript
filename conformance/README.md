# Compiler conformance fixtures

The Lean fixtures in
`LeanMiniscript/Miniscript/CompileExamples.lean` are pinned to:

- `bitcoin/bips` commit
  `c021a5f51ae9d3e71a41eac3dda6dc060fead35d`, specifically the BIP 379
  translation table; and
- `rust-miniscript` 13.1.0 commit
  `c9ed0006144ad92436191047edd4132f79e5916a`.

`LeanMiniscript/Miniscript/CompileExamples.lean` links each constructor tag to
a concrete fragment, BIP-style assembly, and serialized bytes. Its completeness
theorems cover all 27 `CoreFragment` constructors and all 7 `SurfaceFragment`
constructors, and its match theorems build-check every assembly/byte pair.

`rust-miniscript-13.1.0.txt` independently records
`constructor | input expression | serialized bytes` for those same 34 rows.
The core `pk_h` result cross-checks the concrete HASH160 value computed by the
commit-pinned `lean-hash160` dependency. The readable assembly literals are
checked in Lean against `Script.toAssembly`; the byte columns are cross-checked
against the rust-miniscript oracle.

Beyond the finite fixtures, `Miniscript/Conformance.lean` proves that the
executable compiler is exactly characterized by a constructor-wise relational
BIP 379 translation. `Miniscript/Structural.lean` proves balanced conditional
control flow for every related core script and therefore for all core and
surface compiler output. Opcode closure is type-level: `Script.Opcode` is the
complete modeled universe, so no `Script` value can contain an unmodeled opcode.

## Reproduce the oracle output

```bash
git clone --depth 1 --branch miniscript-13.1.0 \
  https://github.com/rust-bitcoin/rust-miniscript.git \
  /tmp/rust-miniscript-13.1.0
cp conformance/rust_miniscript_oracle.rs \
  /tmp/rust-miniscript-13.1.0/examples/conformance_dump.rs
cd /tmp/rust-miniscript-13.1.0
cargo run --quiet --example conformance_dump
```

Compare stdout with `rust-miniscript-13.1.0.txt`. The generator uses the
public expression-tree parser and `FromTree` instead of the top-level
`Miniscript::from_str` entrypoint. This is intentional: BIP 379 translation
rows include K, V, and W fragments that are not valid top-level B Miniscripts.
`FromTree` still parses and type-checks each fragment but does not reject it
solely for not being a sane top-level spending policy.

The fixtures use `v:older(42)` where a V fragment is needed. rust-miniscript
optimizes forms such as `v:pk(...)` to `CHECKSIGVERIFY`, while this Lean model
currently emits the equally valid general `CHECKSIG VERIFY` scheme. Choosing a
fragment with no specialized VERIFY opcode keeps the byte comparison exact and
does not hide an oracle difference.

`multi` is generated under the Segwit v0 context. `multi_a` is generated under
the Tapscript context with x-only keys.
