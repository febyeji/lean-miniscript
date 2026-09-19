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
- Basic metrics and resource accounting are implemented. `ResourceBoundsSound`
  is proved: successful execution grows the final combined main/alt stack by at
  most the compiled instruction count. The proof applies to every modeled
  Script and has core, surface, and runtime corollaries. `RuntimeStackBounds`
  additionally bounds every reachable prefix before combined-stack checks.
  `maxStackGrowth` refines the compiled instruction-count allowance by charging
  only pushes and opcodes that may grow the combined stacks (with a conservative
  charge for `CHECKMULTISIG`). When initial combined size plus this allowance is
  at most 1,000, those checks cannot reject and omitting them preserves the full
  result, including failures, under explicit oracle agreement. Whole-program
  success is not a premise. The allowance charges both conditional branches and
  is not an exact path-sensitive peak.
- The modeled big-step relation includes depth-aware conditional selection plus
  explicit stack-underflow, Script-number, unbalanced-conditional, and
  variable-frame `CHECKMULTISIG` failures; Core-aligned BIP 65 and
  BIP 68/112 transaction-context checks cover CLTV and CSV, together with
  NULLFAIL behavior for ECDSA signature opcodes and global theorems that
  every modeled initial state has exactly one result. ECDSA CHECKSIG and legacy
  CHECKMULTISIG enforce DERSIG, LOW_S, and STRICTENC with typed DER, high-S,
  sighash-type, and public-key-format errors. Multisignature matching checks
  only reached pairs, then applies NULLFAIL and historical-dummy checks.
  Execution versions distinguish legacy, witness-v0, and Tapscript rules.
  Tapscript CHECKSIG/CHECKSIGADD enforce Schnorr size and sighash encoding,
  public-key version rules, and terminal verification errors; CHECKSIGADD is
  unavailable before Tapscript, while CHECKMULTISIG is disabled in Tapscript.
  Witness-v0 optionally enforces compressed-key policy.
  Transaction-backed `execTapscriptTransaction` computes BIP341/342 signing
  hashes per signature using bounded transaction fields, aligned spent outputs,
  the selected input, annex and TapLeaf extension. It derives timelock fields
  from that same input. Hash messages and digests match all seven official
  BIP341 wallet cases and 56 additional pinned-Core reference cases offline.
  Abstract contexts can still supply a hash. `CryptoOracle.pureLeanSchnorr`
  connects an executable pure-Lean BIP340 verifier, checked against all 19
  official vectors and independently signed transaction execution cases.
  ECDSA remains caller-supplied, with rejection as the default. Curve and
  verifier correctness and refinement of the abstract oracle are not proved.
  `execCommittedTapscriptTransaction` parses a complete wire-order witness,
  validates its control-block commitment against the selected native P2TR
  spent output, then executes the modeled script with transaction hashing and
  the full witness budget. All 12 official BIP341 control blocks match,
  including an unknown leaf version in the standalone commitment checker.
  The execution entry explicitly excludes key paths and future leaf versions.
  Full-witness execution checks initial argument count and element size, then
  runs a source-order interpreter enforcing combined main/alt-stack depth after
  each instruction and push sizes even inside inactive branches. Earlier opcode
  failures retain precedence over later oversized pushes.
  `verifyCommittedTapscriptTransaction` additionally checks the modeled flag
  contract and final clean-stack/truth conditions, returning the unused
  signature budget with distinct setup and Script errors. Its acceptance check
  is proved equivalent to `TapscriptAccepts` under explicit oracle agreement.
  `evaluateWithValidationWeight` / `WeightedEval` add BIP342 validation-weight
  accounting and return the remaining weight with both stacks. `execTapscript`
  initializes it from the full serialized input witness, including script,
  control block and annex. `TapscriptAccepts` / `TapscriptDissatisfies` expose
  the resource-aware clean-stack boundary. The budget-only `WeightedEval`
  relation retains refinement, determinism and successful execution's erasure
  to resource-free `Eval`. The full entry uses `RuntimeEval` with conditional
  oracle refinement and determinism; its stack/push bound proofs require no
  oracle agreement. `RuntimeErasure` proves that successful source-order
  execution preserves both stacks and the remaining budget in the older
  branch-projection evaluator for every oracle, and connects model execution
  to `WeightedEval` and `Eval`. Resource failures need not agree.
  An oracle-parameterized `evaluate` function executes that same modeled
  subset; its model-oracle result is proved equivalent to `Eval`, while the
  executable oracle uses the pinned pure-Lean hashes and accepts injected
  signature checks. A conservative importer parses Bitcoin Core's positional
  `script_tests.json` format and fixture Script syntax; 19 pinned positive
  non-signature rows exercise pushes, control flow, stack operations, and all
  four executable hash operations without silently accepting unsupported
  flags or execution modes. Fourteen pinned rejection rows additionally compare
  final-false behavior and exact Core tags for the modeled failure classes;
  `OP_NOP` preserves both stacks, and unclosed conditionals preserve Core's
  active-branch runtime-error precedence. Fifteen additional pinned encoding
  rejection rows match with both accepting and rejecting signature oracles;
  a verifier-dependent BIP66 row remains explicitly unsupported.
  A checked-in audit command runs a complete fixture file, compares every
  supported row, and reports each unsupported row by structured reason.
  Execution behavior targets
  [Bitcoin Core v31.1](https://github.com/bitcoin/bitcoin/tree/9be056a8a72b624dae9623b2f7bded92c2a21c91)
  at the pinned commit recorded in the coverage baseline; `Eval` remains a
  documented subset rather than a complete Bitcoin Core interpreter.
- Basic candidate generation is executable for constants, key leaves and their
  `c` wrappers, timelocks, all four 32-byte hashlocks, and linear propagation
  through `a`, `s`, `v`, and `n`, the guarded `d` and `j` rows, and the
  straight-line `and_v`, `and_b`, and `or_b` connectives, plus conditional
  `or_c`, `or_d`, `or_i`, and `andor`, exact-count `thresh` selection, and
  both `multi` encodings. Paired candidates track HASSIG, DONTUSE, canonical
  origin, and additive witness cost. `thresh` and `multi_a` share a
  proof-carrying arithmetic guard that rejects threshold literals at or above
  `2^31` and retains their exact four-byte decode result under both
  minimal-data modes. Key leaves have exact K-frame lemmas; B
  leaves and well-typed `c` wrappers have arbitrary-stack lemmas leading to
  clean acceptance or dissatisfaction. Wrapper lemmas additionally prove the
  two exact W stack orders, truthy B-to-V conversion, `n`'s explicit
  Script-number normalization boundary, local guarded execution contracts for
  `d` and `j`, B/K/V
  composition through `and_v`, and both exact W stack orders plus numeric decode
  premises for `and_b`/`or_b`. Balanced IF/NOTIF frame lemmas additionally
  prove the `or_c` B-to-V paths, `or_d` B paths, and `or_i`/`andor` B/K/V paths;
  child-produced selectors keep explicit truth and MINIMALIF premises, while
  canonical `or_i` selectors discharge MINIMALIF internally. Threshold
  accumulator lemmas support both W stack orders and retain an explicit numeric
  decode premise for every `OP_ADD`; final `OP_EQUAL` uses byte equality. The
  legacy multisignature contract proves the compiled key-push and canonical
  count frame, then requires the explicit `checkMultiSigFor` result and the
  true-or-NULLFAIL condition used by Script execution. The Tapscript
  multisignature contract keeps its execution version explicit, records every
  CHECKSIG/CHECKSIGADD result and accumulator decode, and retains the final
  NUMEQUAL decode premise.
  Recursive generated-witness soundness for these wrappers, connectives, and
  thresholds, and the connection from selected multisignature candidates to
  cryptographic key/signature matching remain unfinished.
- General soundness, full satisfaction coverage, non-malleability, small-step
  semantics, cryptographic correctness proofs, executable ECDSA verification,
  unsupported Core failure classes,
  and full semantic coverage of the Bitcoin Core differential suite are
  unfinished. The older `Eval` / `Accepts` APIs are resource-free; complete
  budget checks use the full-witness Tapscript APIs above. Legacy/BIP143
  transaction-derived sighashes and Taproot key-path execution remain TODO.
  The older Tapscript entry points
  still require callers to validate the control-block commitment. Script execution covers Miniscript-generated opcodes;
  arbitrary CODESEPARATOR execution is outside the current AST.
  The Miniscript acceptance contract requires its matching execution version.

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

The pinned file currently reports 1,222 tests: 321 compared and matched, zero
mismatches, and 901 explicitly unsupported. Pass `--show-details` before the
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
