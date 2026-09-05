# Miniscript Specification And Coverage Baseline

This document is the source of truth for which claims the repository currently
implements, states, or proves. A check mark never means more than the column
heading says: compilation coverage is not semantic soundness, and a stated
theorem target is not a proved theorem.

## Pinned Specification Baseline

- Compiler/conformance fixtures and the general specification baseline use
  `bitcoin/bips` commit
  [`c021a5f51ae9d3e71a41eac3dda6dc060fead35d`](https://github.com/bitcoin/bips/tree/c021a5f51ae9d3e71a41eac3dda6dc060fead35d).
  The relevant files are BIPs 65, 68, 141, 342, 379, 380, 382, and 386.
- Compiler differential fixtures use `rust-miniscript` 13.1.0 commit
  [`c9ed0006144ad92436191047edd4132f79e5916a`](https://github.com/rust-bitcoin/rust-miniscript/tree/c9ed0006144ad92436191047edd4132f79e5916a).
- The malleability judgment and inference use the newer BIP 379 transcription
  at `bitcoin/bips` commit
  [`442e9628b3dcca1b65f0df8af2308f8260e00caa`](https://github.com/bitcoin/bips/tree/442e9628b3dcca1b65f0df8af2308f8260e00caa)
  and are cross-checked against `rust-miniscript` commit
  [`cb8262253af383a1a5b17363f6a013848f20534b`](https://github.com/rust-bitcoin/rust-miniscript/tree/cb8262253af383a1a5b17363f6a013848f20534b).
  These subsystem-specific pins do not silently replace the older compiler
  fixture pins.
- Script execution and Bitcoin Core `script_tests.json` audits target
  Bitcoin Core v31.1 commit
  [`9be056a8a72b624dae9623b2f7bded92c2a21c91`](https://github.com/bitcoin/bitcoin/tree/9be056a8a72b624dae9623b2f7bded92c2a21c91).
  The Lean semantics remain a documented subset; the audit keeps unsupported
  rows visible rather than treating them as successful comparisons.
- Concrete key HASH160 uses `lean-hash160` commit
  [`d55f38607f76104609004cdaca27ef0e21f372b6`](https://github.com/febyeji/lean-hash160/tree/d55f38607f76104609004cdaca27ef0e21f372b6).
- The checked toolchain is `leanprover/lean4:v4.32.0`.

Changing a pin requires regenerating the affected fixtures and recording any
semantic or byte-level differences. External implementations are differential
oracles, not logical premises of Lean proofs.

## Semantic Conventions

- `Script.Stack` is top-first: the list head is the next element consumed.
- `Witness` is serialized bottom-to-top order. `Witness.toInitialStack` reverses
  it exactly once at the execution boundary.
- `Eval` describes instruction execution. It may finish successfully with any
  stack shape.
- `Accepts` additionally requires modeled context flags, an initially empty
  alt stack, exactly one final main-stack element, and a truthy top. The final
  alt stack is internal execution state and is not constrained by clean-stack.
- `Dissatisfies` is successful execution to the same one-item main-stack shape
  with a false top. It is distinct from a Script error.
- `ScriptFlags.minimalData` controls minimal Script-number operands. Both
  modeled acceptance contexts require it, while raw `Eval` can express the
  relaxed Bitcoin Core flag behavior.
- `TxContext` carries the signed transaction version, transaction locktime,
  and current-input sequence needed for the modeled BIP 65 and BIP 68/112
  checks. Its `Nat` locktime and sequence fields represent the corresponding
  unsigned transaction fields without imposing a machine-word representation.
- P2WSH and Tapscript validation remain separate through `ScriptContext`.
  `ModeledContextFlags` is not yet the full Bitcoin Core flag matrix.

## Representation Boundaries

- `PubKey`, `Hash256`, and `Hash160` remain byte-backed raw AST wrappers.
  Length, serialized key shape, and context validity are explicit `WellFormed`
  obligations; curve-point validity remains the responsibility of key
  resolvers before constructing checked compiler inputs.
- `SurfaceFragment` remains a normalized proof AST with embedded core
  fragments and explicit sugar, not a source-spelling-preserving parse tree.
  Its text codec targets a documented canonical round-trip rather than
  preserving the original spelling.
- Base58/WIF/xpub decoding and key derivation remain outside the Miniscript
  surface codec. Key tokens must pass through an explicit resolver to a
  concrete `PubKey`, followed by context validation.
- Compilation coverage is one-way from Miniscript to Script. Script
  deserialization and Script-to-Miniscript recognition are separate future
  work, not requirements for the current compiler claim.
- `CryptoOracle.model` retains the proof semantics' abstract hashes and
  signature checks. `CryptoOracle.pureLeanHashes` provides executable SHA-256,
  HASH256, RIPEMD-160, and HASH160 from the pinned `lean-hash160` package while
  leaving signature verification injectable; no production secp256k1 binding
  is currently part of the trusted runtime boundary.
- The Bitcoin Core fixture importer preserves positional JSON rows and compiles
  Core's number, quoted-data, raw-hex, and opcode tokens through their serialized
  Script-byte boundary. It rejects unsupported opcodes, P2SH evaluation,
  signature-result rows, witness rows, unmodeled flags, unmodeled failure tags,
  and non-minimal raw pushes under `MINIMALDATA` with structured reasons. The
  audit API retains source indices and exact mismatch details, and its CLI can
  display every unsupported row. Detailed audit categories preserve whether a
  source failure came from scriptSig or scriptPubKey and identify its first
  unsupported textual opcode or raw opcode byte.

## Legend

- **Done**: executable coverage and its local soundness/reflection theorem, when
  the column calls for one, are present.
- **Partial**: useful implementation exists, but a required semantic case or
  proof is still missing.
- **Example**: only a concrete local proof exists; there is no constructor-wide
  theorem.
- **Missing**: no implementation that can support the planned claim exists.

Compilation entries below include constructor-complete assembly/byte fixtures
and the relational BIP 379 conformance theorem. Evaluation is marked partial
for every row because exact Bitcoin Core failure coverage, production
signature verification, final acceptance results, and differential validation
are not yet complete. Within the modeled opcode subset, `Eval.exists_result`
and `Eval.result_unique` prove that the relational semantics has exactly one
result for every fixed initial state. The total `evaluate` function covers the
same cases, and `evaluate_model_iff` proves equivalence for the model oracle.
Resource coverage means exact serialized size and sigop accounting plus
provisional structural estimates;
`ResourceBoundsSound` remains unproved.

## Core Constructor Matrix

| Constructor | Validation | Correctness typing | Malleability typing | Compilation | Evaluation | Satisfy | Dissatisfy | Resources | Semantic proof |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `zero` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `one` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `pk_k` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Example |
| `pk_h` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `older` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `after` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `sha256` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `hash256` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `ripemd160` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `hash160` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `and_v` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `and_b` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `or_b` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `or_c` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `or_d` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `or_i` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `andor` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `a` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Example chain only |
| `s` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `c` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Example chain only |
| `d` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `v` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Example chain only |
| `j` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `n` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `thresh` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `multi` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |
| `multi_a` | Done | Done | Done | Done | Partial | Missing | Missing | Partial | Missing |

`HasType ctx` covers all rows, and `inferType ctx` has soundness, completeness,
uniqueness, and success/reflection theorems. A constructor-exhaustive fixture
set checks one context-valid exact type per core row, while branch-sensitive
fixtures exercise the nontrivial modifier-propagation alternatives in the
pinned BIP 379 correctness table. The context index gives `d:` its
Tapscript-only `u` property; positive Tapscript and negative P2WSH fixtures cover
every parent rule that consumes this Bdu result. Key shape, multisig opcode
availability, and other structural restrictions remain separate `WellFormed`
obligations at the checked boundary.

`HasMalleability` likewise covers all rows. `inferMalleability` has soundness,
completeness, uniqueness, and success/reflection theorems, with build-checked
constructor fixtures; `nonMalleable` records the separate recursive guarantee.
This is static analysis coverage, not a semantic non-malleability theorem
against an attacker model.

Evaluation coverage remains partial. `Eval` has explicit terminal main-stack
underflow results for all 23 positive fixed-arity opcodes and alternate-stack
underflow for `OP_FROMALTSTACK`, with an exhaustive opcode-arity fixture and
local result-uniqueness lemmas. A canonical signed-magnitude decoder now
enforces minimal encoding plus the ordinary four-byte and timelock five-byte
limits. `ADD`, `BOOLAND`, `BOOLOR`, `0NOTEQUAL`, `NUMEQUAL`, `CHECKSIGADD`,
CLTV, and CSV decode arbitrary stack bytes and report typed overflow,
non-minimal, and negative-timelock failures; every numeric decoder-error group
has a local result-uniqueness lemma. CLTV additionally enforces height/time
class compatibility, transaction-locktime comparison, and a non-final current
input. CSV implements the operand disable-bit NOP and otherwise enforces
transaction version, input disable bit, height/time type compatibility, and
the masked low-16-bit comparison. Context failures and negative operands also
have local result-uniqueness lemmas. Legacy `CHECKMULTISIG` now decodes arbitrary
public-key and signature count elements in Bitcoin Core's validation order,
enforces `0 ≤ k ≤ n ≤ 20`, checks each variable stack-frame boundary, places
the historical dummy below the signatures, and reports typed count,
Script-number, underflow, and NULLDUMMY failures. Bitcoin Core op-counting,
signature-encoding and NULLFAIL errors, unmodeled raw-script error precedence,
context-invalid opcodes, and full failure completeness remain unfinished.
`Eval.exists_result` proves relational result existence for every modeled
script and initial state, using strict conditional-branch length decrease;
combined with `Eval.result_unique`, `Eval.existsUnique_result` proves global
existence and result determinism for the modeled relation.
`evaluate` implements every modeled opcode as a terminating function returning
`ExecResult`; `OP_NOP` preserves both stacks and continues with the literal
tail. `evaluate_eq_of_eval` and `evaluate_sound` prove refinement for
any `CryptoOracle` that agrees pointwise with the abstract model, and
`evaluate_model_iff` packages the model-oracle equivalence. Executable fixtures
cover arithmetic, conditional toggles, typed failures, the pinned pure-Lean
SHA-256 implementation, and injected signature results. A native secp256k1
oracle and full semantic support for the Bitcoin Core differential suite remain
future work.
The initial importer targets the pinned v31.1 positional JSON and textual
fixture syntax, including raw `0x...` byte concatenation. Nineteen verbatim
positive rows run offline through the evaluator and cover direct and PUSHDATA
pushes, `OP_NOP`, conditional branches with repeated `ELSE`, stack/arithmetic
behavior, SHA256, HASH256, RIPEMD160, and HASH160. Unsupported execution modes
and unmodeled expected-error rows remain visible as explicit classifications
rather than being dropped from the comparison boundary. `coreScriptErrorTag`
maps all modeled evaluator failures to Core tags. Fourteen verbatim rejection
rows cover final-false results, stack and alt-stack underflow, VERIFY/EQUALVERIFY,
Script-number overflow and non-minimal operands, malformed conditionals,
negative and unsatisfied CSV, and CHECKMULTISIG count failures. Signature
callbacks remain excluded unless the expected error is guaranteed to occur
before cryptographic verification. Running `core_fixture_audit` on the complete
pinned file currently classifies 1,222 tests: 306 supported rows all match,
with zero mismatches and 916 rows retained under explicit unsupported reasons.
Conditional execution uses an executable depth-aware splitter: nested
delimiters stay within their branch, repeated same-depth `ELSE` opcodes toggle
selected segments as in Bitcoin Core, and a missing matching `ENDIF` or
top-level `ELSE`/`ENDIF` produces a typed unbalanced-conditional failure. The
unclosed-frame projection executes only the alternating active segments first:
an active runtime failure takes precedence, while successful execution through
EOF becomes `UNBALANCED_CONDITIONAL`. Relational, executable, and fixture-level
regressions cover active, inactive, and repeated-`ELSE` cases.

## Surface Constructor Matrix

| Constructor | Validation via core | Typing via core | Desugaring/compilation | Parser/pretty-printer | Evaluation | Satisfy/dissatisfy | Surface theorem |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `core` | Done | Done | Done | Done | Partial | Missing | Done |
| `pk` | Done | Done | Done | Done | Partial | Missing | Done |
| `pkh` | Done | Done | Done | Done | Partial | Missing | Done |
| `and_n` | Done | Done | Done | Done | Partial | Missing | Done |
| `t` | Done | Done | Done | Done | Partial | Missing | Done |
| `l` | Done | Done | Done | Done | Partial | Missing | Done |
| `u` | Done | Done | Done | Done | Partial | Missing | Done |

`SurfaceFragment` is currently a thin recursive sugar layer around embedded
core fragments, not a source-preserving concrete-syntax tree. The executable
codec normalizes equivalent core shapes to their canonical surface sugar,
accepts an explicit key resolver, checks resolved keys against the selected
context, and reports structured token, arity, number, hash, key, context,
validation, and trailing-input failures.
Constructor-exhaustive canonical golden fixtures and every structured error tag
are build-checked. General theorems prove that normalization preserves
desugaring, is idempotent, and is stable under canonical pretty-printing. The
`surfaceTextRoundTrip` proves the `SurfaceTextRoundTrip` contract: parsing
canonical hexadecimal output returns the normalized surface fragment for every
context-valid input.

## Checked Contract Targets

The following declarations type-check without `sorry`, `admit`, or a new axiom,
but are propositions to be proved rather than completed theorems:

- `TypeSoundnessCore` and `TypeSoundnessSurface` require context validity,
  relational typing, and an explicitly supported non-vacuous semantic case;
- `SatisfactionCorrectnessCore` and `SatisfactionCorrectnessSurface` require a
  sound material environment and conclude `Accepts`;
- `DissatisfactionCorrectnessCore` and its surface counterpart require the `d`
  modifier and conclude `Dissatisfies`; and
- `ResourceBoundsSound` gives the first conservative combined main/alt-stack
  growth target for successful compiler-output evaluation.

The immediate proof work must extend named semantic predicates before extending
`SupportedMiniType`. Unsupported modifier combinations do not reduce to `True`.
