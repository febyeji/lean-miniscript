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
- BIP340 verification fixtures and reference-signed execution fixtures use
  `bitcoin/bips` commit
  [`55083d36ddebcd2a039135a2f4ee74917a5803d3`](https://github.com/bitcoin/bips/tree/55083d36ddebcd2a039135a2f4ee74917a5803d3),
  files `bip-0340/test-vectors.csv` and `bip-0340/reference.py`. Source SHA256
  digests are enforced by `scripts/generate_schnorr_fixtures.py`.
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
  leaving signature verification injectable. `CryptoOracle.pureLeanSchnorr`
  additionally supplies executable BIP340 verification; its ECDSA callback
  defaults to rejection. No native secp256k1 dependency is required. The
  abstract oracle refinement premises remain explicit; concrete curve and
  verifier correctness have vector coverage but no general Lean proof.
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
Resource coverage means exact serialized size and sigop accounting plus proved
conservative stack bounds. `resourceBoundsSound` proves the existing
`ResourceBoundsSound` contract: final main/alt-stack size is at most the initial
combined size plus compiled instruction count. `RuntimeStackBounds` extends
this guarantee to every reachable prefix before stack-size checks.
`maxStackGrowth` gives each compiled fragment a static allowance no larger than
the compiled instruction count, and often lower, by
counting only pushes and opcodes that may grow the combined stacks. Exact
path-sensitive peak analysis remains unfinished.

## Core Constructor Matrix

| Constructor | Validation | Correctness typing | Malleability typing | Compilation | Evaluation | Satisfy | Dissatisfy | Resources | Semantic proof |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `zero` | Done | Done | Done | Done | Partial | Missing | Basic | Partial | Basic dissatisfaction |
| `one` | Done | Done | Done | Done | Partial | Basic | Missing | Partial | Basic satisfaction |
| `pk_k` | Done | Done | Done | Done | Partial | Leaf candidate | Leaf candidate | Partial | K frame; `c` soundness |
| `pk_h` | Done | Done | Done | Done | Partial | Leaf candidate | Leaf candidate | Partial | K frame; `c` soundness |
| `older` | Done | Done | Done | Done | Partial | Basic | Missing | Partial | Basic satisfaction |
| `after` | Done | Done | Done | Done | Partial | Basic | Missing | Partial | Basic satisfaction |
| `sha256` | Done | Done | Done | Done | Partial | Basic | DONTUSE candidate | Partial | Exact sat/dsat frames |
| `hash256` | Done | Done | Done | Done | Partial | Basic | DONTUSE candidate | Partial | Exact sat/dsat frames |
| `ripemd160` | Done | Done | Done | Done | Partial | Basic | DONTUSE candidate | Partial | Exact sat/dsat frames |
| `hash160` | Done | Done | Done | Done | Partial | Basic | DONTUSE candidate | Partial | Exact sat/dsat frames |
| `and_v` | Done | Done | Done | Done | Partial | Composed candidate | Non-canonical candidate | Partial | B/K/V frame composition |
| `and_b` | Done | Done | Done | Done | Partial | Composed candidate | Selected candidate | Partial | B/W BOOLAND frame |
| `or_b` | Done | Done | Done | Done | Partial | Selected candidate | Composed candidate | Partial | B/W BOOLOR frame |
| `or_c` | Done | Done | Done | Done | Partial | Selected candidate | Impossible | Partial | B-to-V conditional frames |
| `or_d` | Done | Done | Done | Done | Partial | Selected candidate | Composed candidate | Partial | IFDUP conditional B frames |
| `or_i` | Done | Done | Done | Done | Partial | Selected candidate | Selected candidate | Partial | Canonical-selector B/K/V frames |
| `andor` | Done | Done | Done | Done | Partial | Selected candidate | Selected candidate | Partial | Guarded B/K/V branch frames |
| `a` | Done | Done | Done | Done | Partial | Pass-through | Pass-through | Partial | Saved-first W frame |
| `s` | Done | Done | Done | Done | Partial | Pass-through | Pass-through | Partial | Singleton/result-first W frame |
| `c` | Done | Done | Done | Done | Partial | Basic (key leaves) | Basic (key leaves) | Partial | Basic soundness |
| `d` | Done | Done | Done | Done | Partial | Guarded candidate | Canonical false | Partial | Vz true / canonical false frames |
| `v` | Done | Done | Done | Done | Partial | Pass-through | Impossible | Partial | Truthy B-to-V frame |
| `j` | Done | Done | Done | Done | Partial | Pass-through | Guarded choice | Partial | Nonempty child / canonical zero frames |
| `n` | Done | Done | Done | Done | Partial | Pass-through | Pass-through | Partial | ScriptNum-normalized B frame |
| `thresh` | Done | Done | Done | Done | Partial | Exact-count candidate | Canonical/overcomplete choice | Partial | Local accumulator frame |
| `multi` | Done | Done | Done | Done | Partial | Exact-count signatures | Canonical empty signatures | Partial | Local CHECKMULTISIG frame |
| `multi_a` | Done | Done | Done | Done | Partial | Exact-count signatures | Canonical empty signatures | Partial | Local CHECKSIGADD frame |

Key-leaf candidates follow the BIP 379 serialized witness rows: `pk_k` uses
`sig`/`0`, while `pk_h` uses `sig key`/`0 key`. Wrapper `c` preserves the
child pair and supplies the pending signature to the K execution frame. Hash
preimages must be exactly 32 bytes. Their canonical 32-byte nonpreimage
dissatisfactions have an exact false execution proof but remain DONTUSE, so
they are retained by the raw candidate API and omitted by the public usable
witness projection.

Candidate generation is total over the raw AST, so structural `c` propagation
also computes for ill-typed terms. Semantic correctness claims require the
existing context-valid typing boundary and prove `c` execution only for K
children.

Linear wrappers retain the child's serialized witness. Wrappers `a`, `s`, and
`n` preserve the complete candidate pair, including HASSIG, DONTUSE, origin,
and cost; `v` preserves satisfaction and makes dissatisfaction impossible.
Their stack-frame lemmas keep the operational side conditions explicit: `a`
restores the protected element above the B result, `s` requires the child's
single argument and leaves its result above the protected element, `v` requires
a truthy B result, and `n` requires the exact child result to decode as a
four-byte Script number. Raw-AST propagation therefore does not by itself
establish that a wrapper is well typed.

Guarded wrappers now have their local BIP 379 candidate rows. Wrapper `d`
appends a canonical true selector to child satisfaction and supplies the
canonical false dissatisfaction. Wrapper `j` preserves child satisfaction and
selects between its canonical empty dissatisfaction and a non-canonical child
dissatisfaction whose first runtime item has nonzero byte length. This guard
tests byte length, not Script truthiness, and preserves the child's HASSIG and
DONTUSE metadata before selection.

The corresponding arbitrary-stack lemmas remain local execution contracts:
`d` requires a zero-argument V child for its true branch and also proves the
canonical false branch; `j` requires exact B execution on `top :: args`,
`top.size ≠ 0`, and successful four-byte decoding of `scriptNat top.size`, and
also proves its canonical empty branch. These lemmas do not yet establish
recursive soundness for witnesses produced by the candidate algorithm.

The straight-line connectives `and_v`, `and_b`, and `or_b` now implement all
their BIP 379 candidate rows. Sequential candidate composition stores the
second child's witness first while execution consumes the first child's frame
first. `and_v` retains its Script-valid non-canonical dissatisfaction;
`and_b` and `or_b` run their three alternatives through the shared left-folded
selection algebra, marking both `and_b` rows and the `or_b` row overcomplete.
HASSIG, DONTUSE, origin, and additive cost continue to come from the shared
candidate operations, including DONTUSE hash dissatisfactions.

Their local arbitrary-stack contracts compose `and_v` with B, K, and V result
children. The `and_b` and `or_b` contracts support both exact W output orders
and require `decodeBinaryScriptNums` to succeed for the physical top-first
operand order before `OP_BOOLAND` or `OP_BOOLOR` executes. Result-first W
frames use Boolean commutativity to expose one canonical source-child result
order. These contracts preserve arbitrary main-stack suffixes and the complete
alternate stack. They do not yet prove recursive soundness for witnesses
selected by the candidate algorithm.

The conditional connectives `or_c`, `or_d`, `or_i`, and `andor` now implement
their BIP 379 candidate rows. `or_c` and `or_d` select between direct X
satisfaction and composed `dsat(X) sat(Y)`; only `or_d` composes both child
dissatisfactions. `or_i` appends canonical true and false selectors before
selecting each satisfaction or dissatisfaction pair, so selector serialization
cost participates in the shared HASSIG/DONTUSE choice. `andor` selects
`sat(X) sat(Y)` against `dsat(X) sat(Z)` and selects canonical
`dsat(X) dsat(Z)` against the non-canonical `sat(X) dsat(Y)`. That alternate
`andor` dissatisfaction is marked non-canonical without being marked
overcomplete, so its inherited usability remains intact. All sequential rows
use `Witness.combine`, retaining second-child-before-first-child wire order and
first-child-before-second-child runtime order.

Reusable balanced IF/NOTIF frame lemmas prove exact one- and two-branch
execution while preserving arbitrary main-stack suffixes and the alternate
stack. Local connector contracts cover `or_c` B-to-V paths, `or_d` B paths,
and `or_i` and `andor` B/K/V paths. Selectors produced by a child retain
separate `minimalIfSatisfied` and `castToBool` premises; `or_i` discharges
MINIMALIF internally for its canonical selectors. No numeric decoding premise
is used for these branch selectors. These local contracts do not yet prove
recursive soundness for witnesses selected by the candidate algorithm.

Threshold candidates use a shared exact-count dynamic-programming table. State
`j` holds the selected witness with exactly `j` satisfied children; each step
combines the previous witness with the next child's dissatisfaction without
changing `j`, or with its satisfaction while incrementing `j`. Combination
preserves source execution order and reverse serialized witness-block order,
and the ordinary HASSIG/DONTUSE/cost selection rules apply within each state.
Valid `thresh(k, ...)` satisfaction selects state `k`. Dissatisfaction starts
with the canonical all-dissatisfied state zero, skips state `k`, and considers
every other positive state only after marking it DONTUSE and non-canonical as
an overcomplete row. A shared candidate guard requires `1 ≤ k ≤ n` and carries
exact four-byte Script-number decode evidence for `k` under both minimal-data
modes. Raw `k = 0`, empty, `k > n`, and arithmetic-unsafe `k ≥ 2^31` forms
have no candidates; the type system already excludes the arity failures.

The proof-only candidate provenance layer shows that a usable `select` output
came unchanged from one input, a usable `combine` output decomposes into both
usable child witnesses, and selector, non-canonical, runtime-top, and legacy
multisignature-finalizer transforms preserve their exact witness relation. Its
`ChoiceTrace` theorem recovers one source-order child witness for each usable
exact-count output and proves that reversing the combined serialized witness
produces the flattened source-order runtime frames. A usable threshold
dissatisfaction is traced only to the canonical zero-satisfaction head; no
converse is claimed for retained DONTUSE or overcomplete rows. This is
candidate provenance, not a recursive child-execution soundness theorem.

The local threshold execution contract covers a nonempty B child followed by
W children and `OP_ADD`. It supports both saved-first and result-first W stack
orders, and requires an explicit successful `decodeBinaryScriptNums` premise
for every addition. The accumulator is carried as canonical Script-number
bytes; the final literal `k` and `OP_EQUAL` proof uses byte equality directly.
It does not infer four-byte arithmetic decodability from typing and does not
claim recursive soundness for generated child witnesses. The candidate guard
now supplies the expected count's arithmetic bound and decode evidence, while
the compiled threshold still performs final byte equality. Accumulator and
child-result decode premises remain explicit until that recursive connection
is proved.

Legacy `multi(k, keys)` candidates use the same exact-count table over keys in
source order. Each available signature is a HASSIG satisfaction choice and an
empty block is its dissatisfaction choice. Source-order processing makes an
equal-cost tie retain earlier keys. Finalization prepends the historical empty
dummy and reverses the selected one-item signature blocks, producing wire order
`0 sig...` in source key order and top-first runtime order with signatures above
the dummy. The canonical dissatisfaction contains `k + 1` empty items. Raw
`k = 0`, `k > n`, and `n > 20` forms have no candidates on either side.

The local legacy multisignature execution contract proves the exact
`compileKeyPushes` frame and decoder result, including canonical count
encodings, reversed top-first public keys, selected top-first signatures, the
empty dummy, and the untouched stack suffix. Its public premises retain the
non-Tapscript version, 20-key and threshold bounds, exact signature count,
`checkMultiSigFor` result, and the true-or-NULLFAIL condition. NULLDUMMY is
discharged by the canonical empty dummy; the all-empty dissatisfaction also
discharges NULLFAIL. This does not prove that the candidate table's chosen
signatures form the key subsequence accepted by the caller-supplied ECDSA
oracle, and it does not provide recursive generated-witness soundness.

Tapscript `multi_a(k, keys)` uses the exact-count table directly in source key
order. An available signature contributes a one-item HASSIG satisfaction and
an empty signature contributes the canonical dissatisfaction. The selected
wire blocks are already in reverse source order, so no legacy finalizer or
dummy is added; reversing the complete witness at runtime restores source key
order for CHECKSIG followed by CHECKSIGADD. The canonical dissatisfaction has
one empty item per key. The same shared guard rejects `k = 0`, `k > n`, and
arithmetic-unsafe `k ≥ 2^31`. There is deliberately no 20-key guard for this
Tapscript form.

`CheckSigAddTailExecution` relates source-order keys and signatures to an exact
`Int` accumulator. Each step retains the exact `decodeCheckSigAddCount` result
and version-aware `checkSigWithEncoding` result. The nonempty compiler frame
handles the first CHECKSIG separately, and `BExecution.multiA` requires an
explicit Tapscript execution version plus the final `decodeBinaryScriptNums`
result for NUMEQUAL. Empty-signature helpers prove the canonical false path,
but no theorem derives the accumulator decode bounds from `WellFormed` or ties
the candidate table's selected signatures to cryptographic verification.

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
Script-number, underflow, and NULLDUMMY failures. Pre-Tapscript `CHECKSIG` and
`CHECKMULTISIG` enforce NULLFAIL after a rejected cryptographic check: nonempty
signatures produce `SIG_NULLFAIL`, while empty signatures retain the ordinary
false result; the relational and executable semantics agree on these branches.
ECDSA `CHECKSIG` and legacy `CHECKMULTISIG` now check signature and public-key
bytes before cryptographic verification. DERSIG, LOW_S, and STRICTENC select
strict DER, low-S, defined sighash, and compressed/uncompressed-key checks,
reporting `SIG_DER`, `SIG_HIGH_S`, `SIG_HASHTYPE`, and `PUBKEYTYPE` in Core's
order. Empty signatures bypass signature encoding but still check the key.
LOW_S preserves Core's lax scalar-overflow behavior: overflow of either scalar
produces an invalid zeroed signature that passes the low-S check.
Multisignature matching uses the same per-key `checkSig` boundary instead of an
opaque aggregate callback, checking only reached pairs and stopping when too
few keys remain. Matching errors precede NULLFAIL; NULLFAIL precedes missing
dummy and NULLDUMMY checks. The decoder therefore retains a missing dummy as
`none` until matching finishes. Byte fixtures cover each DER rejection branch,
all 256 sighash bytes, scalar boundaries, selective matching, skipped inputs,
and competing terminal errors. Global existence, determinism, and evaluator
refinement remain proved for this expanded relation.
`TxContext.sigVersion` distinguishes BASE, WITNESS_V0, and TAPSCRIPT, with BASE
as the default for raw Script callers. P2WSH and Tapscript acceptance additionally
require the matching execution version. P2WSH enables STRICTENC; Tapscript
ignores DERSIG, LOW_S, STRICTENC, and NULLFAIL in its signature checks.
The version-aware `checkSigWithEncoding` boundary is shared by `Eval` and
`evaluate`. Under Tapscript it reports `TAPSCRIPT_EMPTY_PUBKEY` before Schnorr
encoding; a 32-byte key accepts an empty signature as false without calling any
verifier. Nonempty signatures must be 64 bytes with an implicit default, or 65
bytes with one of `01`, `02`, `03`, `81`, `82`, `83`. Other lengths report
`SCHNORR_SIG_SIZE`; explicit default and reserved sighash types report
`SCHNORR_SIG_HASHTYPE`; a rejected cryptographic check reports `SCHNORR_SIG`
independently of NULLFAIL. Unknown nonempty key versions accept nonempty
signatures without checking their encoding or crypto; the optional
DISCOURAGE_UPGRADABLE_PUBKEYTYPE flag rejects those keys, even with empty
signatures. These rules target the pinned Core interpreter and
[BIP342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki).
`CryptoOracle.checkSchnorrSig` is separate from its ECDSA callback and receives
64 signature bytes plus the caller-supplied signature hash. `pureLeanHashes`
defaults this new callback to rejection unless explicitly supplied.
CHECKSIGADD reports BAD_OPCODE before stack/count validation outside Tapscript;
within Tapscript it decodes the accumulator before signature checks. Tapscript
CHECKMULTISIG reports TAPSCRIPT_CHECKMULTISIG before any frame decoding. Skipped
conditional branches do not execute either opcode. WITNESS_PUBKEYTYPE optionally
requires compressed keys only under WITNESS_V0, following ordinary ECDSA byte
checks; matching still examines only reached pairs.
Build-checked version fixtures cover all 256 explicit Schnorr sighash bytes,
length boundaries, verifier dispatch and signature-byte stripping, empty and
upgradable key versions, policy flags, count/error priority, disabled opcodes,
and skipped branches. Existence, determinism, and evaluator refinement remain
proved for all modeled versions.
`Eval` and `evaluate` remain resource-free opcode interfaces.
`ValidationWeightCore.lean` defines `WeightedEval` and `evaluateWithValidationWeight`,
composing single-opcode transitions with BIP342 resource debits. Nonempty
signatures cost 50, including unknown key versions; empty signatures and skipped
branches cost zero. Exhaustion reports `TAPSCRIPT_VALIDATION_WEIGHT` before
key/signature/oracle checks, after arity and CHECKSIGADD count decoding.
`WeightedResult.success` carries remaining weight across sequential execution.
`initialValidationWeight` is 50 plus the CompactSize-prefixed serialization of
**all** input-witness items. `TapscriptWitness` explicitly includes arguments,
script bytes, control block and optional annex; `evaluateTapscript` / `execTapscript`
bind the canonical modeled script to those bytes and check the annex marker.
They then check the initial argument stack: at most 1,000 elements, each at
most 520 bytes. Count errors (`STACK_SIZE`) precede size errors (`PUSH_SIZE`),
and both precede opcode execution. Script bytes, control block and annex are
excluded from these argument limits but remain included in the signature budget.
`TapscriptAccepts` / `TapscriptDissatisfies` apply clean-stack and modeled flags to
this budget-checked full-witness boundary. The older `Accepts`, satisfaction
lemmas and type-guarantee targets remain resource-free and must not be cited
as budget-aware acceptance results.
`evaluateWithValidationWeight_eq_of_eval`, `evaluateWithValidationWeight_sound`,
`weighted_model_iff` and `WeightedEval.deterministic` prove budget-only
refinement, existence and determinism. `WeightedEval.erase_success` proves
successful budgeted execution has the same result in `Eval`.
Fixtures cover CompactSize boundaries, exact exhaustion, repeated checks,
unknown key charging, count/error precedence, skipped/nested/duplicate-ELSE
branches, witness-size initialization and annex-funded signature reuse.
`checkTapscriptInitialStack_ok_iff` characterizes the exact input bounds, and
`evaluateTapscript_initialStack` proves them for every successful full-witness
execution. `RuntimeLimits.lean` adds source-order traversal with an explicit
conditional stack. Push sizes are checked before dispatch, including in inactive
branches and for canonical numeric pushes. The combined main/alt-stack count
is checked after each instruction, with the inclusive 1,000-element bound.
Opcode errors precede that count check; earlier failures precede later pushes.
The full-witness entry now uses `evaluateWithRuntimeLimits`. The public
`ValidationWeight` import continues to export the original budget-only API.
The AST has no OP_SUCCESSx, so no unconditional-success bypass is
represented. The older entry points require caller control-block validation; `execCommittedTapscriptTransaction`
validates that commitment as described below. Boundary-only script-byte and annex errors have
explicit `MODEL_` audit tags; they are not presented as Core consensus errors.

`RuntimeEval` composes source-order steps using the model oracle and existing
single-opcode execution. `evaluateRuntime_eq_of_eval`, `evaluateRuntime_sound`,
`runtime_model_iff` and `RuntimeEval.deterministic` establish conditional oracle
refinement, existence and determinism for this relation. `runtimeStep_stackBound`
and `runtimeStep_pushBound` apply to every successful transition;
`evaluateRuntime_bounds` and `evaluateTapscript_runtimeBounds` prove final combined
stack bounds and bounds for every source push on success, without an oracle
agreement premise. These runtime enforcement properties are separate from the
final-state growth bound proved by `resourceBoundsSound`.

`RuntimeErasure.lean`, exported through `LeanMiniscript.Proofs`, closes the
whole-script success-preservation bridge. `evaluateWithRuntimeLimits_erase_success`
proves that runtime success preserves both stacks and the remaining signature
budget in `evaluateWithValidationWeight`, for every oracle and with no script
length or control-flow restriction. The proof covers arbitrary nesting and
repeated ELSE segments by relating source-order projection to the existing
conditional splitter. `RuntimeEval.toWeightedEval` and `RuntimeEval.erase_success`
connect successful model execution to `WeightedEval` and resource-free `Eval`.
`evaluateWithRuntimeLimits_eval_success` gives the executable-to-`Eval` result
under oracle agreement. This is a success implication; additional runtime
resource failures need not match the older evaluator's result. It does not
establish cryptographic correctness. The separate `StackGrowth` proof below
supplies the static final-state bound.
Runtime regressions cover both limits, main/alt-stack transfers, transient
overflow, nested/repeated-ELSE/NOTIF control flow, inactive pushes, signature
budget reuse and failure precedence. Two exact pinned Core PUSH_SIZE source
rows (active and inactive pushes) are compared separately through the new
runtime evaluator. They do not change the conservative BASE audit counts.
An additional 44,444 small-program/input combinations compare source-order
execution with the budget-only branch-projection evaluator below the limits.
`Bitcoin.Transaction` represents uint32 version/locktime/sequences and outpoint
indices, uint64 amounts, wire-order transaction IDs, input/output vectors and
raw scripts. `TaprootSigHashContext` requires spent outputs aligned with every
input, even for ANYONECANPAY, and validates input bounds, txid lengths, annex
markers and even leaf versions. It does not prove transaction consensus validity
or that supplied prevouts match the chain.
`taprootSignatureMessage` constructs epoch 0, BIP341 SigMsg and optional BIP342
TapLeaf/key-version/CODESEPARATOR extension. All seven defined hash types are
supported. Missing SIGHASH_SINGLE outputs fail instead of receiving a zero-hash
fallback. `taprootSignatureHash` uses the pinned pure-Lean SHA256 implementation
with the TapSighash tag; its linkage to the complete message API is proved by
`taprootSignatureHash_of_message`. This is not a cryptographic security or full
BIP-conformance theorem.
`TxContext.taproot` enables per-signature transaction hashing. `checkedVerifySigFor`
preserves hash failures separately from rejected Schnorr checks. Known-key
nonempty Tapscript signatures compute their own hash-type-specific digest;
unknown key versions and empty signatures bypass hash computation. Missing
SINGLE output availability maps to `SCHNORR_SIG_HASHTYPE`. Legacy/witness-v0
and abstract Tapscript contexts retain caller-supplied hashes.
`evaluateTapscript` binds signing annex and leaf bytes to the full witness,
uses leaf version 0xc0 and no executed CODESEPARATOR (0xffffffff), and derives
timelock fields from the signing transaction/input. `execTapscriptTransaction`
exposes this transaction-backed, budget-aware entry point.
`evaluateTapscript_eq_model` and `execTapscriptTransaction_eq_model` prove
oracle refinement through full-witness binding and transaction-context setup.
The standalone hash API permits explicit CODESEPARATOR positions, but the Script AST does not
execute that opcode: BIP379 Miniscript compilation never emits it.
Offline fixtures compare exact transaction serialization, all five component
hashes, seven official signing preimages/digests and 56 additional valid pinned
Core cases spanning all hash types, annex presence, key/script path and three
CODESEPARATOR positions. Script fixtures verify per-signature dispatch with
different hash types in the same execution, stripping to 64 bytes, overriding
stale metadata, SINGLE failure, unknown-key bypass, signed transaction version,
and ALL/NONE/ANYONECANPAY commitment boundaries.
The source pins and SHA256 checks are in
`scripts/generate_taproot_sighash_fixtures.py`; reproduce both fixture modules:

```sh
python3 scripts/generate_taproot_sighash_fixtures.py --wallet-vectors WALLET_JSON --core-script CORE_SCRIPT_PY --output LeanMiniscript/Bitcoin/TaprootSighashExamples.lean
python3 scripts/generate_sighash_execution_fixtures.py --wallet-vectors WALLET_JSON --core-script CORE_SCRIPT_PY --output LeanMiniscript/Script/SighashExecutionExamples.lean
```

`WALLET_JSON` is BIP341 `wallet-test-vectors.json` at BIPs commit
`55083d36ddebcd2a039135a2f4ee74917a5803d3`; `CORE_SCRIPT_PY` is
`test/functional/test_framework/script.py` at the pinned Core commit. Core's
test helper can serialize deliberately invalid SINGLE cases by zero-filling;
these cases are excluded from valid hash fixtures and Lean explicitly rejects
them as required by BIP341. CI runs checked-in fixtures without network access.
The generator checks every official message/digest/component before producing
additional cases, and regenerated modules must match byte-for-byte.

Legacy/BIP143 transaction-derived sighashes, executable ECDSA verification,
Taproot key-path execution, Bitcoin Core op-counting,
other unmodeled raw-script errors, and full failure completeness remain unfinished.
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
SHA-256 implementation, and injected signature results. Executable Schnorr
verification is described below; full semantic support for the Bitcoin Core
differential suite remains future work.
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
negative and unsatisfied CSV, and CHECKMULTISIG count failures. Fifteen additional
verbatim encoding-error rows
compare exact tags with both accepting and rejecting signature oracles; one
verbatim BIP66 row whose later error depends on matching stays excluded.
Signature callbacks remain excluded unless execution is shown to fail before
the first verifier call. A straight-line signature-free prefix and the first
pair's byte checks establish that boundary independently of the expected tag;
signature-containing conditional prefixes remain conservatively unsupported.
The prior 3-of-3 nonzero-dummy row is now excluded because its matching must
consult a verifier before the dummy can be checked. Running `core_fixture_audit`
on the complete pinned file currently classifies 1,222 tests: 321 supported
rows all match, with zero mismatches and 901 explicitly unsupported rows.
Conditional execution uses an executable depth-aware splitter: nested
delimiters stay within their branch, repeated same-depth `ELSE` opcodes toggle
selected segments as in Bitcoin Core, and a missing matching `ENDIF` or
top-level `ELSE`/`ENDIF` produces a typed unbalanced-conditional failure. The
unclosed-frame projection executes only the alternating active segments first:
an active runtime failure takes precedence, while successful execution through
EOF becomes `UNBALANCED_CONDITIONAL`. Relational, executable, and fixture-level
regressions cover active, inactive, and repeated-`ELSE` cases.

Satisfaction now has executable candidate rows for constants, `pk_k`, `pk_h`,
their `c` wrappers, timelocks, all four hashlocks, linear wrapper propagation
through `a`, `s`, `v`, and `n`, guarded wrappers `d` and `j`, and straight-line
connectives `and_v`, `and_b`, and `or_b`, plus conditional connectives `or_c`,
`or_d`, `or_i`, and `andor`, thresholds, legacy `multi`, and Tapscript
`multi_a`. Paired candidates retain HASSIG, DONTUSE, canonical origin, and
additive witness cost
metadata while the public projection returns only usable witnesses. Signature
and key material use serialized witness order, and timelock availability reuses
the exact `TxContext` predicates from Script execution. `thresh` and `multi_a`
share a proof-carrying arithmetic threshold guard that records the signed
four-byte bound and exact relaxed and minimal decode facts. Boundary fixtures
accept `2^31 - 1`; `2^31` and above expose no candidate or public projection.
Hash preimages and nonpreimages are required to be exactly 32 bytes; canonical
hash dissatisfactions remain available to recursive proofs as DONTUSE candidates,
including through `a`, `s`, and `n`. For `j`, the hash dissatisfaction's
DONTUSE influence propagates to the selected canonical-zero result, while the
original nonpreimage representative is not retained.

Arbitrary-stack soundness lemmas connect returned B witnesses to `Accepts` or
`Dissatisfies`; timelock lemmas expose the numeric well-formedness premises that
the eventual validity theorem must discharge. `SatEnv.Sound` records signature,
preimage, and nonpreimage obligations at the cryptographic boundary. Basic key
satisfaction additionally requires `SatEnv.EncodingSound`, and key
dissatisfaction requires the empty-signature/key pair to pass the selected
version-specific byte checks. Guarded wrappers `d` and `j` and the supported
straight-line and conditional connectives have the local arbitrary-stack
contracts described above, without a recursive theorem tying every generated
candidate to child execution. Thresholds have the local accumulator contract
described above, without a recursive theorem connecting their selected table
entry to every child execution. Legacy `multi` has the local canonical decoder
and CHECKMULTISIG execution contract described above, without a theorem tying
the selected candidate to an accepted signature/key subsequence. Tapscript
`multi_a` has the local CHECKSIG/CHECKSIGADD accumulator contract described
above, without a theorem tying its selected candidate to those explicit
signature-check and numeric-decode premises.

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
  cryptographically sound material environment and encoding soundness under
  the selected flags and execution version, and conclude `Accepts`;
- `DissatisfactionCorrectnessCore` and its surface counterpart require the `d`
  modifier and version-specific empty-signature/key encoding for the supported signature fragment, and
  conclude `Dissatisfies`.

`ResourceBoundsSound` is now proved by `resourceBoundsSound` in
`Properties/ResourceBoundsProofs.lean`, exported through `LeanMiniscript.Proofs`.
The underlying `Eval.stackGrowth` theorem in `Script/StackGrowth.lean` applies to
every modeled Script, with arbitrary initial main/alt stacks, flags, and
transaction context; no typing or initial resource-bound premise is needed.
It bounds final combined stack size by initial combined size plus source
instruction count. The proof handles dynamic CHECKMULTISIG frames and nested
or repeated-ELSE conditionals. `compile_stackGrowth` and
`compileSurface_stackGrowth` specialize it to core and surface compilation.
`RuntimeEval.stackGrowth` reuses success erasure, and
`evaluateWithRuntimeLimits_stackGrowth` exposes the executable result under
explicit oracle agreement. These are final-state bounds, not peak-stack
analysis or a guarantee that execution avoids resource failures.

`Script/RuntimeStackBounds.lean`, also exported through `LeanMiniscript.Proofs`,
adds conservative intermediate-state guarantees. `RuntimePrefix` composes
`executeRuntimeElement` before combined-stack checks, retaining the other
instruction checks. Prefixes may leave conditionals open or precede a later
execution failure. `runtimePrefix_iff` identifies this relation with the
proof-facing `runRuntimePrefix` function, which returns the intermediate state
without an end-of-script conditional check.

`executeRuntimeElement_stackGrowth` bounds each completed instruction's growth
by one item. `RuntimePrefix.stackGrowth` therefore bounds every reachable
prefix endpoint by initial combined size plus visited source instruction count.
`RuntimePrefix.stackBound` and `RuntimePrefix.checkStack_ok` prove that initial
combined size plus whole-program instruction count at most `maxStackSize`
(1,000) makes every such endpoint pass the combined-stack check. These facts
are proved from the pre-check instruction function, not from successful
resource enforcement. `compile_prefix_stackBound` and
`compileSurface_prefix_stackBound` provide compiler corollaries.

`ScriptElement.stackGrowthAllowance` charges one item only to data and numeric
pushes, `DUP`, `IFDUP`, `SIZE`, and conservatively `CHECKMULTISIG`; every other
modeled opcode has zero combined-stack growth allowance.
`RuntimePrefix.stackGrowth_le_allowance` proves that the sum for the visited source
prefix bounds every reachable intermediate combined stack. `maxStackGrowth`
applies that sum to compiled core fragments, and
`compile_prefix_maxStackGrowth` plus its surface counterpart connect it to the
runtime relation. The allowance is always at most compiled instruction count.
It charges inactive branches and does not subtract earlier consumption, so it
is a sound fragment-specific upper bound rather than an exact peak.

`evaluateRuntime_eq_runRuntimePrefix` proves that under the same allowance the
production evaluator equals the prefix runner followed by the existing final
conditional check. This preserves both successful and failing results; it does
not assume whole-program success.
`evaluateRuntime_eq_runRuntimePrefix_of_allowance` proves the same equality
under the refined static allowance. All growth/check-elimination theorems retain
explicit oracle agreement (discharged for `CryptoOracle.model`). Push-size,
signature-weight, opcode, and unbalanced-conditional failures remain possible.
`maxStackDepth` remains the separate AST-nesting metric and is not presented as
a runtime bound.

The immediate proof work must extend named semantic predicates before extending
`SupportedMiniType`. Unsupported modifier combinations do not reduce to `True`.

## Executable Schnorr Verification

`Bitcoin.Secp256k1` implements field exponentiation, affine point addition and
scalar multiplication, and the even-Y `liftX` used at public-key boundaries.
`Bitcoin.TaggedHash` contains the shared domain-separated SHA256 helper;
Schnorr verification imports it without depending on transaction sighash types.
ECDSA encoding checks reference the shared secp256k1 group order, deriving its
half-order instead of duplicating either numeric constant.
`Bitcoin.Schnorr.verify` implements BIP340's length checks, `r < p`, `s < n`,
challenge tagged hash and `R = sG - eP`, rejecting infinity, odd Y and an X
mismatch. Its message input can have arbitrary length. These operations handle
public verification inputs; there is no signing API or constant-time claim.
Low-level point operations require canonical on-curve points, which `liftX`
and the generator supply in the verifier.

`CryptoOracle.pureLeanSchnorr` combines this verifier with the existing pinned
pure-Lean hashes. Script performs its version/encoding checks and supplies the
64-byte signature body and per-signature 32-byte transaction digest. All 19
official BIP340 vectors are checked offline, including invalid curve keys,
field/order boundaries, infinity/parity failures and messages of length
0, 1, 17, 32 and 100. Additional length guards reject truncated and oversized
keys/signatures. Execution fixtures use all seven Taproot hash types, annex
and CHECKSIGADD signatures made by the pinned BIP340 reference implementation
over independently computed Core digests. Signature, transaction and annex
mutations reject, and empty signatures remain ordinary false results.

Reproduce the two checked-in fixture modules with the pinned public sources:

```sh
python3 scripts/generate_schnorr_fixtures.py --bip340-vectors BIP340_CSV --bip340-reference BIP340_REFERENCE_PY --wallet-vectors WALLET_JSON --core-script CORE_SCRIPT_PY --vectors-output LeanMiniscript/Bitcoin/SchnorrExamples.lean --execution-output LeanMiniscript/Script/SchnorrExecutionExamples.lean
```

The generator first verifies source hashes and every official BIP340 result,
then uses the public test key from vector zero. Lean builds use checked-in
fixtures without downloading or running Python. There is no theorem proving
these curve operations or this verifier correct, nor an unconditional theorem
that `pureLeanSchnorr.RefinesModel`. Existing execution/refinement theorems
retain their explicit agreement premise. The committed execution boundary below
adds control-block validation without claiming curve correctness.

## Taproot Control Blocks And Committed Execution

`parseTaprootControlBlock` enforces the 33 + 32*m byte shape, with m from 0
through 128. It extracts the masked leaf version, output parity, x-only internal
key and bottom-to-top Merkle proof nodes. `verifyTaprootControlBlock` computes
TapLeaf and the lexicographically sorted TapBranch chain, derives TapTweak,
lifts the internal key and computes Q = P + tG. It rejects t ≥ n without
modular reduction, invalid internal keys, infinity, and mismatches in output
X or parity. The standalone checker supports every masked leaf version; it
validates the commitment and does not execute the script. Official-vector
coverage does not establish a general BIP341 or curve-correctness theorem.
Consensus commitment errors map to `TAPROOT_WRONG_CONTROL_SIZE` or
`WITNESS_PROGRAM_MISMATCH`; helper-only tweak/output byte-size errors use
explicit MODEL tags.

`prepareCommittedTapscriptTransaction` separates transaction/witness commitment
checks from Script execution, returning raw `PreparedTapscript` material on
success. This record is not a proof-carrying type: callers can construct it
directly, so the validation guarantee is at the preparation function boundary.
The execution entry always runs preparation first. Its result and error order
are unchanged by this separation.
The preparation function validates transaction-context shape,
requires a selected native OP_1/PUSH32 spent output and an empty scriptSig,
then parses the complete wire-order witness. A trailing annex is removed only
when at least two elements exist and it starts with 0x50. The entry checks
the actual script/control commitment against that spent output before Script
execution and binds the witness's script and annex to per-signature hashing.
The full witness, including control block and annex, supplies the validation
budget. The AST must serialize to the committed witness script bytes.
Key paths and future leaf versions return explicit unsupported-model errors;
they are not classified as Bitcoin consensus-invalid. Commitment validation
precedes that future-version scope check. Setup/commitment errors are separate
from weighted Script results. The full-witness evaluator enforces initial
argument count and size after commitment and leaf-version checks. Final
acceptance is provided by the separate verification entry below. Transaction
consensus validity and the chain provenance of prevouts remain caller
obligations. Older `execTapscript` / `execTapscriptTransaction` APIs
retain their documented unchecked-commitment boundary.

`verifyCommittedTapscriptTransaction` runs preparation, then
`checkTapscriptAcceptance`. The latter enforces the existing Miniscript flag
contract (`minimalIf` and `minimalData` enabled); unsupported settings return
`MODEL_TAPSCRIPT_FLAGS`, a model-scope error rather than a Core consensus error.
Execution errors retain their original tags. Successful execution must leave
exactly one main-stack item (`CLEANSTACK` otherwise, including an empty stack),
then a truthy item (`EVAL_FALSE` otherwise, including negative zero). The final
alt stack is unrestricted. Success returns the remaining validation weight;
`TaprootVerificationError` keeps setup/commitment and Script errors distinct.
These checks follow `ExecuteWitnessScript` in the pinned Core
[`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/9be056a8a72b624dae9623b2f7bded92c2a21c91/src/script/interpreter.cpp#L1689).
This remains acceptance for the modeled subset, not complete consensus
verification: arbitrary raw-script parsing and OP_SUCCESSx are still unmodeled.

`WeightedResult.checkAcceptance_ok_iff` characterizes successful final-stack
checking. `checkTapscriptAcceptance_iff` proves that executable acceptance
exactly reflects `TapscriptAccepts` for any oracle refining the model.
`verifyCommittedTapscriptTransaction_eq_model` preserves that explicit
oracle-agreement boundary through commitment preparation;
`verifyCommittedTapscriptTransaction_iff` connects its success to
`TapscriptAccepts` under an explicit successful preparation premise.
Build-checked boundary regressions cover 1,000/1,001 arguments, 520/521-byte
elements, metadata exclusion, empty/multiple/false/negative-zero results,
noncanonical truthy values, nonempty final alt stacks, and error precedence.
The regenerated committed fixtures additionally test real Schnorr acceptance,
annex acceptance, false and dirty-stack rejection, initial-limit failures and
commitment/future-version precedence. These local regressions do not expand
the BASE-only Core fixture audit's supported set.

`execCommittedTapscriptTransaction_eq_model` proves conditional evaluator
refinement through these deterministic setup/commitment checks, retaining the
explicit `CryptoOracle.RefinesModel` premise. It does not prove cryptographic
correctness or unconditional refinement for the concrete Schnorr verifier.

Offline fixtures match all 12 official BIP341 control blocks, exact leaf hashes
and Merkle roots, including both output parities, proof depths 0/1/2 and a 0xfa
leaf. A reference-generated depth-128 commitment succeeds; depth 129 and
malformed lengths reject. Negative fixtures cover mutated parity, script,
output key, proof nodes and proof order; invalid internal keys; zero, n, n-1,
oversized and malformed tweaks; and infinity. Complete execution fixtures use
a real native P2TR commitment, pinned-Core transaction digests and reference
Schnorr signatures, with and without annex. They check parsing/reconstruction,
remaining weight, actual spent-output binding, Script-byte binding and exact
setup/commitment/crypto error separation.

Reproduce the checked-in fixtures using the same pinned sources documented
above (`BIP340_REFERENCE_PY`, `WALLET_JSON`, `CORE_SCRIPT_PY`):

```sh
python3 scripts/generate_taproot_control_fixtures.py --bip340-reference BIP340_REFERENCE_PY --wallet-vectors WALLET_JSON --core-script CORE_SCRIPT_PY --control-output LeanMiniscript/Bitcoin/TaprootControlBlockExamples.lean --execution-output LeanMiniscript/Extraction/TaprootExamples.lean
```

The generator verifies source SHA256 hashes and independently checks every
official commitment before generating additional cases. Lean builds consume
checked-in fixtures offline. The older Core script-test audit remains a
BASE-only comparison boundary and does not become a full Taproot consensus
differential suite through these additions.
