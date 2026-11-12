import LeanMiniscript.Extraction.ScriptEquivalence
import LeanMiniscript.Bitcoin.ScriptBytes
import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Miniscript.Validity
import LeanMiniscript.Script.Codec.Serialization

/-!
# Miniscript compilation obligations at Core's VerifyScript

Four properties of a compiled sane Miniscript in each script context, stated
with Core's VerifyScript reference semantics `coreVerifyScript`: a generated
satisfaction passes, a generated dissatisfaction runs to false, a third party
cannot turn a generated satisfaction into another passing witness (BIP 379
non-malleability), and no generated witness fails on a Core resource limit.

Each spends the serialized bytes of `compile` with an empty scriptSig: P2WSH
from the witness-v0 output of the bytes, Tapscript from a version-1 output
that commits to the bytes as a version-0xc0 leaf.

`scripts/miniscript_obligations.lean` counts the obligations without a proof.
-/

namespace LeanMiniscript.Miniscript.CoreFragment

mutual
  /-- Hash locks of a fragment in source order, with repeats. -/
  def hashLocks : CoreFragment → List HashLock
    | .sha256 hash => [.sha256 hash]
    | .hash256 hash => [.hash256 hash]
    | .ripemd160 hash => [.ripemd160 hash]
    | .hash160 hash => [.hash160 hash]
    | .zero | .one | .pk_k _ | .pk_h _ | .older _ | .after _ | .multi _ _ | .multi_a _ _ => []
    | .and_v x y | .and_b x y | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
        hashLocks x ++ hashLocks y
    | .andor x y z => hashLocks x ++ hashLocks y ++ hashLocks z
    | .a x | .s x | .c x | .d x | .v x | .j x | .n x => hashLocks x
    | .thresh _ fragments => hashLocksList fragments

  /-- Hash locks of a list of threshold children. -/
  def hashLocksList : List CoreFragment → List HashLock
    | [] => []
    | fragment :: fragments => hashLocks fragment ++ hashLocksList fragments
end

end LeanMiniscript.Miniscript.CoreFragment

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- `bytes` serialize `compile fragment`, and the model's HASH160 returns 20
bytes, as Bitcoin's does, so each `pk_h` pushes a 20-byte hash. -/
def CompiledScriptBytes (fragment : CoreFragment) (bytes : ByteArray) : Prop :=
  serializeScript (compile fragment) = .ok bytes ∧
    ∀ data, (LeanMiniscript.Script.hash160 data).size = 20

/-- How Core reaches compiled script bytes `bytes` of `context` from
`scriptPubKey` when the witness is the arguments followed by `suffix`.

* P2WSH: `scriptPubKey` is the witness-v0 output of `bytes`
  (`ScriptBytes.p2wsh`), `suffix` is `[bytes]`, and the SHA256 of `bytes` is
  truthy.
* Tapscript: `scriptPubKey` is the version-1 output `0x51 0x20 output`,
  `suffix` is `[bytes, control]`, `control` proves `bytes` as a version-0xc0
  leaf of `output`, and `output` is truthy.

Core requires the truthy program when it runs the scriptPubKey. -/
def CompiledScriptSpend (context : ScriptContext) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) : Prop :=
  match context with
  | .p2wsh =>
      scriptPubKey = ScriptBytes.p2wsh bytes ∧ suffix = [bytes] ∧
        castToBool (LeanHash160.SHA256.hash bytes) = true
  | .tapscript =>
      ∃ output control root,
        scriptPubKey = ⟨#[0x51, 0x20]⟩ ++ output ∧ suffix = [bytes, control] ∧
        verifyTaprootControlBlock output bytes control =
          .ok { leafVersion := 0xc0, leafHash := tapleafHash bytes 0xc0, merkleRoot := root } ∧
        castToBool output = true

/-- The transaction context of the signature and timelock checks of `bytes`
when Core runs them as the witness script of `context`: witness v0 without
Taproot data for P2WSH, and for Tapscript the script path of `bytes` with leaf
version 0xc0, no annex, and no executed OP_CODESEPARATOR. -/
def compiledScriptContext (context : ScriptContext) (ctx : TxContext) (bytes : ByteArray) :
    TxContext :=
  match context with
  | .p2wsh => { ctx with sigVersion := .witnessV0, taproot := none }
  | .tapscript =>
      { ctx with
        sigVersion := .tapscript
        taproot := ctx.taproot.map fun taproot =>
          { taproot with annex := none, spendPath := .scriptPath bytes 0xc0 0xffffffff } }

/-- The run premises for compiled script bytes `bytes` of `context`:

* the Core flags turn on WITNESS, TAPROOT for Tapscript, CHECKLOCKTIMEVERIFY,
  CHECKSEQUENCEVERIFY, and the script flags the model requires of `context`
  (`ModeledContextFlags`);
* the signatures and preimages of `env` are valid (`SatEnv.Sound`) and its
  signatures pass the encoding checks of the flags (`SatEnv.EncodingSound`);
* `env` has the transaction context Core gives `bytes`
  (`compiledScriptContext`);
* the oracle Core uses for `bytes` refines the model's cryptography. -/
def CompiledScriptRun (context : ScriptContext) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (bytes : ByteArray) : Prop :=
  flags.witness = true ∧ (context = .tapscript → flags.taproot = true) ∧
    flags.script.checkLockTimeVerify = true ∧ flags.script.checkSequenceVerify = true ∧
    ModeledContextFlags context flags.script ∧
    env.Sound ∧ env.EncodingSound flags.script ∧
    env.txCtx = compiledScriptContext context ctx bytes ∧
    (oracles (compiledScriptContext context ctx bytes).sigVersion bytes).RefinesModel

/-- What BIP 379 lets a third party put in a witness `other` for `fragment`
after seeing the satisfaction `arguments`, with signatures checked under
`txCtx`:

* no item of `other` is a valid signature for two distinct keys of `fragment`;
* an item of `other` that is a valid signature for a key of `fragment` is an
  item of `arguments`;
* an item of `other` that matches a hash lock of `fragment` is an item of
  `arguments`;
* an item of `other` whose HASH160 is that of a key of `fragment` is that
  key. -/
def ThirdPartyWitness (fragment : CoreFragment) (txCtx : TxContext)
    (arguments other : Witness) : Prop :=
  let valid := fun (item : StackElement) (key : PubKey) =>
    verifySigFor checkSig checkSchnorrSig txCtx item key.bytes = true
  (∀ item ∈ other, ∀ first ∈ fragment.keys, ∀ second ∈ fragment.keys,
      first ≠ second → valid item first → ¬ valid item second) ∧
  (∀ item ∈ other, ∀ key ∈ fragment.keys, valid item key → item ∈ arguments) ∧
  (∀ item ∈ other, ∀ lock ∈ fragment.hashLocks, lock.Matches item → item ∈ arguments) ∧
  (∀ item ∈ other, ∀ key ∈ fragment.keys,
      LeanMiniscript.Script.hash160 item = LeanMiniscript.Script.hash160 key.bytes →
        item = key.bytes)

/-- Core's resource-limit errors: script size, operation count, stack size,
push size, and the Tapscript validation-weight budget. -/
def CoreVerificationError.isResourceLimit : CoreVerificationError → Bool
  | .script .scriptSize | .script .opCount | .script .stackSize | .script .pushSize
  | .script .tapscriptValidationWeight => true
  | _ => false

/-- Satisfaction in `context`: Core's VerifyScript accepts the spend whose
witness is the generated final satisfaction followed by the spend's suffix.

Premises: `sane` is a sane fragment of `context`; `bytes` serialize its
`compile` (`CompiledScriptBytes`); `scriptPubKey` and `suffix` spend `bytes`
with an empty scriptSig (`CompiledScriptSpend`); the run premises hold
(`CompiledScriptRun`); and `satisfyFinal` returns `arguments` for the fragment
and `env`. -/
def CompiledSatisfaction (context : ScriptContext) : Prop :=
  ∀ (sane : SaneFragment context) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : Witness),
    CompiledScriptBytes sane.checked.fragment bytes →
    CompiledScriptSpend context bytes scriptPubKey suffix →
    CompiledScriptRun context env flags ctx oracles bytes →
    satisfyFinal sane.checked.fragment env = some arguments →
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (arguments ++ suffix) = .ok ()

/-- Dissatisfaction in `context`: Core runs the compiled script on the
generated dissatisfaction to one false element, so VerifyScript fails with
EVAL_FALSE.

Premises: those of `CompiledSatisfaction` without the satisfaction; the
fragment has the `d` type property (`ValidDissatisfiableMiniscript`); and
`dissatisfy` returns `arguments` for the fragment and `env`. -/
def CompiledDissatisfaction (context : ScriptContext) : Prop :=
  ∀ (sane : SaneFragment context) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : Witness),
    CompiledScriptBytes sane.checked.fragment bytes →
    CompiledScriptSpend context bytes scriptPubKey suffix →
    CompiledScriptRun context env flags ctx oracles bytes →
    ValidDissatisfiableMiniscript context sane.checked.fragment →
    dissatisfy sane.checked.fragment env = some arguments →
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (arguments ++ suffix) = .error (.script .evalFalse)

/-- Non-malleability in `context` (BIP 379): a witness that a third party
builds after seeing the generated final satisfaction, and that Core's
VerifyScript accepts on the same spend, is that satisfaction.

Premises: those of `CompiledSatisfaction`, with `arguments` the satisfaction;
`other` uses only what `arguments` reveals (`ThirdPartyWitness` under the
transaction context of `env`); and Core's VerifyScript accepts `other`
followed by the spend's suffix. -/
def CompiledNonMalleability (context : ScriptContext) : Prop :=
  ∀ (sane : SaneFragment context) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness),
    CompiledScriptBytes sane.checked.fragment bytes →
    CompiledScriptSpend context bytes scriptPubKey suffix →
    CompiledScriptRun context env flags ctx oracles bytes →
    satisfyFinal sane.checked.fragment env = some arguments →
    ThirdPartyWitness sane.checked.fragment env.txCtx arguments other →
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok () →
    other = arguments

/-- Resource limits in `context`: Core's VerifyScript on a generated
satisfaction or dissatisfaction does not fail with a resource-limit error
(`CoreVerificationError.isResourceLimit`).

Premises: those of `CompiledSatisfaction` without the satisfaction, and
`satisfy` or `dissatisfy` returns `arguments` for the fragment and `env`. -/
def CompiledResourceLimits (context : ScriptContext) : Prop :=
  ∀ (sane : SaneFragment context) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : Witness),
    CompiledScriptBytes sane.checked.fragment bytes →
    CompiledScriptSpend context bytes scriptPubKey suffix →
    CompiledScriptRun context env flags ctx oracles bytes →
    (satisfy sane.checked.fragment env = some arguments ∨
      dissatisfy sane.checked.fragment env = some arguments) →
    ∀ error, coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (arguments ++ suffix) = .error error → error.isResourceLimit = false

/-- P2WSH satisfaction. Premises: those of `CompiledSatisfaction` for P2WSH:
the spend is from the witness-v0 output of the compiled bytes, whose SHA256 is
truthy; the witness is the arguments followed by the bytes; and `env` has the
witness-v0 transaction context. -/
def P2WSHSatisfaction : Prop := CompiledSatisfaction .p2wsh

/-- Tapscript satisfaction. Premises: those of `CompiledSatisfaction` for
Tapscript: the spend is from a truthy version-1 output key that commits to the
compiled bytes as a version-0xc0 leaf; the witness is the arguments followed by
the bytes and the control block; TAPROOT is on; and `env` has the leaf's
script-path transaction context without annex. -/
def TapscriptSatisfaction : Prop := CompiledSatisfaction .tapscript

/-- P2WSH dissatisfaction. Premises: those of `CompiledDissatisfaction` for
P2WSH, with the spend and context of `P2WSHSatisfaction`. -/
def P2WSHDissatisfaction : Prop := CompiledDissatisfaction .p2wsh

/-- Tapscript dissatisfaction. Premises: those of `CompiledDissatisfaction`
for Tapscript, with the spend and context of `TapscriptSatisfaction`. -/
def TapscriptDissatisfaction : Prop := CompiledDissatisfaction .tapscript

/-- P2WSH non-malleability. Premises: those of `CompiledNonMalleability` for
P2WSH, with the spend and context of `P2WSHSatisfaction`. -/
def P2WSHNonMalleability : Prop := CompiledNonMalleability .p2wsh

/-- Tapscript non-malleability. Premises: those of `CompiledNonMalleability`
for Tapscript, with the spend and context of `TapscriptSatisfaction`; the
other witness keeps the same leaf and control block. -/
def TapscriptNonMalleability : Prop := CompiledNonMalleability .tapscript

/-- P2WSH resource limits. Premises: those of `CompiledResourceLimits` for
P2WSH, with the spend and context of `P2WSHSatisfaction`. -/
def P2WSHResourceLimits : Prop := CompiledResourceLimits .p2wsh

/-- Tapscript resource limits. Premises: those of `CompiledResourceLimits` for
Tapscript, with the spend and context of `TapscriptSatisfaction`. -/
def TapscriptResourceLimits : Prop := CompiledResourceLimits .tapscript

end LeanMiniscript.Extraction
