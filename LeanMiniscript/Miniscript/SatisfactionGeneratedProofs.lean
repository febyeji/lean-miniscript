import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Typed execution of generated witnesses

This module connects candidate provenance to the arbitrary-stack execution
frames in `SatisfactionProofs`. The proof-only carrier keeps the fragment's
typing derivation together with the exact execution contract selected by its
base type. In particular, a K execution separates the K fragment's own
arguments from the pending signature consumed by wrapper `c`.

The first layer covers `0`, `1`, both key leaves, all four hash leaves, and the
`c` lift. Timelocks still need a generic ScriptNum round-trip theorem derived
from their `WellFormed` bound. The other wrappers need inductively maintained
input-shape or numeric-result invariants, so they remain outside this layer.
-/

/-- Exact execution contract selected by the fragment's base type. K
    fragments retain the pending signature below their own runtime arguments;
    this is the precise frame consumed by a following `OP_CHECKSIG`. -/
inductive GeneratedExecution (fragment : CoreFragment) (witness : Witness)
    (expected : Bool) (flags : ScriptFlags) (txCtx : TxContext) :
    BaseType → Prop where
  | b (executed : BExecutionOutcome fragment witness.toInitialStack expected
      flags txCtx) : GeneratedExecution fragment witness expected flags txCtx .B
  | v (expectedTrue : expected = true)
      (executed : VExecution fragment witness.toInitialStack flags txCtx) :
      GeneratedExecution fragment witness expected flags txCtx .V
  | k (ownArgs : Stack) (key signature : StackElement)
      (stackShape : witness.toInitialStack = ownArgs ++ [signature])
      (executed : KExecution fragment ownArgs key flags txCtx)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
        signature key = .ok expected) :
      GeneratedExecution fragment witness expected flags txCtx .K
  | w (order : WStackOrder)
      (executed : WExecutionOutcome fragment witness.toInitialStack expected
        order flags txCtx) :
      GeneratedExecution fragment witness expected flags txCtx .W

/-- A candidate pair carries one global typing derivation plus an execution
    invariant for every projected satisfaction and dissatisfaction. Keeping
    typing outside the projections also covers pairs with impossible sides. -/
structure CandidatePair.SupportsGenerated (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports fun witness =>
    GeneratedExecution fragment witness true flags txCtx ty.base
  dsat : pair.dsat.Supports fun witness =>
    GeneratedExecution fragment witness false flags txCtx ty.base

namespace CandidatePair.SupportsGenerated

/-- Project the satisfaction execution contract through the public
    `satisfy` API. -/
theorem satisfyExecution
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : (satisfactionCandidates fragment env).SupportsGenerated
      scriptCtx fragment ty flags env.txCtx)
    (generated : satisfy fragment env = some witness) :
    GeneratedExecution fragment witness true flags env.txCtx ty.base :=
  supported.sat witness generated

/-- Project the dissatisfaction execution contract through the public
    `dissatisfy` API. -/
theorem dissatisfyExecution
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : (satisfactionCandidates fragment env).SupportsGenerated
      scriptCtx fragment ty flags env.txCtx)
    (generated : dissatisfy fragment env = some witness) :
    GeneratedExecution fragment witness false flags env.txCtx ty.base :=
  supported.dsat witness generated

end CandidatePair.SupportsGenerated

/-! ## Atomic candidate rows -/

/-- The `0` row has only its canonical empty dissatisfaction. -/
theorem generated_zero (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .zero env).SupportsGenerated scriptCtx .zero
      ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
  apply CandidateResult.supports_usable
  exact .b ⟨falseElement, by simpa using zero_execution flags env.txCtx,
    by native_decide⟩

/-- The `1` row has only its canonical empty satisfaction. -/
theorem generated_one (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGenerated scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
  apply CandidateResult.supports_usable
  exact .b ⟨trueElement, by simpa using one_execution flags env.txCtx,
    by native_decide⟩

/-- Generated `pk_k` candidates carry the pending signature below the empty K
    argument frame, including the canonical empty dissatisfaction. -/
theorem generated_pk_k
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (emptyEncoding : checkSigEncodingFor flags env.txCtx.sigVersion
      falseElement key.bytes = .ok ()) :
    (satisfactionCandidates (.pk_k key) env).SupportsGenerated scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_k key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_k key) env).sat =
          .usable [signature] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        refine .k [] key.bytes signature rfl
          (pk_k_execution key flags env.txCtx) ?_
        exact checkSigWithEncoding_true (encodings key signature selected)
          (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_k key) env).dsat =
      .usable [falseElement] false by rfl]
    apply CandidateResult.supports_usable
    refine .k [] key.bytes falseElement rfl
      (pk_k_execution key flags env.txCtx) ?_
    exact checkSigWithEncoding_empty
      emptyEncoding
      (sound.emptySignatureInvalid key)

/-- Generated `pk_h` candidates reveal the key in the K argument frame and
    keep the signature below it. -/
theorem generated_pk_h
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (emptyEncoding : checkSigEncodingFor flags env.txCtx.sigVersion
      falseElement key.bytes = .ok ()) :
    (satisfactionCandidates (.pk_h key) env).SupportsGenerated scriptCtx
      (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_h key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_h key) env).sat =
          .usable [signature, key.bytes] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        refine .k [key.bytes] key.bytes signature rfl
          (pk_h_execution key flags env.txCtx) ?_
        exact checkSigWithEncoding_true (encodings key signature selected)
          (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_h key) env).dsat =
      .usable [falseElement, key.bytes] false by rfl]
    apply CandidateResult.supports_usable
    refine .k [key.bytes] key.bytes falseElement rfl
      (pk_h_execution key flags env.txCtx) ?_
    exact checkSigWithEncoding_empty
      emptyEncoding
      (sound.emptySignatureInvalid key)

private theorem generated_hash_sat
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (hashCandidates lock env).sat.Supports fun witness =>
      GeneratedExecution lock.fragment witness true flags env.txCtx .B := by
  cases selected : env.preimageFor lock with
  | none =>
      simpa [hashCandidates, selected] using
        (CandidateResult.supports_impossible (fun witness =>
          GeneratedExecution lock.fragment witness true flags env.txCtx .B))
  | some preimage =>
      rw [show (hashCandidates lock env).sat = .usable [preimage] false by
        simp [hashCandidates, selected]]
      apply CandidateResult.supports_usable
      exact .b ⟨trueElement,
        hash_satisfaction_execution (sound.preimageMatches selected),
        by native_decide⟩

private theorem generated_hash_dsat
    (lock : HashLock) (env : SatEnv) (flags : ScriptFlags) :
    (hashCandidates lock env).dsat.Supports fun witness =>
      GeneratedExecution lock.fragment witness false flags env.txCtx .B := by
  intro witness selected
  simp [hashCandidates, CandidateResult.dontUse,
    CandidateResult.usableWitness?] at selected

/-- All four hashlock rows share the same typed generated-execution proof.
    Their canonical dissatisfaction is DONTUSE, so its public support claim is
    vacuous; `hash_dsat_candidate_execution` retains its raw semantic proof. -/
theorem generated_hash
    {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).SupportsGenerated scriptCtx
      lock.fragment ⟨.B, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  cases lock with
  | sha256 hash =>
      exact ⟨.sha256 hash, generated_hash_sat sound,
        generated_hash_dsat (.sha256 hash) env flags⟩
  | hash256 hash =>
      exact ⟨.hash256 hash, generated_hash_sat sound,
        generated_hash_dsat (.hash256 hash) env flags⟩
  | ripemd160 hash =>
      exact ⟨.ripemd160 hash, generated_hash_sat sound,
        generated_hash_dsat (.ripemd160 hash) env flags⟩
  | hash160 hash =>
      exact ⟨.hash160 hash, generated_hash_sat sound,
        generated_hash_dsat (.hash160 hash) env flags⟩

/-! ## K-to-B wrapper lift -/

namespace CandidatePair.SupportsGenerated

/-- Wrapper `c` consumes the checked pending signature carried by a generated
    K execution. The candidate pair itself is unchanged by `c`, so metadata
    and selection provenance remain exact. -/
theorem c
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGenerated scriptCtx fragment ⟨.K, mods⟩
      flags txCtx) :
    pair.SupportsGenerated scriptCtx (.c fragment)
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx := by
  refine ⟨.c_wrap supported.typed, ?_, ?_⟩
  · intro witness selected
    cases supported.sat witness selected with
    | k ownArgs key signature stackShape keyExec checked =>
        apply GeneratedExecution.b
        refine ⟨boolToElement true, ?_, castToBool_boolToElement true⟩
        simpa [stackShape] using keyExec.c checked
  · intro witness selected
    cases supported.dsat witness selected with
    | k ownArgs key signature stackShape keyExec checked =>
        apply GeneratedExecution.b
        refine ⟨boolToElement false, ?_, castToBool_boolToElement false⟩
        simpa [stackShape] using keyExec.c checked

end CandidatePair.SupportsGenerated

end LeanMiniscript.Miniscript
