import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Bridges
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Contracts

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: atomic candidate rows

Generated-contract facts for `0`, `1`, timelocks, keys, and hash locks.
-/

/-! ## Atomic candidate rows -/

/-- The `0` row has only its canonical empty dissatisfaction. -/
theorem generated_zero (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .zero env).SupportsGenerated scriptCtx .zero
      ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
  apply CandidateResult.supports_usable
  exact .b ⟨falseElement, by simpa using zero_execution flags env.txCtx,
    by decide⟩

/-- The `1` row has only its canonical empty satisfaction. -/
theorem generated_one (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGenerated scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
  apply CandidateResult.supports_usable
  exact .b ⟨trueElement, by simpa using one_execution flags env.txCtx,
    by decide⟩

/-- Strong generated contract for `0`. -/
theorem generatedContract_zero (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .zero env).SupportsGeneratedContract scriptCtx .zero
      ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
  apply CandidateResult.supports_usable
  apply GeneratedContract.b
  · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · exact BooleanResultFacts.canonical false _ flags
  · simpa [boolToElement] using zero_execution flags env.txCtx

/-- Strong generated contract for `1`. -/
theorem generatedContract_one (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGeneratedContract scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
  apply CandidateResult.supports_usable
  apply GeneratedContract.b
  · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · exact BooleanResultFacts.canonical true _ flags
  · simpa [boolToElement] using one_execution flags env.txCtx

/-- A well-formed relative timelock has a generated satisfaction exactly when
    the environment transaction satisfies its sequence predicate. -/
theorem generated_older
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.older n) env).SupportsGenerated scriptCtx
      (.older n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.older n, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.older n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    exact .b ⟨scriptNat n, by simpa [scriptNat] using
      (older_execution facts.decoded satisfied), facts.positive⟩
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- A well-formed absolute timelock has the matching generated-execution
    contract under its transaction locktime predicate. -/
theorem generated_after
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.after n) env).SupportsGenerated scriptCtx
      (.after n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.after n, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.after n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    exact .b ⟨scriptNat n, by simpa [scriptNat] using
      (after_execution facts.decoded satisfied), facts.positive⟩
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

private theorem timelockBooleanResultFacts
    {n : Nat} {flags : ScriptFlags} (valid : validTimelockArg n) :
    BooleanResultFacts (scriptNat n) (Int.ofNat n) true
      { z := true } flags := by
  have executionFacts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  rcases valid with ⟨positive, bound⟩
  refine ⟨?_, ?_, executionFacts.positive, ?_, ?_⟩
  · apply decodeScriptNum_scriptNat_of_lt
    simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
      maxArithmeticScriptNatExclusive] using bound
  · simp
    omega
  · simp
  · simp

/-- Strong relative-timelock contract, including the empty-input and exact
    arithmetic result facts needed by later wrappers. -/
theorem generatedContract_older
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.older n) env).SupportsGeneratedContract scriptCtx
      (.older n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.older n, ?_, CandidateResult.supports_impossible _⟩
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.older n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩ <;> simp
    · exact timelockBooleanResultFacts valid
    · have facts := TimelockExecutionFacts.of_validTimelockArg
        (flags := flags) valid
      simpa [scriptNat] using older_execution facts.decoded satisfied
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- Strong absolute-timelock contract. -/
theorem generatedContract_after
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.after n) env).SupportsGeneratedContract scriptCtx
      (.after n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.after n, ?_, CandidateResult.supports_impossible _⟩
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.after n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩ <;> simp
    · exact timelockBooleanResultFacts valid
    · have facts := TimelockExecutionFacts.of_validTimelockArg
        (flags := flags) valid
      simpa [scriptNat] using after_execution facts.decoded satisfied
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

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

/-- Modeled context assumptions discharge the empty-signature encoding
    premise of `generated_pk_k` for a context-valid key. -/
theorem generated_pk_k_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_k key) env).SupportsGenerated scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_pk_k sound encodings
    (checkSigEncodingFor_empty_of_modeled valid version modeled)

/-- Modeled context assumptions likewise discharge the exact empty-signature
    boundary for `pk_h`. -/
theorem generated_pk_h_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_h key) env).SupportsGenerated scriptCtx
      (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_pk_h sound encodings
    (checkSigEncodingFor_empty_of_modeled valid version modeled)

/-- Strong `pk_k` contract at the modeled, context-valid boundary. The added
    assumptions are exactly what supplies witness item bounds; the older weak
    theorem remains available when only execution is needed. -/
theorem generatedContract_pk_k_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_k key) env).SupportsGeneratedContract scriptCtx
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
        apply GeneratedContract.k
          (ownArgs := []) (key := key.bytes) (signature := signature)
        · refine ⟨Witness.ItemsBounded.singleton.mpr
              (selectedSignature_size_le valid version modeled encodings selected),
            ?_, ?_, ?_⟩
          · simp
          · intro _
            exact ⟨signature, rfl⟩
          · intro _ _
            exact ⟨signature, [], rfl,
              selectedSignature_size_ne_zero sound selected⟩
        · rfl
        · exact pk_k_execution key flags env.txCtx
        · exact checkSigWithEncoding_true (encodings key signature selected)
            (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_k key) env).dsat =
      .usable [falseElement] false by rfl]
    apply CandidateResult.supports_usable
    apply GeneratedContract.k
      (ownArgs := []) (key := key.bytes) (signature := falseElement)
    · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
        ?_, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨falseElement, rfl⟩
      · simp
    · rfl
    · exact pk_k_execution key flags env.txCtx
    · exact checkSigWithEncoding_empty
        (checkSigEncodingFor_empty_of_modeled valid version modeled)
        (sound.emptySignatureInvalid key)

/-- Strong modeled `pk_h` contract. The public witness remains wire ordered as
    `[signature, key]`, while the K execution receives `[key]` above the pending
    signature at runtime. -/
theorem generatedContract_pk_h_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_h key) env).SupportsGeneratedContract scriptCtx
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
        apply GeneratedContract.k
          (ownArgs := [key.bytes]) (key := key.bytes) (signature := signature)
        · refine ⟨?_, ?_, ?_, ?_⟩
          · simp [Witness.ItemsBounded, selectedSignature_size_le valid version
              modeled encodings selected, validResolvedPubKey_size_le valid]
          · simp
          · simp
          · intro _ _
            exact ⟨key.bytes, [signature], rfl,
              validResolvedPubKey_size_ne_zero valid⟩
        · rfl
        · exact pk_h_execution key flags env.txCtx
        · exact checkSigWithEncoding_true (encodings key signature selected)
            (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_h key) env).dsat =
      .usable [falseElement, key.bytes] false by rfl]
    apply CandidateResult.supports_usable
    apply GeneratedContract.k
      (ownArgs := [key.bytes]) (key := key.bytes) (signature := falseElement)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le,
          validResolvedPubKey_size_le valid]
      · simp
      · simp
      · simp
    · rfl
    · exact pk_h_execution key flags env.txCtx
    · exact checkSigWithEncoding_empty
        (checkSigEncodingFor_empty_of_modeled valid version modeled)
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
        by decide⟩

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

private theorem generatedContract_hash_sat
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (hashCandidates lock env).sat.Supports fun witness =>
      GeneratedContract lock.fragment witness true flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  cases selected : env.preimageFor lock with
  | none =>
      simpa [hashCandidates, selected] using
        (CandidateResult.supports_impossible (fun witness =>
          GeneratedContract lock.fragment witness true flags env.txCtx
            ⟨.B, { o := true, n := true, d := true, u := true }⟩))
  | some preimage =>
      rw [show (hashCandidates lock env).sat = .usable [preimage] false by
        simp [hashCandidates, selected]]
      apply CandidateResult.supports_usable
      apply GeneratedContract.b
      · refine ⟨Witness.ItemsBounded.singleton.mpr
            (selectedPreimage_size_le sound selected), ?_, ?_, ?_⟩
        · simp
        · intro _
          exact ⟨preimage, rfl⟩
        · intro _ _
          refine ⟨preimage, [], rfl, ?_⟩
          have exactSize := (sound.preimageMatches selected).1
          omega
      · exact BooleanResultFacts.canonical true _ flags
      · simpa [boolToElement, Witness.toInitialStack] using
          hash_satisfaction_execution (sound.preimageMatches selected)

private theorem generatedContract_hash_dsat
    (lock : HashLock) (env : SatEnv) (flags : ScriptFlags) :
    (hashCandidates lock env).dsat.Supports fun witness =>
      GeneratedContract lock.fragment witness false flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  intro witness selected
  simp [hashCandidates, CandidateResult.dontUse,
    CandidateResult.usableWitness?] at selected

/-- Strong generated contract shared by all four hashlock rows. The raw
    canonical dissatisfaction remains DONTUSE and hence has no public usable
    projection. -/
theorem generatedContract_hash
    {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).SupportsGeneratedContract
      scriptCtx lock.fragment
      ⟨.B, { o := true, n := true, d := true, u := true }⟩ flags env.txCtx := by
  cases lock with
  | sha256 hash =>
      exact ⟨.sha256 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.sha256 hash) env flags⟩
  | hash256 hash =>
      exact ⟨.hash256 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.hash256 hash) env flags⟩
  | ripemd160 hash =>
      exact ⟨.ripemd160 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.ripemd160 hash) env flags⟩
  | hash160 hash =>
      exact ⟨.hash160 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.hash160 hash) env flags⟩

end LeanMiniscript.Miniscript
