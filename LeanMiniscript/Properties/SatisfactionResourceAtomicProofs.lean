import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Resource proofs for atomic generated satisfactions

The helpers in this file expose the exact one-instruction resource frames used
by the nonconstant atomic Miniscript fragments.
-/

private theorem hash160Frame (value : StackElement) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_HASH160] [value] [hash160 value] flags ctx
      StackTraceBound.hash 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.op_hash160 value rest [] altStack flags ctx _ Eval.done
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [executedMultiSigKeyCharge]

private theorem sha256Frame (value : StackElement) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_SHA256] [value] [sha256 value] flags ctx
      StackTraceBound.hash 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.op_sha256 value rest [] altStack flags ctx _ Eval.done
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [executedMultiSigKeyCharge]

private theorem hash256Frame (value : StackElement) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_HASH256] [value] [hash256 value] flags ctx
      StackTraceBound.hash 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.op_hash256 value rest [] altStack flags ctx _ Eval.done
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [executedMultiSigKeyCharge]

private theorem ripemd160Frame (value : StackElement) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_RIPEMD160] [value] [ripemd160 value]
      flags ctx StackTraceBound.hash 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.op_ripemd160 value rest [] altStack flags ctx _ Eval.done
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [StackTraceBound.hash]
  · simp [executedMultiSigKeyCharge]

private theorem equalVerifyFrame (first second : StackElement)
    (equal : first = second) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_EQUALVERIFY] [first, second] [] flags ctx
      StackTraceBound.equalVerify 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.equalverify_success first second rest [] altStack flags ctx _
      equal Eval.done
  · simp [StackTraceBound.equalVerify]
  · simp [StackTraceBound.equalVerify]
  · simp [StackTraceBound.equalVerify]
  · simp [executedMultiSigKeyCharge]

private theorem equalTrueFrame (first second : StackElement)
    (equal : first = second) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_EQUAL] [first, second] [trueElement]
      flags ctx StackTraceBound.equal 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.equal_true first second rest [] altStack flags ctx _ equal Eval.done
  · simp [StackTraceBound.equal]
  · simp [StackTraceBound.equal]
  · simp [StackTraceBound.equal]
  · simp [executedMultiSigKeyCharge]

private theorem pkHFrame (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame (compile (.pk_h key)) [key.bytes] [key.bytes]
      flags ctx
      (((StackTraceBound.dup.sequential StackTraceBound.hash).sequential
        StackTraceBound.push).sequential StackTraceBound.equalVerify) 0 := by
  have duplicated := ExecutesResourceFrame.dup key.bytes flags ctx
  have hashed := hash160Frame key.bytes flags ctx
  have pushed := ExecutesResourceFrame.pushData (modelKeyHash key) flags ctx
  have compared := equalVerifyFrame (modelKeyHash key) (hash160 key.bytes)
    (by simp [modelKeyHash, Hash160.ofBytes]) flags ctx
  simpa [compile, compileWithKeyHash] using
    (((duplicated.append (hashed.withSuffix (suffix := [key.bytes]))).append
      (pushed.withSuffix (suffix := [hash160 key.bytes, key.bytes]))).append
      (compared.withSuffix (suffix := [key.bytes])))

/-- Generated `pk_h` candidates carry an exact resource observation for the
    key-hash check while preserving the pending signature. -/
theorem generatedResources_pk_h
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates (.pk_h key) env) scriptCtx (.pk_h key)
      ⟨.K, { n := true, d := true, u := true }⟩ flags env.txCtx := by
  have supported := generatedContract_pk_h_of_modeled valid version modeled
    sound encodings
  refine ⟨supported.typed, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_h key) env).sat =
          .usable [signature, key.bytes] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        apply GeneratedResourceContract.k
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
        · have frame := (pkHFrame key flags env.txCtx).withSuffix
              (suffix := [signature])
          simpa [Witness.toInitialStack] using frame
        · rfl
        · rfl
  · rw [show (satisfactionCandidates (.pk_h key) env).dsat =
      .usable [falseElement, key.bytes] false by rfl]
    apply CandidateResult.supports_usable
    apply GeneratedResourceContract.k
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
    · have frame := (pkHFrame key flags env.txCtx).withSuffix
          (suffix := [falseElement])
      simpa [Witness.toInitialStack] using frame
    · rfl
    · rfl

private theorem checkSequenceFrame {n : Nat} {flags : ScriptFlags}
    {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNat n) flags.minimalData
      maxTimelockScriptNumBytes = .ok (Int.ofNat n))
    (satisfied : sequenceSatisfied n ctx) :
    ExecutesResourceFrame [.op .OP_CHECKSEQUENCEVERIFY] [scriptNat n]
      [scriptNat n] flags ctx StackTraceBound.nop 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.checksequenceverify_success (scriptNat n) n rest [] altStack
      flags ctx _ decoded (by omega) satisfied Eval.done
  · simp [StackTraceBound.nop]
  · simp [StackTraceBound.nop]
  · simp [StackTraceBound.nop]
  · simp [executedMultiSigKeyCharge]

private theorem checkLockTimeFrame {n : Nat} {flags : ScriptFlags}
    {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNat n) flags.minimalData
      maxTimelockScriptNumBytes = .ok (Int.ofNat n))
    (satisfied : locktimeSatisfied n ctx) :
    ExecutesResourceFrame [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNat n]
      [scriptNat n] flags ctx StackTraceBound.nop 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.checklocktimeverify_success (scriptNat n) n rest [] altStack
      flags ctx _ decoded (by omega) satisfied Eval.done
  · simp [StackTraceBound.nop]
  · simp [StackTraceBound.nop]
  · simp [StackTraceBound.nop]
  · simp [executedMultiSigKeyCharge]

private theorem olderFrame {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNat n) flags.minimalData
      maxTimelockScriptNumBytes = .ok (Int.ofNat n))
    (satisfied : sequenceSatisfied n ctx) :
    ExecutesResourceFrame (compile (.older n)) [] [scriptNat n] flags ctx
      (StackTraceBound.push.sequential StackTraceBound.nop) 0 := by
  simpa [compile, compileWithKeyHash] using
    (ExecutesResourceFrame.pushNum n flags ctx).append
      (checkSequenceFrame decoded satisfied)

private theorem afterFrame {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNat n) flags.minimalData
      maxTimelockScriptNumBytes = .ok (Int.ofNat n))
    (satisfied : locktimeSatisfied n ctx) :
    ExecutesResourceFrame (compile (.after n)) [] [scriptNat n] flags ctx
      (StackTraceBound.push.sequential StackTraceBound.nop) 0 := by
  simpa [compile, compileWithKeyHash] using
    (ExecutesResourceFrame.pushNum n flags ctx).append
      (checkLockTimeFrame decoded satisfied)

/-- A selected relative timelock carries the exact push-and-nop resource path. -/
theorem generatedResources_older
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates (.older n) env) scriptCtx (.older n)
      ⟨.B, { z := true }⟩ flags env.txCtx := by
  have supported := generatedContract_older (scriptCtx := scriptCtx)
    (env := env) (flags := flags) valid
  refine ⟨supported.typed, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.older n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    have contract := supported.sat [] (by
      simp [satisfactionCandidates, satisfied])
    cases contract with
    | b input resultFacts executed =>
        rename_i result value
        have explicit := older_execution facts.decoded satisfied
        have sameResult := Eval.result_unique (executed [] [])
          (explicit [] [])
        have resultEq : result = scriptNat n := by
          simpa [scriptNat] using sameResult
        subst result
        apply GeneratedResourceContract.b input resultFacts executed
        · simpa [Witness.toInitialStack] using
            olderFrame facts.decoded satisfied
        · rfl
        · rfl
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- A selected absolute timelock carries the exact push-and-nop resource path. -/
theorem generatedResources_after
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates (.after n) env) scriptCtx (.after n)
      ⟨.B, { z := true }⟩ flags env.txCtx := by
  have supported := generatedContract_after (scriptCtx := scriptCtx)
    (env := env) (flags := flags) valid
  refine ⟨supported.typed, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.after n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    have contract := supported.sat [] (by
      simp [satisfactionCandidates, satisfied])
    cases contract with
    | b input resultFacts executed =>
        rename_i result value
        have explicit := after_execution facts.decoded satisfied
        have sameResult := Eval.result_unique (executed [] [])
          (explicit [] [])
        have resultEq : result = scriptNat n := by
          simpa [scriptNat] using sameResult
        subst result
        apply GeneratedResourceContract.b input resultFacts executed
        · simpa [Witness.toInitialStack] using
            afterFrame facts.decoded satisfied
        · rfl
        · rfl
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

private theorem hashSizePrefixFrame (preimage : StackElement)
    (size : preimage.size = 32) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame
      [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY]
      [preimage] [preimage] flags ctx
      ((StackTraceBound.size.sequential StackTraceBound.push).sequential
        StackTraceBound.equalVerify) 0 := by
  have measured := ExecutesResourceFrame.size preimage flags ctx
  have pushed := (ExecutesResourceFrame.pushNum 32 flags ctx).withSuffix
    (suffix := [scriptNat preimage.size, preimage])
  have equal : scriptNum 32 = scriptNat preimage.size := by
    simp [scriptNat, size]
  have compared := (equalVerifyFrame (scriptNum 32)
    (scriptNat preimage.size) equal flags ctx).withSuffix
      (suffix := [preimage])
  simpa using (measured.append pushed).append compared

private theorem hashLockFrame
    {lock : HashLock} {preimage : StackElement}
    (matching : lock.Matches preimage) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame (compile lock.fragment) [preimage] [trueElement]
      flags ctx
      (((((StackTraceBound.size.sequential StackTraceBound.push).sequential
        StackTraceBound.equalVerify).sequential StackTraceBound.hash).sequential
        StackTraceBound.push).sequential StackTraceBound.equal) 0 := by
  rcases matching with ⟨size, digest⟩
  have prefixFrame := hashSizePrefixFrame preimage size flags ctx
  cases lock with
  | sha256 expected =>
      have hashed := sha256Frame preimage flags ctx
      have pushed := (ExecutesResourceFrame.pushData expected.bytes flags
        ctx).withSuffix
        (suffix := [sha256 preimage])
      have compared := equalTrueFrame expected.bytes (sha256 preimage)
        (by simpa [HashLock.digest, HashLock.expected] using digest.symm) flags ctx
      simpa [HashLock.fragment, compile, compileWithKeyHash] using
        (((prefixFrame.append hashed).append pushed).append compared)
  | hash256 expected =>
      have hashed := hash256Frame preimage flags ctx
      have pushed := (ExecutesResourceFrame.pushData expected.bytes flags
        ctx).withSuffix
        (suffix := [hash256 preimage])
      have compared := equalTrueFrame expected.bytes (hash256 preimage)
        (by simpa [HashLock.digest, HashLock.expected] using digest.symm) flags ctx
      simpa [HashLock.fragment, compile, compileWithKeyHash] using
        (((prefixFrame.append hashed).append pushed).append compared)
  | ripemd160 expected =>
      have hashed := ripemd160Frame preimage flags ctx
      have pushed := (ExecutesResourceFrame.pushData expected.bytes flags
        ctx).withSuffix
        (suffix := [ripemd160 preimage])
      have compared := equalTrueFrame expected.bytes (ripemd160 preimage)
        (by simpa [HashLock.digest, HashLock.expected] using digest.symm) flags ctx
      simpa [HashLock.fragment, compile, compileWithKeyHash] using
        (((prefixFrame.append hashed).append pushed).append compared)
  | hash160 expected =>
      have hashed := hash160Frame preimage flags ctx
      have pushed := (ExecutesResourceFrame.pushData expected.bytes flags
        ctx).withSuffix
        (suffix := [hash160 preimage])
      have compared := equalTrueFrame expected.bytes (hash160 preimage)
        (by simpa [HashLock.digest, HashLock.expected] using digest.symm) flags ctx
      simpa [HashLock.fragment, compile, compileWithKeyHash] using
        (((prefixFrame.append hashed).append pushed).append compared)

private theorem generatedResources_hash_sat
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (hashCandidates lock env).sat.Supports fun witness =>
      GeneratedResourceContract lock.fragment witness true flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  cases selected : env.preimageFor lock with
  | none =>
      simpa [hashCandidates, selected] using
        (CandidateResult.supports_impossible (fun witness =>
          GeneratedResourceContract lock.fragment witness true flags env.txCtx
            ⟨.B, { o := true, n := true, d := true, u := true }⟩))
  | some preimage =>
      rw [show (hashCandidates lock env).sat = .usable [preimage] false by
        simp [hashCandidates, selected]]
      apply CandidateResult.supports_usable
      apply GeneratedResourceContract.b
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
      · simpa [Witness.toInitialStack, boolToElement] using
          hashLockFrame (sound.preimageMatches selected) flags env.txCtx
      · cases lock <;> rfl
      · cases lock <;> rfl

private theorem generatedResources_hash_dsat
    (lock : HashLock) (env : SatEnv) (flags : ScriptFlags) :
    (hashCandidates lock env).dsat.Supports fun witness =>
      GeneratedResourceContract lock.fragment witness false flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  intro witness selected
  simp [hashCandidates, CandidateResult.dontUse,
    CandidateResult.usableWitness?] at selected

/-- All four hash locks share the same size-check, digest, and equality
    resource trace. Their public dissatisfaction candidate remains unusable. -/
theorem generatedResources_hash
    {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates lock.fragment env) scriptCtx lock.fragment
      ⟨.B, { o := true, n := true, d := true, u := true }⟩ flags
      env.txCtx := by
  cases lock with
  | sha256 hash =>
      exact ⟨.sha256 hash, generatedResources_hash_sat sound,
        generatedResources_hash_dsat (.sha256 hash) env flags⟩
  | hash256 hash =>
      exact ⟨.hash256 hash, generatedResources_hash_sat sound,
        generatedResources_hash_dsat (.hash256 hash) env flags⟩
  | ripemd160 hash =>
      exact ⟨.ripemd160 hash, generatedResources_hash_sat sound,
        generatedResources_hash_dsat (.ripemd160 hash) env flags⟩
  | hash160 hash =>
      exact ⟨.hash160 hash, generatedResources_hash_sat sound,
        generatedResources_hash_dsat (.hash160 hash) env flags⟩

end LeanMiniscript.Properties
