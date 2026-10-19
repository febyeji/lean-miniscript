import LeanMiniscript.Miniscript.SatisfactionProofs.Execution

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Primitive execution contracts -/

/-- `1` needs no arguments and leaves the canonical true element. -/
theorem one_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .one [] trueElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_one] using
    (Eval.pushNum 1 [] rest altStack flags ctx
      (.success (trueElement :: rest) altStack)
      (Eval.done (stack := trueElement :: rest) (altStack := altStack)))

/-- `0` needs no arguments and leaves the canonical false element. -/
theorem zero_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .zero [] falseElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_zero] using
    (Eval.pushNum 0 [] rest altStack flags ctx
      (.success (falseElement :: rest) altStack)
      (Eval.done (stack := falseElement :: rest) (altStack := altStack)))

/-- `pk_k` needs no arguments of its own and leaves its exact public key. -/
theorem pk_k_execution (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    KExecution (.pk_k key) [] key.bytes flags ctx := by
  intro rest altStack
  simpa [KExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushDataNext (data := key.bytes)
      (Eval.done (stack := key.bytes :: rest) (altStack := altStack)))

/-- `pk_h` consumes the revealed key, verifies its model HASH160, and leaves
    that same key for a following signature check. -/
theorem pk_h_execution (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    KExecution (.pk_h key) [key.bytes] key.bytes flags ctx := by
  intro rest altStack
  simp only [compile, compileWithKeyHash, modelKeyHash, Hash160.ofBytes]
  apply Eval.dup
  apply Eval.op_hash160
  apply Eval.pushDataNext
  apply Eval.equalverify_success
  · rfl
  · exact Eval.done

/-- A matching 32-byte preimage executes its hashlock to the canonical true
    element while preserving arbitrary surrounding stacks. -/
theorem hash_satisfaction_execution
    {lock : HashLock} {preimage : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (matching : lock.Matches preimage) :
    BExecution lock.fragment [preimage] trueElement flags ctx := by
  rcases matching with ⟨size, digest⟩
  cases lock with
  | sha256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_sha256
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | hash256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash256
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | ripemd160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_ripemd160
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done
  | hash160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash160
      apply Eval.pushDataNext
      apply Eval.equal_true
      · exact digest.symm
      · exact Eval.done

/-- A mismatching 32-byte value executes its hashlock to the canonical false
    element; an arbitrary-length mismatch would instead abort at `EQUALVERIFY`. -/
theorem hash_dissatisfaction_execution
    {lock : HashLock} {nonPreimage : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (mismatches : lock.Mismatches nonPreimage) :
    BExecution lock.fragment [nonPreimage] falseElement flags ctx := by
  rcases mismatches with ⟨size, digest⟩
  cases lock with
  | sha256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_sha256
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | hash256 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash256
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | ripemd160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_ripemd160
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done
  | hash160 expected =>
      intro rest altStack
      simp only [HashLock.fragment, compile, compileWithKeyHash]
      apply Eval.size
      apply Eval.pushNum
      apply Eval.equalverify_success
      · simp [scriptNat, size]
      apply Eval.op_hash160
      apply Eval.pushDataNext
      apply Eval.equal_false
      · exact Ne.symm digest
      · exact Eval.done

/-- A satisfied relative timelock preserves arbitrary surrounding stacks and
    leaves its compiler-produced numeric operand. -/
theorem older_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : sequenceSatisfied n ctx) :
    BExecution (.older n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKSEQUENCEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checksequenceverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- A satisfied absolute timelock has the corresponding arbitrary-stack
    execution contract. -/
theorem after_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : locktimeSatisfied n ctx) :
    BExecution (.after n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKLOCKTIMEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checklocktimeverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- The basic fragment cases whose witness algorithms need no numeric
    well-formedness premise. Timelocks have separate theorems below because
    their compiled Script-number must also satisfy the five-byte limit. -/
inductive BasicSatisfactionFragment : CoreFragment → Prop where
  | one : BasicSatisfactionFragment .one
  | cPkK (key : PubKey) : BasicSatisfactionFragment (.c (.pk_k key))
  | cPkH (key : PubKey) : BasicSatisfactionFragment (.c (.pk_h key))
  | sha256 (hash : Hash256) : BasicSatisfactionFragment (.sha256 hash)
  | hash256 (hash : Hash256) : BasicSatisfactionFragment (.hash256 hash)
  | ripemd160 (hash : Hash160) : BasicSatisfactionFragment (.ripemd160 hash)
  | hash160 (hash : Hash160) : BasicSatisfactionFragment (.hash160 hash)

/-- A witness returned for a supported basic fragment has a satisfying
    arbitrary-stack B execution. Cryptographic and byte-encoding assumptions
    are kept at this execution boundary rather than baked into the frame API. -/
theorem satisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (generated : satisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack true flags env.txCtx := by
  cases supported with
  | one =>
      simp [satisfy] at generated
      subst witness
      exact ⟨trueElement, by simpa using one_execution flags env.txCtx,
        by decide⟩
  | cPkK key =>
      cases signatureFor : env.signatureFor key with
      | none => simp [satisfy, keyCandidates, signatureFor] at generated
      | some signature =>
          simp [satisfy, keyCandidates, signatureFor] at generated
          subst witness
          have verified := sound.signatureValid signatureFor
          have checked := checkSigWithEncoding_true
            (encodings key signature signatureFor) verified
          refine ⟨trueElement, ?_, by decide⟩
          change BExecution (.c (.pk_k key)) [signature]
            trueElement flags env.txCtx
          simpa [boolToElement] using
            (KExecution.c (pk_k_execution key flags env.txCtx) checked)
  | cPkH key =>
      cases signatureFor : env.signatureFor key with
      | none => simp [satisfy, keyCandidates, signatureFor] at generated
      | some signature =>
          simp [satisfy, keyCandidates, signatureFor] at generated
          subst witness
          have verified := sound.signatureValid signatureFor
          have checked := checkSigWithEncoding_true
            (encodings key signature signatureFor) verified
          refine ⟨trueElement, ?_, by decide⟩
          change BExecution (.c (.pk_h key)) [key.bytes, signature]
            trueElement flags env.txCtx
          simpa [boolToElement] using
            (KExecution.c (pk_h_execution key flags env.txCtx) checked)
  | sha256 hash =>
      cases preimageFor : env.preimageFor (.sha256 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by decide⟩
  | hash256 hash =>
      cases preimageFor : env.preimageFor (.hash256 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by decide⟩
  | ripemd160 hash =>
      cases preimageFor : env.preimageFor (.ripemd160 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by decide⟩
  | hash160 hash =>
      cases preimageFor : env.preimageFor (.hash160 hash) with
      | none => simp [satisfy, hashCandidates, preimageFor] at generated
      | some preimage =>
          simp [satisfy, hashCandidates, preimageFor] at generated
          subst witness
          exact ⟨trueElement,
            hash_satisfaction_execution (sound.preimageMatches preimageFor),
            by decide⟩

/-- Every witness returned for a supported basic fragment is accepted by its
    compiled script under the environment transaction and modeled flags,
    provided the supplied material also passes the selected encoding checks. -/
theorem satisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfy m env = some witness) :
    Accepts ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_basic_execution supported sound encodings generated).cleanStackResult⟩

/-- The witness returned for a satisfied relative timelock has the reusable B
    execution contract before final clean-stack acceptance is imposed. -/
theorem satisfy_older_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    BExecutionOutcome (.older n) witness.toInitialStack true flags env.txCtx := by
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · simp [satisfy, satisfied] at generated
    subst witness
    exact ⟨scriptNum n, by simpa using older_execution decoded satisfied, positive⟩
  · simp [satisfy, satisfied] at generated

/-- A returned `older` witness is accepted whenever its compiler-produced
    numeric operand is valid and truthy. `WellFormed` supplies these numeric
    premises when this lemma is lifted into the general correctness theorem. -/
theorem satisfy_older_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    Accepts ctx (compile (.older n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_older_execution decoded positive generated).cleanStackResult⟩

/-- The witness returned for a satisfied absolute timelock likewise executes
    over arbitrary surrounding stacks. -/
theorem satisfy_after_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    BExecutionOutcome (.after n) witness.toInitialStack true flags env.txCtx := by
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · simp [satisfy, satisfied] at generated
    subst witness
    exact ⟨scriptNum n, by simpa using after_execution decoded satisfied, positive⟩
  · simp [satisfy, satisfied] at generated

/-- Absolute timelocks use the same transaction predicate and numeric boundary
    as relational Script execution. -/
theorem satisfy_after_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    Accepts ctx (compile (.after n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_after_execution decoded positive generated).cleanStackResult⟩

/-- The raw hash dissatisfaction is a canonical DONTUSE candidate, but its
    retained witness still has an exact false execution contract. -/
theorem hash_dsat_candidate_execution
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).dsat =
        .dontUse [env.nonPreimageFor lock] false .canonical ∧
      BExecution lock.fragment [env.nonPreimageFor lock] falseElement
        flags env.txCtx := by
  constructor
  · cases lock <;> rfl
  · exact hash_dissatisfaction_execution
      (sound.nonPreimageMismatches lock)

/-- A returned basic dissatisfaction has a false B execution over every
    surrounding main and alternate stack. -/
theorem dissatisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨
      (∃ key, m = .c (.pk_k key)) ∨
      (∃ key, m = .c (.pk_h key)))
    (sound : env.Sound)
    (keys : ∀ key,
      (m = .c (.pk_k key) ∨ m = .c (.pk_h key)) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (generated : dissatisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack false flags env.txCtx := by
  rcases supported with rfl | ⟨key, rfl⟩ | ⟨key, rfl⟩
  · simp [dissatisfy] at generated
    subst witness
    exact ⟨falseElement, by simpa using zero_execution flags env.txCtx,
      by decide⟩
  · simp [dissatisfy, keyCandidates] at generated
    subst witness
    have rejected := sound.emptySignatureInvalid key
    have checked := checkSigWithEncoding_empty (keys key (Or.inl rfl)) rejected
    refine ⟨falseElement, ?_, by decide⟩
    change BExecution (.c (.pk_k key)) [falseElement] falseElement flags env.txCtx
    simpa [boolToElement] using
      (KExecution.c (pk_k_execution key flags env.txCtx) checked)
  · simp [dissatisfy, keyCandidates] at generated
    subst witness
    have rejected := sound.emptySignatureInvalid key
    have checked := checkSigWithEncoding_empty (keys key (Or.inr rfl)) rejected
    refine ⟨falseElement, ?_, by decide⟩
    change BExecution (.c (.pk_h key)) [key.bytes, falseElement]
      falseElement flags env.txCtx
    simpa [boolToElement] using
      (KExecution.c (pk_h_execution key flags env.txCtx) checked)

/-- Every witness returned for a supported basic dissatisfiable fragment
    executes successfully to a clean false result when the fragment's key
    passes the public-key encoding check, even with an empty signature. -/
theorem dissatisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨
      (∃ key, m = .c (.pk_k key)) ∨
      (∃ key, m = .c (.pk_h key)))
    (sound : env.Sound)
    (keys : ∀ key,
      (m = .c (.pk_k key) ∨ m = .c (.pk_h key)) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : dissatisfy m env = some witness) :
    Dissatisfies ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (dissatisfy_basic_execution supported sound keys generated).cleanStackResult⟩

end LeanMiniscript.Miniscript
