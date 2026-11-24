import LeanMiniscript.Extraction.MiniscriptCompilationProofs

/-!
# P2WSH accepted-run inversion and single-key witness uniqueness

For sane `c:pk_k(key)` fragments, an accepted third-party witness equals the
generated satisfaction under the existing `P2WSHNonMalleability` premises.
Core's VerifyScript acceptance reduces to a successful witness-v0 typed
runtime; inversion of `<key> OP_CHECKSIG` recovers the single verified item,
and `ThirdPartyWitness` identifies it with the generated signature.

`p2wshAccepted_runtime` and `p2wshAccepted_eval` expose the common accepted-run
boundary for any sane P2WSH fragment. `p2wshAccepted_c_pk_h` uses that boundary
to recover the two witness positions of `c:pk_h(key)`, the committed HASH160
equality, and the successful encoded signature check. The companion module
`P2WSHNonMalleabilityInversion` proves equality with the generated satisfaction
using the existing third-party and STRICTENC premises.

The unrestricted `P2WSHNonMalleability` obligation remains unproved.
Extending these results requires recovering material positions for the other
constructors and establishing their equality with the generated witness under
the existing third-party contract.
-/

-- TODO(p2wsh-non-malleability): establish positional witness uniqueness for
-- the remaining constructors, including witnesses with mixed material roles.

namespace LeanMiniscript.Extraction.P2WSHNonMalleabilitySubcase

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open LeanMiniscript.Properties CoreScriptExecution

/-- The compiled script of the subcase shape. -/
theorem compile_c_pk_k (key : PubKey) :
    compile (.c (.pk_k key)) = [.pushData key.bytes, .op .OP_CHECKSIG] := rfl

/-- Truthiness of a Boolean result pushed by the evaluator. -/
theorem castToBool_boolToElement (b : Bool) : castToBool (boolToElement b) = b := by
  cases b <;> rfl

/-- At witness v0 the checked signature boundary is the ECDSA callback at the
    context's supplied hash. -/
theorem verifySigFor_witnessV0
    (ecdsa schnorr : StackElement → StackElement → ByteArray → Bool)
    {ctx : TxContext} (version : ctx.sigVersion = .witnessV0)
    (sig pubkey : StackElement) :
    verifySigFor ecdsa schnorr ctx sig pubkey = ecdsa sig pubkey ctx.sigHash := by
  simp [verifySigFor, checkedVerifySigFor, version]

/-- A CHECKSIG step that returns true verified the signature. -/
theorem verifySigFor_of_checkSigWithEncoding_true
    {ecdsa schnorr : StackElement → StackElement → ByteArray → Bool}
    {flags : ScriptFlags} {ctx : TxContext} {sig pubkey : StackElement}
    (checked : checkSigWithEncoding ecdsa schnorr flags ctx sig pubkey = .ok true) :
    verifySigFor ecdsa schnorr ctx sig pubkey = true := by
  unfold checkSigWithEncoding at checked
  cases encoding : checkSigEncodingFor flags ctx.sigVersion sig pubkey with
  | error error => rw [encoding] at checked; contradiction
  | ok _ =>
      rw [encoding] at checked
      cases verified : checkedVerifySigFor ecdsa schnorr ctx sig pubkey with
      | error error => rw [verified] at checked; contradiction
      | ok result =>
          rw [verified] at checked
          have resultTrue : result = true := by
            cases result with
            | true => rfl
            | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at checked
                split at checked <;> split at checked <;> contradiction
          simp [verifySigFor, verified, resultTrue]

/-- The push step of the subcase script: size checks, then the push. -/
private theorem pushStep (oracle : CryptoOracle) (flags : ScriptFlags) (ctx : TxContext)
    (version : ctx.sigVersion = .witnessV0)
    (key : StackElement) (stack : Stack) :
    runtimeStep oracle (.pushData key)
      { stack := stack, altStack := [], conditions := [], weight := 0,
          operationCount := 0 } flags ctx =
      (if key.size > maxScriptElementSize then .error .pushSize
      else if stack.length + 1 > maxStackSize then .error .stackSize
      else .ok { stack := key :: stack, altStack := [], conditions := [], weight := 0, operationCount := 0 }) := by
  by_cases fits : key.size > maxScriptElementSize <;>
    by_cases room : stack.length + 1 > maxStackSize <;>
    simp [runtimeStep_pushData, runtimeInstruction, executeRuntimeElement,
      ScriptElement.pushSize, prepareValidationWeight, version, evaluate,
      checkRuntimeStack, fits, room,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The CHECKSIG step of the subcase script on a two-item stack. -/
private theorem sigStep (oracle : CryptoOracle) (flags : ScriptFlags) (ctx : TxContext)
    (version : ctx.sigVersion = .witnessV0)
    (key sig : StackElement) (rest : Stack) :
    runtimeStep oracle (.op .OP_CHECKSIG)
      { stack := key :: sig :: rest, altStack := [], conditions := [], weight := 0,
          operationCount := 0 } flags ctx =
      (match checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig key with
      | .error error => .error error
      | .ok checked =>
          if rest.length + 1 > maxStackSize then .error .stackSize
          else .ok { stack := boolToElement checked :: rest, altStack := [], conditions := [], weight := 0, operationCount := 1 }) := by
  have notOversize : ¬ (0 : Nat) > maxScriptElementSize := by decide
  cases checked : checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx
      sig key <;>
    simp [runtimeStep_withoutScriptCode, chargeOperations, version, chargedOperationCount,
      opcodeKeyCount, maxOpsPerScript, runtimeInstruction, executeRuntimeElement,
      ScriptElement.pushSize, prepareValidationWeight, evaluate, checkRuntimeStack,
      notOversize, checked,
      bind, Except.bind, pure, Except.pure, Except.map, throw, throwThe, MonadExceptOf.throw]

/-- The CHECKSIG step of the subcase script on a one-item stack underflows. -/
private theorem sigStepUnderflow (oracle : CryptoOracle) (flags : ScriptFlags)
    (ctx : TxContext) (version : ctx.sigVersion = .witnessV0) (key : StackElement) :
    runtimeStep oracle (.op .OP_CHECKSIG)
      { stack := [key], altStack := [], conditions := [], weight := 0,
          operationCount := 0 } flags ctx = .error .stackUnderflow := by
  simp [runtimeStep_withoutScriptCode, chargeOperations, version, chargedOperationCount,
    opcodeKeyCount, maxOpsPerScript, runtimeInstruction, executeRuntimeElement,
    ScriptElement.pushSize, prepareValidationWeight, evaluate,
    maxScriptElementSize,
    bind, Except.bind, pure, Except.pure, Except.map, throw, throwThe, MonadExceptOf.throw]

/-- Inversion of the typed witness-v0 runtime for the subcase script
`<key> OP_CHECKSIG`: a successful run ending in one item started from a
one-item stack whose item passed CHECKSIG under `key`. -/
theorem checkSigTail_inversion
    (oracle : CryptoOracle) (flags : ScriptFlags) (ctx : TxContext)
    (version : ctx.sigVersion = .witnessV0)
    (key : StackElement) (stack : Stack) {top : StackElement} {alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits oracle [.pushData key, .op .OP_CHECKSIG]
      stack [] flags ctx 0 = .success [top] alt weight) :
    ∃ sig checked, stack = [sig] ∧ alt = [] ∧
      checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig key =
        .ok checked ∧
      top = boolToElement checked := by
  unfold evaluateWithRuntimeLimits at executed
  by_cases fits : key.size > maxScriptElementSize
  · simp [evaluateRuntime, pushStep oracle flags ctx version key stack, fits] at executed
  · by_cases room : stack.length + 1 > maxStackSize
    · simp [evaluateRuntime, pushStep oracle flags ctx version key stack, fits, room]
        at executed
    · simp only [evaluateRuntime, pushStep oracle flags ctx version key stack] at executed
      rw [if_neg fits, if_neg room] at executed
      change evaluateRuntime oracle [.op .OP_CHECKSIG]
        { stack := key :: stack, altStack := [], conditions := [], weight := 0,
          operationCount := 0 } flags ctx = .success [top] alt weight at executed
      simp only [evaluateRuntime] at executed
      cases stack with
      | nil =>
          rw [sigStepUnderflow oracle flags ctx version key] at executed
          simp at executed
      | cons sig rest =>
          rw [sigStep oracle flags ctx version key sig rest] at executed
          cases hchecked : checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig
              flags ctx sig key with
          | error error => simp [hchecked] at executed
          | ok checked =>
              simp only [hchecked] at executed
              by_cases overflow : rest.length + 1 > maxStackSize
              · simp [overflow] at executed
              · rw [if_neg overflow] at executed
                simp only [finishRuntime, List.isEmpty, ↓reduceIte,
                  WeightedResult.success.injEq] at executed
                obtain ⟨stackResult, altEq, _⟩ := executed
                obtain ⟨topEq, restEq⟩ := List.cons.inj stackResult
                subst restEq
                exact ⟨sig, checked, rfl, altEq.symm, hchecked, topEq.symm⟩

/-- The witness-program check of a P2WSH spend is its witness-script check. -/
theorem verifyCoreWitnessProgram_p2wsh_eq
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (other : Witness) (bytes : ByteArray) (keyPath : CoreKeyPathChecker) :
    verifyCoreWitnessProgram execute flags (other ++ [bytes]) 0
      (LeanHash160.SHA256.hash bytes) false keyPath =
    executeCoreWitnessScript execute flags
      { scriptBytes := bytes, stack := other.reverse, sigVersion := .witnessV0 } := by
  simp [verifyCoreWitnessProgram, sha256_size, List.reverse_append]

/-- An accepted witness-v0 script execution ran to a single truthy item. -/
theorem executeCoreWitnessScript_ok_of_witnessV0
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (request : CoreScriptExecutionRequest)
    (version : request.sigVersion = .witnessV0)
    (accepted : executeCoreWitnessScript execute flags request = .ok ()) :
    (request.stack.any fun item => item.size > maxScriptElementSize) = false ∧
    ∃ top, execute request = .ok [top] ∧ castToBool top = true := by
  unfold executeCoreWitnessScript at accepted
  rw [if_neg (by simp [version])] at accepted
  cases oversize : request.stack.any (fun item => item.size > maxScriptElementSize) with
  | true =>
      simp [oversize, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | false =>
      rw [if_neg (by simp [oversize])] at accepted
      refine ⟨rfl, ?_⟩
      cases executed : execute request with
      | error error => simp [executed, bind, Except.bind] at accepted
      | ok stack =>
          simp only [executed, bind, Except.bind] at accepted
          cases stack with
          | nil =>
              change (Except.error (CoreVerificationError.script .cleanStack) :
                Except CoreVerificationError Unit) = .ok () at accepted
              simp at accepted
          | cons top rest =>
              cases rest with
              | nil =>
                  refine ⟨top, rfl, ?_⟩
                  change (if castToBool top then Except.ok ()
                      else .error (CoreVerificationError.script .evalFalse)) = .ok ()
                    at accepted
                  cases truth : castToBool top with
                  | false =>
                      rw [if_neg (by simp [truth])] at accepted
                      simp at accepted
                  | true => rfl
              | cons extra rest =>
                  change (Except.error (CoreVerificationError.script .cleanStack) :
                    Except CoreVerificationError Unit) = .ok () at accepted
                  simp at accepted

/-- Acceptance of a native P2WSH spend with an empty scriptSig reduces to the
    witness-script check, for a truthy program and WITNESS on. -/
theorem coreVerifyScript_p2wsh_eq_witnessScript
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (other : Witness) (bytes : ByteArray)
    (truth : castToBool (LeanHash160.SHA256.hash bytes) = true)
    (enabled : flags.witness = true) :
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty (ScriptBytes.p2wsh bytes)
      (other ++ [bytes]) =
    executeCoreWitnessScript (executeCoreScript flags ctx oracles) flags
      { scriptBytes := bytes, stack := other.reverse, sigVersion := .witnessV0 } := by
  have empty : executeCoreScript flags ctx oracles { scriptBytes := ByteArray.empty } =
      .ok [] := by
    simp [executeCoreScript, executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have size34 : (ScriptBytes.p2wsh bytes).size = 34 := by
    simp [ScriptBytes.p2wsh, sha256_size]
    rfl
  have noP2SH : coreScriptIsP2SH (ScriptBytes.p2wsh bytes) = false := by
    simp [coreScriptIsP2SH, size34]
  have pub := executeCoreScript_p2wshOutput flags ctx oracles bytes
  simp only [coreVerifyScript, verifyScriptWith, verifyCoreScripts, pushOnly, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool (LeanHash160.SHA256.hash bytes) then .ok ()
      else .error (CoreVerificationError.script .evalFalse)) _) = _
  simp [truth, enabled, decodeCoreWitnessProgram_p2wsh, noP2SH, ByteArray.size_empty,
    Except.bind, pure, Except.pure, verifyCoreWitnessProgram_p2wsh_eq]
  cases executeCoreWitnessScript (executeCoreScript flags ctx oracles) flags
      { scriptBytes := bytes, stack := other.reverse, sigVersion := .witnessV0 } <;>
    rfl

/-- A Core-ok typed runtime result is a success. -/
theorem coreRuntimeResult_eq_ok {result : WeightedResult} {stack : Stack}
    (ok : coreRuntimeResult result = .ok stack) :
    ∃ alt weight, result = .success stack alt weight := by
  cases result with
  | success stack alt weight =>
      simp only [coreRuntimeResult, Except.ok.injEq] at ok
      subst ok
      exact ⟨alt, weight, rfl⟩
  | failure error => simp [coreRuntimeResult] at ok

/-- Acceptance of any sane compiled P2WSH fragment supplies a successful
    runtime on the reversed witness, with a single truthy final item.
    Serialization and sanity supply the byte encoding and script-size bound. -/
theorem p2wshAccepted_runtime
    (sane : SaneFragment .p2wsh)
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (enabled : flags.witness = true)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    ∃ top alt weight,
      evaluateWithRuntimeLimits (oracles .witnessV0 bytes) (compile sane.checked.fragment)
        other.reverse [] flags.script (coreWitnessV0Context ctx) 0 =
          .success [top] alt weight ∧ castToBool top = true := by
  obtain ⟨spendKey, suffixEq, programTruth⟩ := spend
  subst spendKey suffixEq
  obtain ⟨serialized, hashes⟩ := serialized
  have small := compile_pushSize_le (fun data => by rw [hashes data]; decide)
    sane.checked.wellFormed
  have encoded : CoreTapscriptEncoding bytes 0 (compile sane.checked.fragment) :=
    CoreTapscriptEncoding.of_serializeScript _ bytes
      (fun element member => by have := small element member; omega) serialized
  have scriptSize : bytes.size ≤ 10000 := by
    have limits := sane.withinResourceLimits
    simp only [WithinResourceLimits, resourceLimitsSatisfied, Bool.and_eq_true] at limits
    have compiledLimit := limits.1.1
    change serializeScript (compileWithKeyHash modelKeyHash sane.checked.fragment) =
      .ok bytes at serialized
    rw [compiledScriptSizeWithinLimit,
      resourceSerializedScriptSize_eq_compileWithKeyHash modelKeyHash
        (fun key => hashes key.bytes), Script.serializedScriptSize, serialized]
      at compiledLimit
    simp only [Except.map, scriptSizeWithinContextLimit, saneScriptSizeLimit,
      MAX_STANDARD_P2WSH_SCRIPT_SIZE, decide_eq_true_eq] at compiledLimit
    omega
  rw [coreVerifyScript_p2wsh_eq_witnessScript flags ctx oracles keyPath other bytes
    programTruth enabled] at accepted
  obtain ⟨-, top, executed, truth⟩ :=
    executeCoreWitnessScript_ok_of_witnessV0 _ flags _ rfl accepted
  have runtime := executeCoreScript_eq_runtime_witnessV0 flags ctx oracles
    { scriptBytes := bytes, stack := other.reverse, sigVersion := .witnessV0 }
    (compile sane.checked.fragment) rfl scriptSize encoded
  rw [executed] at runtime
  obtain ⟨alt, weight, runtime⟩ := coreRuntimeResult_eq_ok runtime.symm
  exact ⟨top, alt, weight, runtime, truth⟩

/-- The existing run contract transfers an accepted P2WSH runtime to the
    model's evaluation relation under the environment's transaction context. -/
theorem p2wshAccepted_eval
    (sane : SaneFragment .p2wsh)
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    ∃ top alt, Eval (compile sane.checked.fragment) other.reverse [] flags.script env.txCtx
      (.success [top] alt) ∧ castToBool top = true := by
  obtain ⟨enabled, _, locktime, sequence, _, _, _, context, agreement⟩ := run
  obtain ⟨top, alt, weight, runtime, truth⟩ := p2wshAccepted_runtime sane bytes scriptPubKey
    suffix flags ctx oracles keyPath other serialized spend enabled accepted
  refine ⟨top, alt, ?_, truth⟩
  rw [context]
  exact evaluateWithRuntimeLimits_eval_success agreement locktime sequence runtime

/-- A truthy singleton from the `c:pk_h` opcode sequence determines both
    input positions and the successful hash and signature checks. -/
theorem checkSigHashTail_inversion
    (oracle : CryptoOracle) (flags : ScriptFlags) (ctx : TxContext)
    (hash : StackElement) (stack : Stack) {top : StackElement} {alt : Stack}
    (executed : evaluate oracle
      [.op .OP_DUP, .op .OP_HASH160, .pushData hash, .op .OP_EQUALVERIFY, .op .OP_CHECKSIG]
      stack [] flags ctx = .success [top] alt)
    (truth : castToBool top = true) :
    ∃ sig pubkey, stack = [pubkey, sig] ∧ alt = [] ∧ oracle.hash160 pubkey = hash ∧
      checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig pubkey =
        .ok true := by
  cases stack with
  | nil => simp [evaluate] at executed
  | cons pubkey rest =>
      simp only [evaluate] at executed
      by_cases hashMatches : hash = oracle.hash160 pubkey
      · rw [if_pos hashMatches] at executed
        cases rest with
        | nil => simp [evaluate] at executed
        | cons sig rest =>
            simp only [evaluate] at executed
            cases checked : checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig
                flags ctx sig pubkey with
            | error error => simp [checked] at executed
            | ok result =>
                simp only [checked, ExecResult.success.injEq,
                  List.cons.injEq] at executed
                obtain ⟨⟨topEq, restEq⟩, altEq⟩ := executed
                subst rest
                have resultTrue : result = true := by
                  rw [← topEq, castToBool_boolToElement] at truth
                  exact truth
                exact ⟨sig, pubkey, rfl, altEq.symm, hashMatches.symm, resultTrue ▸ checked⟩
      · simp [hashMatches] at executed

/-- Inversion of an accepted `c:pk_h(key)` spend under the existing run
    premises: the serialized witness is a signature followed by a public key
    with the committed HASH160, and its encoded signature check succeeds. -/
theorem p2wshAccepted_c_pk_h
    (sane : SaneFragment .p2wsh) (key : PubKey)
    (shape : sane.checked.fragment = .c (.pk_h key))
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    ∃ sig pubkey, other = [sig, pubkey] ∧ hash160 pubkey = hash160 key.bytes ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags.script env.txCtx sig pubkey =
        .ok true := by
  obtain ⟨top, alt, evaluated, truth⟩ := p2wshAccepted_eval sane bytes scriptPubKey suffix
    env flags ctx oracles keyPath other serialized spend run accepted
  rw [shape] at evaluated
  have executed := evaluate_eq_of_eval CryptoOracle.model_refines evaluated
  obtain ⟨sig, pubkey, stackEq, _, hashEq, checked⟩ :=
    checkSigHashTail_inversion CryptoOracle.model flags.script env.txCtx
      (hash160 key.bytes) other.reverse executed truth
  have otherEq := congrArg List.reverse stackEq
  simp only [List.reverse_reverse, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at otherEq
  exact ⟨sig, pubkey, otherEq, hashEq, checked⟩

/-- The generated final satisfaction of the subcase shape is the environment's
    single signature. -/
theorem satisfyFinal_c_pk_k {env : SatEnv} {key : PubKey} {arguments : Witness}
    (generated : satisfyFinal (.c (.pk_k key)) env = some arguments) :
    ∃ sig, env.signatureFor key = some sig ∧ arguments = [sig] := by
  simp only [satisfyFinal, satisfactionCandidates, keyCandidates] at generated
  cases signed : env.signatureFor key with
  | none => simp [signed] at generated
  | some sig =>
      simp only [signed, CandidateResult.usable, CandidateResult.finalWitness?] at generated
      exact ⟨sig, rfl, (Option.some.inj generated).symm⟩

/-- The checked structural subcase: a sane P2WSH fragment of the form
`c:pk_k(key)` is non-malleable at Core's VerifyScript. A third-party witness
that Core accepts on the same spend equals the generated satisfaction.

Premises: those of `P2WSHNonMalleability` restricted to the subcase shape.
The proof inverts the checked semantics of the accepted run
(`checkSigTail_inversion` via `executeCoreScript_eq_runtime_witnessV0`) and
pins the single accepted item with `ThirdPartyWitness`. -/
theorem p2wshNonMalleability_c_pk_k
    (sane : SaneFragment .p2wsh) (key : PubKey)
    (shape : sane.checked.fragment = .c (.pk_k key))
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (thirdParty : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  obtain ⟨top, alt, weight, runtime, truth⟩ := p2wshAccepted_runtime sane bytes scriptPubKey
    suffix flags ctx oracles keyPath other serialized spend run.1 accepted
  rw [shape, compile_c_pk_k] at runtime
  rw [shape] at generated thirdParty
  obtain ⟨_, _, _, _, _, _, _, context, agreement⟩ := run
  change (oracles .witnessV0 bytes).RefinesModel at agreement
  obtain ⟨sig, checked, stackEq, _, checksig, topEq⟩ :=
    checkSigTail_inversion _ flags.script _ rfl key.bytes other.reverse runtime
  have checkedTrue : checked = true := by
    rw [topEq, castToBool_boolToElement] at truth
    exact truth
  rw [checkedTrue] at checksig
  have validOracle : verifySigFor (oracles .witnessV0 bytes).checkSig
      (oracles .witnessV0 bytes).checkSchnorrSig (coreWitnessV0Context ctx) sig key.bytes =
        true :=
    verifySigFor_of_checkSigWithEncoding_true checksig
  have envCtx : env.txCtx = coreWitnessV0Context ctx := context
  have validModel : verifySigFor checkSig checkSchnorrSig env.txCtx sig key.bytes = true := by
    rw [envCtx, verifySigFor_witnessV0 (version := rfl)]
    rw [verifySigFor_witnessV0 (version := rfl)] at validOracle
    rw [← agreement.2.2.2.2.1]
    exact validOracle
  obtain ⟨sig0, _, argsEq⟩ := satisfyFinal_c_pk_k generated
  have otherEq : other = [sig] := by
    have reversed := congrArg List.reverse stackEq
    simp only [List.reverse_reverse, List.reverse_singleton] at reversed
    exact reversed
  have keyMember : key ∈ CoreFragment.keys (.c (.pk_k key)) := by simp [CoreFragment.keys]
  have sigMember : sig ∈ arguments :=
    thirdParty.2.1 sig (by rw [otherEq]; exact List.mem_singleton_self sig) key keyMember
      validModel
  rw [argsEq, List.mem_singleton] at sigMember
  rw [otherEq, sigMember, argsEq]

end LeanMiniscript.Extraction.P2WSHNonMalleabilitySubcase
