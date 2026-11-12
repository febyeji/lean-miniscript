import LeanMiniscript.Extraction.BitcoinCoreWitnessProofs
import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Bitcoin.ScriptBytes
import LeanMiniscript.Bitcoin.TaprootControlBlockProofs

/-!
Agreement between original-byte witness-v0 execution and the typed runtime,
and native P2WSH verification from a typed witness-script run.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin CoreScriptExecution

/-- The context Core gives every instruction of a witness-v0 script: the
witness-v0 signature version and no Taproot data. -/
def coreWitnessV0Context (ctx : TxContext) : TxContext :=
  { ctx with sigVersion := .witnessV0, taproot := none }

theorem instructionContext_witnessV0 (ctx : TxContext) (request : CoreScriptExecutionRequest)
    (state : CoreRawState) (version : request.sigVersion = .witnessV0) :
    instructionContext ctx request state = coreWitnessV0Context ctx := by
  simp +decide [instructionContext, coreWitnessV0Context, version]

private theorem coreRawStep_witnessV0 (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (version : request.sigVersion = .witnessV0)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (encoded : instruction.Encodes element) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep (oracles .witnessV0 request.scriptBytes) element state.runtime
        flags.script (coreWitnessV0Context ctx)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  rw [coreRawStep_encoded flags ctx oracles request state instruction element encoded,
    instructionContext_witnessV0 ctx request state version,
    runtimeStep_of_ne_base _ _ _ _ (by simp [coreWitnessV0Context])]
  simp [version, separatorOffset]

private theorem executeCoreRawLoop_witnessV0 (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest)
    (version : request.sigVersion = .witnessV0)
    (script : Script) (state : CoreRawState) (fuel : Nat)
    (enough : script.length < fuel)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (encoded : CoreTapscriptEncoding request.scriptBytes state.offset script) :
    executeCoreRawLoop flags ctx oracles request fuel state =
      coreRuntimeResult (evaluateRuntime (oracles .witnessV0 request.scriptBytes)
        script state.runtime flags.script (coreWitnessV0Context ctx)) := by
  induction script generalizing state fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          change state.offset = request.scriptBytes.size at encoded
          simp [executeCoreRawLoop, encoded, evaluateRuntime, finishRuntime]
          split <;> rfl
  | cons element rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [CoreTapscriptEncoding] at encoded
          cases decoded : readCoreRawInstruction request.scriptBytes state.offset with
          | error error => simp [decoded] at encoded
          | ok instruction =>
              simp only [decoded] at encoded
              rw [executeCoreRawLoop, if_neg (Nat.not_le_of_lt encoded.1)]
              simp only [decoded, bind, Except.bind, Except.mapError]
              rw [coreRawStep_witnessV0 flags ctx oracles request state instruction element
                version separatorOffset encoded.2.2.1]
              cases stepped : runtimeStep (oracles .witnessV0 request.scriptBytes) element
                  state.runtime flags.script (coreWitnessV0Context ctx) with
              | error error =>
                  simp [Except.mapError, Except.map, evaluateRuntime, stepped, coreRuntimeResult]
              | ok next =>
                  simp only [Except.mapError, Except.map, evaluateRuntime, stepped]
                  exact ih _ fuel (by simpa using enough) separatorOffset encoded.2.2.2

/-- Original-byte witness-v0 execution of at most 10,000 bytes and the typed
runtime have the same main-stack result and exact Script error for every
input stack and oracle. Both count operations up to 201. The byte-only
certificate excludes CODESEPARATOR and nonminimal pushes, so the script code
is the whole script. -/
theorem executeCoreScript_eq_runtime_witnessV0 (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .witnessV0)
    (small : request.scriptBytes.size ≤ 10000)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .witnessV0 request.scriptBytes)
        script request.stack [] flags.script (coreWitnessV0Context ctx)
        request.validationWeight) := by
  have bound := encoded.length_bound
  rw [executeCoreScript, if_neg (by simp [version]; omega), evaluateWithRuntimeLimits]
  exact executeCoreRawLoop_witnessV0 flags ctx oracles request version
    script _ _ (by omega) rfl encoded

/-- Argument sizes, typed execution, and a truthy singleton suffice for the
Core witness-script boundary of a witness-v0 script. -/
theorem executeCoreWitnessScript_of_witnessV0_runtime
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .witnessV0)
    (small : request.scriptBytes.size ≤ 10000)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script)
    (sizes : ∀ item ∈ request.stack, item.size ≤ maxScriptElementSize)
    {top : StackElement} {alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits (oracles .witnessV0 request.scriptBytes)
      script request.stack [] flags.script (coreWitnessV0Context ctx)
      request.validationWeight = .success [top] alt weight)
    (truth : castToBool top = true) :
    executeCoreWitnessScript (executeCoreScript flags ctx oracles) flags request = .ok () := by
  have elements : request.stack.any (fun item => item.size > maxScriptElementSize) = false := by
    simp only [List.any_eq_false]; intro item member
    simpa using Nat.not_lt.mpr (sizes item member)
  have raw := executeCoreScript_eq_runtime_witnessV0 flags ctx oracles request script
    version small encoded
  rw [executed] at raw
  simp only [coreRuntimeResult] at raw
  simp [executeCoreWitnessScript, version, elements, raw, bind, Except.bind]
  change (if castToBool top then Except.ok () else .error (CoreVerificationError.script .evalFalse)) = .ok ()
  simp [truth]

/-- The witness script of a P2WSH spend: the last witness item, run with the
other items reversed onto the stack. -/
def coreP2WSHRequest (arguments : List ByteArray) (script : ByteArray) :
    CoreScriptExecutionRequest :=
  { scriptBytes := script, stack := arguments.reverse, sigVersion := .witnessV0 }

/-- An accepted witness script whose SHA256 is the program passes native
witness-v0 dispatch. -/
theorem verifyCoreWitnessProgram_p2wsh
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (arguments : List ByteArray) (script : ByteArray) (isP2SH : Bool)
    (keyPath : CoreKeyPathChecker)
    (accepted : executeCoreWitnessScript execute flags
      (coreP2WSHRequest arguments script) = .ok ()) :
    verifyCoreWitnessProgram execute flags (arguments ++ [script]) 0
      (LeanHash160.SHA256.hash script) isP2SH keyPath = .ok () := by
  simpa [verifyCoreWitnessProgram, sha256_size, List.reverse_append, coreP2WSHRequest,
    bind, Except.bind, pure, Except.pure] using accepted

private theorem p2wsh_size (script : ByteArray) : (ScriptBytes.p2wsh script).size = 34 := by
  simp [ScriptBytes.p2wsh, sha256_size]
  rfl

private theorem p2wsh_first (script : ByteArray) :
    (ScriptBytes.p2wsh script)[0]! = 0x00 ∧ (ScriptBytes.p2wsh script)[1]! = 0x20 := by
  have zero : 0 < (ScriptBytes.p2wsh script).size := by rw [p2wsh_size]; omega
  have one : 1 < (ScriptBytes.p2wsh script).size := by rw [p2wsh_size]; omega
  constructor
  · rw [getElem!_pos (ScriptBytes.p2wsh script) 0 zero]
    change (ByteArray.mk #[0x00, 0x20] ++ LeanHash160.SHA256.hash script)[0] = _
    rw [ByteArray.getElem_append_left (by decide)]
    rfl
  · rw [getElem!_pos (ScriptBytes.p2wsh script) 1 one]
    change (ByteArray.mk #[0x00, 0x20] ++ LeanHash160.SHA256.hash script)[1] = _
    rw [ByteArray.getElem_append_left (by decide)]
    rfl

private theorem p2wsh_payload (script : ByteArray) :
    (ScriptBytes.p2wsh script).extract 2 34 = LeanHash160.SHA256.hash script :=
  ByteArray.extract_append_eq_right (a := ByteArray.mk #[0x00, 0x20])
    (b := LeanHash160.SHA256.hash script) (i := 2) (j := 34) rfl (by simp [sha256_size]; rfl)

/-- Core recognizes a P2WSH output as the witness-v0 program of its script's
SHA256. -/
theorem decodeCoreWitnessProgram_p2wsh (script : ByteArray) :
    decodeCoreWitnessProgram? (ScriptBytes.p2wsh script) =
      some (0, LeanHash160.SHA256.hash script) := by
  simp only [decodeCoreWitnessProgram?, (p2wsh_first script).1, (p2wsh_first script).2,
    p2wsh_size]
  simp [p2wsh_payload]

/-- A P2WSH output executes as two BASE pushes before witness dispatch. -/
theorem executeCoreScript_p2wshOutput (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (script : ByteArray) :
    executeCoreScript flags ctx oracles { scriptBytes := ScriptBytes.p2wsh script } =
      .ok [LeanHash160.SHA256.hash script, ByteArray.empty] := by
  have first : readCoreRawInstruction (ScriptBytes.p2wsh script) 0 =
      .ok ⟨0x00, ByteArray.empty, 1⟩ := by
    simp only [readCoreRawInstruction, (p2wsh_first script).1, p2wsh_size]
    simp [pure, Except.pure]
  have second : readCoreRawInstruction (ScriptBytes.p2wsh script) 1 =
      .ok ⟨0x20, LeanHash160.SHA256.hash script, 34⟩ := by
    simp only [readCoreRawInstruction, (p2wsh_first script).2, p2wsh_size]
    simp [p2wsh_payload, pure, Except.pure]
  simp +decide [executeCoreScript, p2wsh_size, executeCoreRawLoop,
    first, second, coreRawStep, coreLegacyDisabledOpcode, coreLegacyMinimalPush,
    runtimeStep_pushData, runtimeInstruction, executeRuntimeElement,
    ScriptElement.pushSize, prepareValidationWeight,
    evaluate.eq_1, evaluate.eq_2, checkRuntimeStack,
    maxScriptElementSize, maxStackSize, sha256_size,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- For a truthy program, native P2WSH verification reduces to its witness
verifier. Empty scriptSig execution, P2SH exclusion, and cleanstack are proved. -/
theorem verifyCoreScripts_p2wsh
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (verifyWitness : CoreWitnessVerifier) (script : ByteArray) (witness : List ByteArray)
    (truth : castToBool (LeanHash160.SHA256.hash script) = true)
    (enabled : flags.witness = true)
    (accepted : verifyWitness witness 0 (LeanHash160.SHA256.hash script) false = .ok ()) :
    verifyCoreScripts (executeCoreScript flags ctx oracles) verifyWitness flags
      ByteArray.empty (ScriptBytes.p2wsh script) witness = .ok () := by
  have empty : executeCoreScript flags ctx oracles { scriptBytes := ByteArray.empty } =
      .ok [] := by
    simp [executeCoreScript, executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have noP2SH : coreScriptIsP2SH (ScriptBytes.p2wsh script) = false := by
    simp [coreScriptIsP2SH, p2wsh_size]
  have pub := executeCoreScript_p2wshOutput flags ctx oracles script
  simp only [verifyCoreScripts, pushOnly, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool (LeanHash160.SHA256.hash script) then .ok ()
      else .error (CoreVerificationError.script .evalFalse)) _) = .ok ()
  simp [truth, enabled, decodeCoreWitnessProgram_p2wsh, noP2SH, accepted,
    ByteArray.size_empty, Except.bind, pure, Except.pure]

/-- Typed witness-v0 execution that ends in one truthy item reaches the
complete Core VerifyScript entry point for the native P2WSH output of its
script, with the actual raw executor. -/
theorem verifyCoreScripts_of_witnessV0_runtime
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : List ByteArray)
    (bytes : ByteArray) (script : Script)
    (enabled : flags.witness = true)
    (encoded : CoreTapscriptEncoding bytes 0 script)
    (small : bytes.size ≤ 10000)
    (sizes : ∀ item ∈ arguments, item.size ≤ maxScriptElementSize)
    (programTruth : castToBool (LeanHash160.SHA256.hash bytes) = true)
    {top : StackElement} {alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits (oracles .witnessV0 bytes)
      script arguments.reverse [] flags.script (coreWitnessV0Context ctx) 0 =
        .success [top] alt weight)
    (truth : castToBool top = true) :
    verifyCoreScripts (executeCoreScript flags ctx oracles)
      (fun witness version program isP2SH => verifyCoreWitnessProgram
        (executeCoreScript flags ctx oracles) flags witness version program isP2SH keyPath)
      flags ByteArray.empty (ScriptBytes.p2wsh bytes) (arguments ++ [bytes]) = .ok () := by
  apply verifyCoreScripts_p2wsh flags ctx oracles _ bytes _ programTruth enabled
  apply verifyCoreWitnessProgram_p2wsh _ flags arguments bytes false keyPath
  exact executeCoreWitnessScript_of_witnessV0_runtime flags ctx oracles
    (coreP2WSHRequest arguments bytes) script rfl small encoded
    (by simpa [coreP2WSHRequest] using sizes) executed truth

end LeanMiniscript.Extraction
