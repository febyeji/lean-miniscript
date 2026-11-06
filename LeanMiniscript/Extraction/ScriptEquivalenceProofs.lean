import LeanMiniscript.Extraction.ScriptEquivalence

/-!
Facts about the typed reader and executor of `ScriptEquivalence`, the three
execution obligations, the six VerifyScript obligations, and the coverage of
the six VerifyScript boundaries.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-- The reader returns only elements the instruction reads as. -/
theorem typedElement?_readsAs {instruction : CoreRawInstruction} {element : ScriptElement}
    (read : typedElement? instruction = some element) : instruction.ReadsAs element := by
  simp only [typedElement?] at read
  split at read
  · split at read
    · cases read
      assumption
    · cases read
  · cases read

/-- Complete source-order reading with Core's GetOp boundaries, every
instruction reading as its typed element: `CoreTapscriptEncoding` with
`badOpcode` elements as well. -/
def CoreTypedReading (bytes : ByteArray) : Nat → Script → Prop
  | offset, [] => offset = bytes.size
  | offset, element :: rest =>
      match readCoreRawInstruction bytes offset with
      | .error _ => False
      | .ok instruction =>
          offset < bytes.size ∧ offset < instruction.nextOffset ∧
          instruction.ReadsAs element ∧
          CoreTypedReading bytes instruction.nextOffset rest

theorem CoreTypedReading.length_bound {bytes : ByteArray} {offset : Nat} {script : Script}
    (read : CoreTypedReading bytes offset script) : offset + script.length ≤ bytes.size := by
  induction script generalizing offset with
  | nil => simpa [CoreTypedReading] using Nat.le_of_eq read
  | cons element rest ih =>
      simp only [CoreTypedReading] at read
      cases decoded : readCoreRawInstruction bytes offset with
      | error error => simp [decoded] at read
      | ok instruction =>
          simp only [decoded] at read
          have tail := ih read.2.2.2
          simp only [List.length_cons]
          omega

theorem decodeTypedScriptFrom_reading {bytes : ByteArray} {fuel offset : Nat}
    {script : Script} (decoded : decodeTypedScriptFrom bytes fuel offset = some script) :
    CoreTypedReading bytes offset script := by
  induction fuel generalizing offset script with
  | zero => simp [decodeTypedScriptFrom] at decoded
  | succ fuel ih =>
      unfold decodeTypedScriptFrom at decoded
      split at decoded
      · cases decoded
        assumption
      · cases read : readCoreRawInstruction bytes offset with
        | error error => simp [read] at decoded
        | ok instruction =>
            simp only [read] at decoded
            split at decoded
            · rename_i bounds
              split at decoded
              · rename_i element rest typed decodedRest
                cases decoded
                simp only [CoreTypedReading, read]
                exact ⟨bounds.1, bounds.2, typedElement?_readsAs typed, ih decodedRest⟩
              · cases decoded
            · cases decoded

/-- A typed reading is a complete GetOp decoding with a typed element for
every instruction. -/
theorem decodeTypedScript?_reading {bytes : ByteArray} {script : Script}
    (decoded : decodeTypedScript? bytes = some script) :
    CoreTypedReading bytes 0 script :=
  decodeTypedScriptFrom_reading decoded

/-- With one oracle and an empty script code, typed whole-script execution is
`evaluateRuntime`. -/
theorem evaluateScriptCodeRuntime_withoutScriptCode (oracle : CryptoOracle) (script : Script)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    evaluateScriptCodeRuntime oracle script state flags ctx =
      evaluateRuntime oracle script state flags ctx := by
  induction script generalizing state with
  | nil => rfl
  | cons element rest ih =>
      simp only [evaluateScriptCodeRuntime, evaluateRuntime]
      cases runtimeStep oracle element state flags ctx with
      | error => rfl
      | ok next => exact ih next

/-- Outside BASE no step removes signatures, so typed whole-script execution
is `evaluateRuntime` with the oracle for the script code. -/
theorem evaluateScriptCodeRuntime_of_ne_base (oracles : ScriptCodeOracles) (script : Script)
    (state : RuntimeState) (flags : ScriptFlags) {ctx : TxContext}
    (version : ctx.sigVersion ≠ .base) :
    evaluateScriptCodeRuntime oracles script state flags ctx =
      evaluateRuntime (oracles.oracleFor oracles.scriptCode) script state flags ctx := by
  induction script generalizing state with
  | nil => rfl
  | cons element rest ih =>
      simp only [evaluateScriptCodeRuntime, evaluateRuntime,
        runtimeStep_of_ne_base oracles element state flags version]
      cases runtimeStep (oracles.oracleFor oracles.scriptCode) element state flags ctx with
      | error => rfl
      | ok next => exact ih next

theorem typedScriptContext_tapscript (ctx : TxContext) (request : CoreScriptExecutionRequest)
    (version : request.sigVersion = .tapscript) :
    typedScriptContext ctx request = coreTapscriptContext ctx request := by
  simp +decide [typedScriptContext, coreTapscriptContext, version]

/-- Before the first OP_CODESEPARATOR, Core's instruction context is the typed
script's context. -/
theorem instructionContext_typedScriptContext (ctx : TxContext)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff) :
    instructionContext ctx request state = typedScriptContext ctx request := by
  simp [instructionContext, typedScriptContext, separatorPosition]

/-- The raw step of an instruction that reads as a typed element is the typed
step, as `coreRawStep_encoded` and `coreRawStep_badOpcode` give it. -/
theorem coreRawStep_readsAs (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (read : instruction.ReadsAs element) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        element state.runtime flags.script (instructionContext ctx request state)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  cases element with
  | badOpcode opcode =>
      exact coreRawStep_badOpcode flags ctx oracles request state instruction opcode read.1 read.2
  | op | pushData | pushNum =>
      exact coreRawStep_encoded flags ctx oracles request state instruction _ read

/-- Core's raw loop over bytes with a typed reading is typed whole-script
execution with the whole script as script code, under every signature version.
A typed reading has no OP_CODESEPARATOR, so the script code stays whole. -/
theorem executeCoreRawLoop_typed (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script) (state : CoreRawState)
    (fuel : Nat) (enough : script.length < fuel)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff)
    (encoded : CoreTypedReading request.scriptBytes state.offset script) :
    executeCoreRawLoop flags ctx oracles request fuel state =
      coreRuntimeResult (evaluateScriptCodeRuntime
        ⟨oracles request.sigVersion, request.scriptBytes⟩ script state.runtime flags.script
        (typedScriptContext ctx request)) := by
  induction script generalizing state fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          change state.offset = request.scriptBytes.size at encoded
          simp [executeCoreRawLoop, encoded, evaluateScriptCodeRuntime, finishRuntime]
          split <;> rfl
  | cons element rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [CoreTypedReading] at encoded
          cases decoded : readCoreRawInstruction request.scriptBytes state.offset with
          | error error => simp [decoded] at encoded
          | ok instruction =>
              simp only [decoded] at encoded
              have code : request.scriptBytes.extract state.codeSeparatorOffset
                  request.scriptBytes.size = request.scriptBytes := by simp [separatorOffset]
              rw [executeCoreRawLoop, if_neg (Nat.not_le_of_lt encoded.1)]
              simp only [decoded, bind, Except.bind, Except.mapError]
              rw [coreRawStep_readsAs flags ctx oracles request state instruction element
                  encoded.2.2.1, code,
                instructionContext_typedScriptContext ctx request state separatorPosition]
              cases stepped : runtimeStep ⟨oracles request.sigVersion, request.scriptBytes⟩
                  element state.runtime flags.script (typedScriptContext ctx request) with
              | error error =>
                  simp [Except.mapError, Except.map, evaluateScriptCodeRuntime, stepped,
                    coreRuntimeResult]
              | ok next =>
                  simp only [Except.mapError, Except.map, evaluateScriptCodeRuntime, stepped]
                  exact ih _ fuel (by simpa using enough) separatorOffset separatorPosition
                    encoded.2.2.2

/-- Whole-script execution under every signature version: both executors
reject a BASE or witness-v0 script over 10,000 bytes, and the typed reading
supplies the byte certificate of `executeCoreRawLoop_typed`. -/
theorem scriptExecutionAgreement (version : SignatureVersion) :
    ScriptExecutionAgreement version := by
  intro flags ctx oracles request _
  unfold executeTypedScript
  split
  · next large => simp only [executeCoreScript, large, ↓reduceIte]
  · next small =>
      cases decoded : decodeTypedScript? request.scriptBytes with
      | none => rfl
      | some script =>
          have encoded := decodeTypedScript?_reading decoded
          have bound := encoded.length_bound
          dsimp only
          rw [executeCoreScript, if_neg small]
          exact executeCoreRawLoop_typed flags ctx oracles request script _ _ (by omega)
            rfl rfl encoded

/-- BASE whole-script execution. Active signature opcodes remove their
signatures from the whole script on both sides, and both count operations up
to 201. -/
theorem baseExecutionAgreement : BaseExecutionAgreement :=
  scriptExecutionAgreement .base

/-- Witness-v0 whole-script execution. Both sides count operations up to 201. -/
theorem witnessV0ExecutionAgreement : WitnessV0ExecutionAgreement :=
  scriptExecutionAgreement .witnessV0

/-- Tapscript whole-script execution. The witness boundary scans for
OP_SUCCESSx before either executor runs; a `badOpcode` byte that reaches them
fails on both sides only when executed. -/
theorem tapscriptExecutionAgreement : TapscriptExecutionAgreement :=
  scriptExecutionAgreement .tapscript

/-- Core's raw loop and the typed executor are the same executor: each request
runs under its own signature version, where `scriptExecutionAgreement` holds. -/
theorem executeCoreScript_eq_executeTypedScript (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle) :
    executeCoreScript flags ctx oracles = executeTypedScript flags ctx oracles :=
  funext fun request =>
    scriptExecutionAgreement request.sigVersion flags ctx oracles request rfl

/-- `coreVerifyScript` and `typedVerifyScript` pass `verifyScriptWith` the
same executor, so they give the same verdict on every input. -/
theorem coreVerifyScript_eq_typedVerifyScript (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (scriptSig scriptPubKey : ByteArray)
    (witness : List ByteArray) :
    coreVerifyScript flags ctx oracles keyPath scriptSig scriptPubKey witness =
      typedVerifyScript flags ctx oracles keyPath scriptSig scriptPubKey witness := by
  rw [coreVerifyScript, typedVerifyScript, executeCoreScript_eq_executeTypedScript]

/-- Every VerifyScript boundary: the verdicts agree on every input, so they
agree on the inputs of one boundary. -/
theorem verifyScriptAgreement (boundary : VerifyScriptBoundary) :
    VerifyScriptAgreement boundary :=
  fun flags ctx oracles keyPath scriptSig scriptPubKey witness _ =>
    coreVerifyScript_eq_typedVerifyScript flags ctx oracles keyPath scriptSig scriptPubKey
      witness

/-- The legacy boundary: scriptSig and scriptPubKey run as BASE scripts. -/
theorem legacyVerificationAgreement : LegacyVerificationAgreement :=
  verifyScriptAgreement .legacy

/-- The P2SH boundary: scriptSig, scriptPubKey, and the redeem script run as
BASE scripts. -/
theorem p2shVerificationAgreement : P2SHVerificationAgreement :=
  verifyScriptAgreement .p2sh

/-- The native witness-v0 boundary: the witness script or P2WPKH template
runs as a witness-v0 script. -/
theorem witnessV0VerificationAgreement : WitnessV0VerificationAgreement :=
  verifyScriptAgreement .witnessV0

/-- The P2SH-wrapped witness-v0 boundary: the redeem script runs as a BASE
script and the witness script or P2WPKH template as a witness-v0 script. -/
theorem p2shWitnessV0VerificationAgreement : P2SHWitnessV0VerificationAgreement :=
  verifyScriptAgreement .p2shWitnessV0

/-- The Taproot key-path boundary: both sides check the signature with the
same key-path checker. -/
theorem taprootKeyPathVerificationAgreement : TaprootKeyPathVerificationAgreement :=
  verifyScriptAgreement .taprootKeyPath

/-- The Taproot script-path boundary: a version-0xc0 leaf runs as a Tapscript
script. -/
theorem taprootScriptPathVerificationAgreement : TaprootScriptPathVerificationAgreement :=
  verifyScriptAgreement .taprootScriptPath

/-- `verifyScriptBoundary` covers every input, so the six boundary
obligations together give the agreement for every input. -/
theorem verifyScriptAgreement_of_boundaries
    (legacy : LegacyVerificationAgreement) (p2sh : P2SHVerificationAgreement)
    (witnessV0 : WitnessV0VerificationAgreement)
    (p2shWitnessV0 : P2SHWitnessV0VerificationAgreement)
    (keyPath : TaprootKeyPathVerificationAgreement)
    (scriptPath : TaprootScriptPathVerificationAgreement)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (checker : CoreKeyPathChecker)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray) :
    coreVerifyScript flags ctx oracles checker scriptSig scriptPubKey witness =
      typedVerifyScript flags ctx oracles checker scriptSig scriptPubKey witness := by
  cases boundary : verifyScriptBoundary flags scriptSig scriptPubKey witness
  · exact legacy flags ctx oracles checker scriptSig scriptPubKey witness boundary
  · exact p2sh flags ctx oracles checker scriptSig scriptPubKey witness boundary
  · exact witnessV0 flags ctx oracles checker scriptSig scriptPubKey witness boundary
  · exact p2shWitnessV0 flags ctx oracles checker scriptSig scriptPubKey witness boundary
  · exact keyPath flags ctx oracles checker scriptSig scriptPubKey witness boundary
  · exact scriptPath flags ctx oracles checker scriptSig scriptPubKey witness boundary

end LeanMiniscript.Extraction
