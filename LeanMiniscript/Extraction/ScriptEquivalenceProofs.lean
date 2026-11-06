import LeanMiniscript.Extraction.ScriptEquivalence

/-!
Facts about the typed reader and executor of `ScriptEquivalence`, the three
execution obligations, and the coverage of the six VerifyScript boundaries.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-- The reader returns only elements the instruction encodes. -/
theorem typedElement?_encodes {instruction : CoreRawInstruction} {element : ScriptElement}
    (read : typedElement? instruction = some element) : instruction.Encodes element := by
  simp only [typedElement?] at read
  split at read
  · split at read
    · cases read
      assumption
    · cases read
  · cases read

theorem decodeTypedScriptFrom_encoding {bytes : ByteArray} {fuel offset : Nat}
    {script : Script} (decoded : decodeTypedScriptFrom bytes fuel offset = some script) :
    CoreTapscriptEncoding bytes offset script := by
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
                simp only [CoreTapscriptEncoding, read]
                exact ⟨bounds.1, bounds.2, typedElement?_encodes typed, ih decodedRest⟩
              · cases decoded
            · cases decoded

/-- A typed reading is a complete GetOp decoding with a typed element for
every instruction. -/
theorem decodeTypedScript?_encoding {bytes : ByteArray} {script : Script}
    (decoded : decodeTypedScript? bytes = some script) :
    CoreTapscriptEncoding bytes 0 script :=
  decodeTypedScriptFrom_encoding decoded

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

/-- Tapscript whole-script execution: the typed reading supplies the byte
certificate of `executeCoreScript_eq_runtime`. -/
theorem tapscriptExecutionAgreement : TapscriptExecutionAgreement := by
  intro flags ctx oracles request version
  have notLegacy :
      (request.sigVersion != .tapscript && decide (request.scriptBytes.size > 10000)) = false := by
    simp +decide [version]
  unfold executeTypedScript
  simp only [notLegacy, Bool.false_eq_true, ↓reduceIte]
  cases decoded : decodeTypedScript? request.scriptBytes with
  | none => rfl
  | some script =>
      have notBase : (coreTapscriptContext ctx request).sigVersion ≠ .base := by
        simp [coreTapscriptContext]
      dsimp only
      rw [executeCoreScript_eq_runtime flags ctx oracles request script version
          (decodeTypedScript?_encoding decoded),
        typedScriptContext_tapscript ctx request version, version,
        evaluateScriptCodeRuntime_of_ne_base _ _ _ _ notBase]
      rfl

/-- Before the first OP_CODESEPARATOR, Core's instruction context is the typed
script's context. -/
theorem instructionContext_typedScriptContext (ctx : TxContext)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff) :
    instructionContext ctx request state = typedScriptContext ctx request := by
  simp [instructionContext, typedScriptContext, separatorPosition]

/-- Core's raw loop over bytes with a typed reading is typed whole-script
execution with the whole script as script code, under every signature version.
A typed reading has no OP_CODESEPARATOR, so the script code stays whole. -/
theorem executeCoreRawLoop_typed (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script) (state : CoreRawState)
    (fuel : Nat) (enough : script.length < fuel)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff)
    (encoded : CoreTapscriptEncoding request.scriptBytes state.offset script) :
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
          simp only [CoreTapscriptEncoding] at encoded
          cases decoded : readCoreRawInstruction request.scriptBytes state.offset with
          | error error => simp [decoded] at encoded
          | ok instruction =>
              simp only [decoded] at encoded
              have code : request.scriptBytes.extract state.codeSeparatorOffset
                  request.scriptBytes.size = request.scriptBytes := by simp [separatorOffset]
              rw [executeCoreRawLoop, if_neg (Nat.not_le_of_lt encoded.1)]
              simp only [decoded, bind, Except.bind, Except.mapError]
              rw [coreRawStep_encoded flags ctx oracles request state instruction element
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
          have encoded := decodeTypedScript?_encoding decoded
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
