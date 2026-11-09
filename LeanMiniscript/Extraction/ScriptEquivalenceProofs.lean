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
  repeat' split at read
  all_goals first
    | (cases read; assumption)
    | (cases read)

/-- Complete source-order reading with Core's GetOp boundaries, every
instruction reading as its typed element: `CoreTapscriptEncoding` with
`badOpcode`, `illegalOpcode`, and `nonminimalPush` elements as well. Where
GetOp fails inside the bytes, the last element is a `truncatedPush` of the
bytes from there to the end. -/
def CoreTypedReading (bytes : ByteArray) : Nat → Script → Prop
  | offset, [] => offset = bytes.size
  | offset, element :: rest =>
      match readCoreRawInstruction bytes offset with
      | .error _ =>
          offset < bytes.size ∧ rest = [] ∧
            ∃ push, element = .truncatedPush push ∧
              push.bytes = bytes.extract offset bytes.size
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
      | error error =>
          simp only [decoded] at read
          obtain ⟨inside, empty, _⟩ := read
          subst empty
          simp only [List.length_cons, List.length_nil]
          omega
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
        | error error =>
            simp only [read] at decoded
            split at decoded
            · rename_i truncated
              cases decoded
              simp only [CoreTypedReading, read]
              exact ⟨truncated.1, by simp, _, rfl, rfl⟩
            · cases decoded
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

/-- The typed context after an executed OP_CODESEPARATOR is Core's
instruction context with its codesep position. -/
theorem withCodeSeparatorPosition_instructionContext (ctx : TxContext)
    (request : CoreScriptExecutionRequest) (state : CoreRawState) (position : UInt32) :
    withCodeSeparatorPosition (instructionContext ctx request state) position =
      instructionContext ctx request { state with codeSeparatorPosition := position } := by
  cases version : request.sigVersion <;> cases taproot : ctx.taproot <;>
    simp [instructionContext, withCodeSeparatorPosition, version, taproot]

/-- The raw step of an instruction that reads as a typed element other than
OP_CODESEPARATOR is the typed step, as `coreRawStep_encoded`,
`coreRawStep_badOpcode`, `coreRawStep_illegalOpcode`, and
`coreRawStep_nonminimalPush` give it. -/
theorem coreRawStep_readsAs (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (notCodeSeparator : ∀ n, element ≠ .codeSeparator n)
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
  | illegalOpcode opcode =>
      exact coreRawStep_illegalOpcode flags ctx oracles request state instruction opcode
        read.1 read.2
  | nonminimalPush push =>
      exact coreRawStep_nonminimalPush flags ctx oracles request state instruction push
        read.1 read.2
  | codeSeparator => exact absurd rfl (notCodeSeparator _)
  | op | pushData | pushNum | truncatedPush =>
      exact coreRawStep_encoded flags ctx oracles request state instruction _ read

/-- Core's raw loop over bytes with a typed reading is typed whole-script
execution, under every signature version: the script code and the Tapscript
codesep position follow the last executed OP_CODESEPARATOR on both sides. -/
theorem executeCoreRawLoop_typed (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script) (state : CoreRawState)
    (fuel : Nat) (enough : script.length < fuel)
    (encoded : CoreTypedReading request.scriptBytes state.offset script) :
    executeCoreRawLoop flags ctx oracles request fuel state =
      evaluateScriptCodeRuntime (oracles request.sigVersion) request.scriptBytes
        state.opcodePosition state.codeSeparatorOffset script state.runtime flags.script
        (instructionContext ctx request state) := by
  induction script generalizing state fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          change state.offset = request.scriptBytes.size at encoded
          simp [executeCoreRawLoop, encoded, evaluateScriptCodeRuntime]
  | cons element rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [CoreTypedReading] at encoded
          cases decoded : readCoreRawInstruction request.scriptBytes state.offset with
          | error error =>
              simp only [decoded] at encoded
              obtain ⟨inside, empty, push, truncated, _⟩ := encoded
              subst empty truncated
              rw [readCoreRawInstruction_error decoded] at decoded
              rw [executeCoreRawLoop, if_neg (Nat.not_le_of_lt inside)]
              simp [decoded, evaluateScriptCodeRuntime, runtimeStep_truncatedPush,
                bind, Except.bind, Except.mapError]
          | ok instruction =>
              simp only [decoded] at encoded
              obtain ⟨inside, advancing, readsAs, restReading⟩ := encoded
              rw [executeCoreRawLoop, if_neg (Nat.not_le_of_lt inside)]
              simp only [decoded, bind, Except.bind, Except.mapError]
              cases element with
              | codeSeparator nextOffset =>
                  simp only [CoreRawInstruction.ReadsAs] at readsAs
                  obtain ⟨byte, payload, nextEq⟩ := readsAs
                  rw [coreRawStep_codeSeparator flags ctx oracles request state instruction byte
                    payload, nextEq]
                  have sv : (instructionContext ctx request state).sigVersion =
                      request.sigVersion := rfl
                  simp only [evaluateScriptCodeRuntime, sv]
                  by_cases over : request.sigVersion != .tapscript &&
                      maxOpsPerScript < state.runtime.operationCount + 1
                  · simp [over]
                  · by_cases const : request.sigVersion == .base && flags.script.constScriptCode
                    · simp [over, const]
                    · simp only [over, const]
                      cases stepped : runtimeStep
                          ⟨oracles request.sigVersion, request.scriptBytes.extract
                            state.codeSeparatorOffset request.scriptBytes.size⟩
                          (.codeSeparator instruction.nextOffset) state.runtime flags.script
                          (instructionContext ctx request state) with
                      | error error =>
                          simp [Except.mapError, Except.map]
                      | ok next =>
                          simp only [Except.mapError, Except.map]
                          by_cases active : state.runtime.conditions.all id = true
                          · simp only [active, ↓reduceIte]
                            rw [withCodeSeparatorPosition_instructionContext]
                            exact ih _ fuel (by simpa using enough) restReading
                          · have inactive : state.runtime.conditions.all id = false :=
                              Bool.eq_false_iff.mpr active
                            simp only [inactive]
                            exact ih _ fuel (by simpa using enough) restReading
              | badOpcode opcode =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.badOpcode opcode) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | illegalOpcode opcode =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.illegalOpcode opcode) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | nonminimalPush push =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.nonminimalPush push) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | op opcode =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.op opcode) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | pushData data =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.pushData data) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | pushNum number =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.pushNum number) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading
              | truncatedPush push =>
                  rw [coreRawStep_readsAs flags ctx oracles request state instruction _
                    (fun _ same => by cases same) readsAs]
                  cases stepped : runtimeStep
                      ⟨oracles request.sigVersion, request.scriptBytes.extract
                        state.codeSeparatorOffset request.scriptBytes.size⟩
                      (.truncatedPush push) state.runtime flags.script
                      (instructionContext ctx request state) with
                  | error error =>
                      simp [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                  | ok next =>
                      simp only [stepped, evaluateScriptCodeRuntime, Except.mapError, Except.map]
                      exact ih _ fuel (by simpa using enough) restReading

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
          rw [executeCoreScript, if_neg small,
            ← instructionContext_typedScriptContext ctx request
              ({ runtime := { stack := request.stack, altStack := [], weight := request.validationWeight } } : CoreRawState) rfl]
          exact executeCoreRawLoop_typed flags ctx oracles request script _ _ (by omega) encoded

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
fails on both sides only when executed, and an `illegalOpcode` byte (OP_VERIF
or OP_VERNOTIF, the ones that are not OP_SUCCESSx) fails on both sides
wherever it appears. -/
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
