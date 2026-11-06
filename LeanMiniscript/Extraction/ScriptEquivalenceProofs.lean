import LeanMiniscript.Extraction.ScriptEquivalence

/-!
Facts about the typed reader and executor of `ScriptEquivalence`, the
Tapscript execution obligation, and the coverage of the six VerifyScript
boundaries.
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
