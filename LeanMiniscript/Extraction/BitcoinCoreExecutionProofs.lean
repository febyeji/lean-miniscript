import LeanMiniscript.Extraction.BitcoinCoreScriptExecution
import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.RuntimeErasure
import LeanMiniscript.Miniscript.CompileConcrete

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-!
Agreement between original-byte Tapscript execution and the typed runtime.
Encoding conditions describe only bytes and instruction boundaries; they do
not depend on a witness, an oracle, or either interpreter's result.
-/

private def rawNumber (value : Nat) : Int :=
  if value == 0x4f then -1 else value - 0x50

private def encodesPush (instruction : CoreRawInstruction) (data : ByteArray) : Prop :=
  let value := instruction.opcode.toNat
  if value ≤ 0x4e then
    instruction.payload = data ∧ coreLegacyMinimalPush value data = true
  else if value == 0x4f || (0x51 ≤ value && value ≤ 0x60) then
    instruction.payload = ByteArray.empty ∧ scriptNum (rawNumber value) = data
  else False

/-- A raw instruction has the typed instruction's opcode or pushed bytes.
Length-prefixed pushes must be minimal so MINIMALDATA is preserved as well,
and no instruction encodes a `nonminimalPush`. No instruction encodes a
`badOpcode` or an `illegalOpcode`: Tapscript reads most of their bytes as
OP_SUCCESSx, which these encodings exclude. -/
def _root_.LeanMiniscript.Script.CoreRawInstruction.Encodes (instruction : CoreRawInstruction) :
    ScriptElement → Prop
  | .pushData data => encodesPush instruction data
  | .pushNum number => encodesPush instruction (scriptNum number)
  | .op opcode => instruction.opcode = opcodeByte opcode ∧
      instruction.payload = ByteArray.empty
  | .badOpcode _ => False
  | .illegalOpcode _ => False
  | .nonminimalPush _ => False

instance (instruction : CoreRawInstruction) (element : ScriptElement) :
    Decidable (instruction.Encodes element) := by
  cases element <;> unfold CoreRawInstruction.Encodes encodesPush <;> infer_instance

/-- Modeled encodings contain only pushes, numeric constants, and AST opcodes. -/
theorem _root_.LeanMiniscript.Script.CoreRawInstruction.Encodes.opcodeCases
    {instruction : CoreRawInstruction} {element : ScriptElement}
    (encoded : instruction.Encodes element) :
    instruction.opcode.toNat ≤ 0x4e ∨ instruction.opcode.toNat = 0x4f ∨
      (0x51 ≤ instruction.opcode.toNat ∧ instruction.opcode.toNat ≤ 0x60) ∨
      ∃ opcode, instruction.opcode = opcodeByte opcode := by
  cases element with
  | op opcode => exact Or.inr (Or.inr (Or.inr ⟨opcode, encoded.1⟩))
  | badOpcode => exact encoded.elim
  | illegalOpcode => exact encoded.elim
  | nonminimalPush => exact encoded.elim
  | pushData | pushNum =>
      simp only [CoreRawInstruction.Encodes, encodesPush] at encoded
      split at encoded
      · exact Or.inl (by assumption)
      · split at encoded
        · rename_i numeric
          simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
            decide_eq_true_eq] at numeric
          rcases numeric with number | range
          · exact Or.inr (Or.inl number)
          · exact Or.inr (Or.inr (Or.inl range))
        · contradiction

/-- Complete source-order decoding, with strictly advancing offsets and no
trailing bytes. This is a decidable, input-only certificate. -/
def CoreTapscriptEncoding (bytes : ByteArray) : Nat → Script → Prop
  | offset, [] => offset = bytes.size
  | offset, element :: rest =>
      match readCoreRawInstruction bytes offset with
      | .error _ => False
      | .ok instruction =>
          offset < bytes.size ∧ offset < instruction.nextOffset ∧
          instruction.Encodes element ∧
          CoreTapscriptEncoding bytes instruction.nextOffset rest

instance coreTapscriptEncodingDecidable (bytes : ByteArray) (offset : Nat) (script : Script) :
    Decidable (CoreTapscriptEncoding bytes offset script) :=
  match script with
  | [] => inferInstanceAs (Decidable (offset = bytes.size))
  | element :: rest => by
      unfold CoreTapscriptEncoding
      cases readCoreRawInstruction bytes offset with
      | error error => exact isFalse id
      | ok instruction =>
          haveI := coreTapscriptEncodingDecidable bytes instruction.nextOffset rest
          infer_instance

/-- Tapscript metadata installed by the raw executor when the script contains
only modeled instructions, which do not include CODESEPARATOR. -/
def coreTapscriptContext (ctx : TxContext) (request : CoreScriptExecutionRequest) : TxContext :=
  { ctx with
    sigVersion := .tapscript
    taproot := ctx.taproot.map fun taproot =>
      { taproot with
        annex := request.annex
        spendPath := .scriptPath request.scriptBytes request.leafVersion 0xffffffff } }

private theorem runtimeStep_pushNum (oracle : CryptoOracle) (number : Int)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (.pushNum number) state flags ctx =
      runtimeStep oracle (.pushData (scriptNum number)) state flags ctx := by
  simp [runtimeStep_pushNumber, runtimeStep_pushData, runtimeInstruction, executeRuntimeElement,
    ScriptElement.pushSize, prepareValidationWeight, evaluate.eq_1, evaluate.eq_2, evaluate.eq_3]

/-- Byte facts shared by every modeled opcode: it lies above OP_16 and is
neither disabled, reserved, nor CODESEPARATOR, and only OP_SHA1 has Core's
own branch for 0xa7. -/
theorem opcodeByte_modeled (opcode : Opcode) :
    0x60 < (opcodeByte opcode).toNat ∧
      coreLegacyDisabledOpcode (opcodeByte opcode).toNat = false ∧
      (opcodeByte opcode).toNat ≠ 0x65 ∧ (opcodeByte opcode).toNat ≠ 0x66 ∧
      ((opcodeByte opcode).toNat = 0xa7 ↔ opcode = .OP_SHA1) ∧
      (opcodeByte opcode).toNat ≠ 0xab := by
  cases opcode <;> decide

/-- Core's fallback of a disabled timelock to OP_NOP is the typed step's own. -/
theorem runtimeStep_coreTimelockFallback (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (.op (if (opcode == .OP_CHECKLOCKTIMEVERIFY && !flags.checkLockTimeVerify) ||
        (opcode == .OP_CHECKSEQUENCEVERIFY && !flags.checkSequenceVerify) then .OP_NOP
      else opcode)) state flags ctx = runtimeStep oracle (.op opcode) state flags ctx := by
  cases opcode
  case OP_CHECKLOCKTIMEVERIFY =>
    cases off : flags.checkLockTimeVerify
    · rw [runtimeStep_checkLockTimeVerify_off oracle state ctx off]
      simp +decide
    · simp +decide
  case OP_CHECKSEQUENCEVERIFY =>
    cases off : flags.checkSequenceVerify
    · rw [runtimeStep_checkSequenceVerify_off oracle state ctx off]
      simp +decide
    · simp +decide
  all_goals simp +decide

/-- The timelock fallback hands FindAndDelete the same signatures. -/
theorem instructionSignatures_coreTimelockFallback (opcode : Opcode) (state : RuntimeState)
    (flags : ScriptFlags) :
    instructionSignatures (if (opcode == .OP_CHECKLOCKTIMEVERIFY && !flags.checkLockTimeVerify) ||
        (opcode == .OP_CHECKSEQUENCEVERIFY && !flags.checkSequenceVerify) then .OP_NOP
      else opcode) state flags = instructionSignatures opcode state flags := by
  cases opcode <;> simp +decide <;> split <;> rfl

/-- The raw step of OP_SHA1 is the typed step. Core runs 0xa7 on a branch of
its own: outside Tapscript it counts one operation, an executed step replaces
the top item with its SHA-1 hash or fails on an empty stack, and a skipped
step only checks the stack size. -/
private theorem coreRawStep_sha1 (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction)
    (byte : instruction.opcode = opcodeByte .OP_SHA1)
    (payload : instruction.payload = ByteArray.empty) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        (.op .OP_SHA1) state.runtime flags.script (instructionContext ctx request state)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  have version : (instructionContext ctx request state).sigVersion = request.sigVersion := rfl
  unfold coreRawStep
  simp only [payload, byte, ByteArray.size_empty, maxScriptElementSize]
  obtain ⟨⟨stack, altStack, conditions, weight, count⟩, offset, position, separatorOffset,
    separatorPosition⟩ := state
  rcases versionEq : request.sigVersion <;>
    by_cases over : maxOpsPerScript < count + 1 <;>
    by_cases inactive : false ∈ conditions <;>
    rcases stack with _ | ⟨top, rest⟩ <;>
    simp +decide [versionEq, over, inactive, opcodeByte, runtimeStep, chargeOperations,
      chargedOperationCount, opcodeKeyCount, ScriptCodeOracles.forStep, instructionSignatures,
      removeSignatures, runtimeInstruction, executeRuntimeElement, prepareValidationWeight,
      evaluate, ScriptElement.underTimelockFlags, version, bind, Except.bind, Except.mapError,
      Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The raw step of a modeled opcode is the typed step on the same runtime
state, given the script code after the last OP_CODESEPARATOR and the oracle
for each script code of the request's signature version. -/
theorem coreRawStep_op (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (opcode : Opcode)
    (encoded : instruction.Encodes (.op opcode)) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        (.op opcode) state.runtime flags.script (instructionContext ctx request state)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  obtain ⟨byte, payload⟩ := encoded
  by_cases sha1 : opcode = .OP_SHA1
  · subst sha1
    exact coreRawStep_sha1 flags ctx oracles request state instruction byte payload
  obtain ⟨high, enabled, not65, not66, sha1Byte, notSeparator⟩ := opcodeByte_modeled opcode
  have notSha1 : (opcodeByte opcode).toNat ≠ 0xa7 := fun same => sha1 (sha1Byte.mp same)
  have mapped := runtimeStep_coreTimelockFallback
    (state := state.runtime) (flags := flags.script) (ctx := instructionContext ctx request state)
    (opcode := opcode)
  have notPush : ¬ (opcodeByte opcode).toNat ≤ 78 := by omega
  have not79 : (opcodeByte opcode).toNat ≠ 79 := by omega
  have notSmall : ¬ (opcodeByte opcode).toNat ≤ 96 := by omega
  have version : (instructionContext ctx request state).sigVersion = request.sigVersion := rfl
  unfold coreRawStep
  simp only [payload, byte, ByteArray.size_empty, maxScriptElementSize, enabled,
    opcodeFromByte_opcodeByte, mapped, instructionSignatures_coreTimelockFallback]
  rw [runtimeStep_eq_forStep ⟨oracles request.sigVersion,
    request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩]
  simp [notPush, not79, notSmall, not65, not66, notSha1, notSeparator, high,
    bind, Except.bind, Except.mapError, Except.map, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, ScriptCodeOracles.forStep, version]
  have overflow : maxOpsPerScript < state.runtime.operationCount + 1 →
      request.sigVersion ≠ .tapscript →
      chargeOperations (.op opcode) state.runtime flags.script (instructionContext ctx request state) =
        .error .opCount := by
    intro over tap
    simp [chargeOperations, chargedOperationCount, version, tap, over, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, Except.map]
  by_cases tap : request.sigVersion = .tapscript
  · cases charging : chargeOperations (.op opcode) state.runtime flags.script
        (instructionContext ctx request state) with
    | error => simp [tap, show (SignatureVersion.tapscript != SignatureVersion.tapscript) = false from rfl]
    | ok =>
        simp only [tap, show (SignatureVersion.tapscript != SignatureVersion.tapscript) = false
          from rfl, Bool.false_eq_true, ↓reduceIte]
        split <;> split <;> rfl
  · by_cases over : maxOpsPerScript < state.runtime.operationCount + 1
    · simp [over, overflow over tap]
    · cases charging : chargeOperations (.op opcode) state.runtime flags.script
          (instructionContext ctx request state) with
      | error => simp [over]
      | ok =>
          have notTap : (request.sigVersion != .tapscript) = true := by
            cases versionEq : request.sigVersion <;> first | rfl | exact absurd versionEq tap
          simp only [notTap, over, ↓reduceIte]
          split <;> split <;> rfl

/-- The raw step of an instruction that encodes a typed element is the typed
step on the same runtime state, under every signature version, given the
script code after the last OP_CODESEPARATOR and the oracle for each script
code of the request's signature version. -/
theorem coreRawStep_encoded (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (encoded : instruction.Encodes element) :
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
  | op opcode => exact coreRawStep_op flags ctx oracles request state instruction opcode encoded
  | badOpcode => exact encoded.elim
  | illegalOpcode => exact encoded.elim
  | nonminimalPush => exact encoded.elim
  | pushData data =>
      rw [runtimeStep_of_signatures _ _ _ _ _ (fun _ element => by cases element)]
      simp only [CoreRawInstruction.Encodes, encodesPush] at encoded
      split at encoded
      next push =>
        obtain ⟨payload, minimal⟩ := encoded
        have notDisabled : coreLegacyDisabledOpcode instruction.opcode.toNat = false := by
          simp [coreLegacyDisabledOpcode]
          omega
        have low : instruction.opcode.toNat ≠ 0x65 ∧ instruction.opcode.toNat ≠ 0x66 ∧
            instruction.opcode.toNat ≠ 0xab := by omega
        have uncounted : ¬ 0x60 < instruction.opcode.toNat := by omega
        by_cases large : data.size > maxScriptElementSize
        · simp +decide [coreRawStep, payload, large, runtimeStep_pushData, runtimeInstruction,
            executeRuntimeElement, ScriptElement.pushSize, bind, Except.bind,
            Except.mapError, Except.map, pure, Except.pure, throw]
          rfl
        · simp +decide [coreRawStep, payload, notDisabled, low.1, low.2.1, low.2.2,
            uncounted, push, minimal, large,
            bind, Except.bind, Except.mapError, Except.map, pure, Except.pure]
      next notPush =>
        split at encoded
        next numeric =>
          obtain ⟨payload, dataEq⟩ := encoded
          have numberBounds : instruction.opcode.toNat = 0x4f ∨
              (0x51 ≤ instruction.opcode.toNat ∧ instruction.opcode.toNat ≤ 0x60) := by
            simpa using numeric
          have notDisabled : coreLegacyDisabledOpcode instruction.opcode.toNat = false := by
            simp [coreLegacyDisabledOpcode]
            omega
          have low : instruction.opcode.toNat ≠ 0x65 ∧ instruction.opcode.toNat ≠ 0x66 ∧
              instruction.opcode.toNat ≠ 0xab := by omega
          have uncounted : ¬ 0x60 < instruction.opcode.toNat := by omega
          simp +decide [coreRawStep, payload, notDisabled, low.1, low.2.1, low.2.2,
            uncounted, notPush, numeric, maxScriptElementSize,
            runtimeStep_pushNum, ← dataEq, rawNumber, bind, Except.bind,
            Except.mapError, Except.map, pure, Except.pure]
        next => contradiction
  | pushNum number =>
      rw [runtimeStep_of_signatures _ _ _ _ _ (fun _ element => by cases element),
        runtimeStep_pushNum, ← runtimeStep_of_signatures _ _ _ _ _
          (fun _ element => by cases element)]
      exact coreRawStep_encoded flags ctx oracles request state instruction
        (.pushData (scriptNum number)) encoded
termination_by match element with | .pushNum _ => 1 | _ => 0

/-- A `badOpcode` byte is no push or numeric constant, and Core's raw step
reaches its unmodeled-opcode branch: the byte is not disabled, OP_VERIF,
OP_VERNOTIF, OP_SHA1, OP_CODESEPARATOR, or a modeled opcode. -/
theorem _root_.LeanMiniscript.Script.BadOpcode.byte_facts (opcode : BadOpcode) :
    0x4f < opcode.byte.toNat ∧ ¬ (0x51 ≤ opcode.byte.toNat ∧ opcode.byte.toNat ≤ 0x60) ∧
      coreLegacyDisabledOpcode opcode.byte.toNat = false ∧
      opcode.byte.toNat ≠ 0x65 ∧ opcode.byte.toNat ≠ 0x66 ∧ opcode.byte.toNat ≠ 0xa7 ∧
      opcode.byte.toNat ≠ 0xab ∧ opcodeFromByte? opcode.byte.toNat = none := by
  obtain ⟨byte, bad⟩ := opcode
  simp only [isBadOpcodeByte] at bad
  dsimp only
  have bound := byte.toNat_lt
  generalize byte.toNat = value at bad bound ⊢
  revert bad
  revert bound
  revert value
  decide +kernel

/-- The raw step of a `badOpcode` byte is the typed step: outside Tapscript a
byte above OP_16 counts one operation, an executed byte fails with BAD_OPCODE,
and a skipped byte only checks the stack size. -/
theorem coreRawStep_badOpcode (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (opcode : BadOpcode)
    (byte : instruction.opcode = opcode.byte)
    (payload : instruction.payload = ByteArray.empty) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        (.badOpcode opcode) state.runtime flags.script (instructionContext ctx request state)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  obtain ⟨high, notNumber, enabled, not65, not66, notSha1, notSeparator, unmodeled⟩ :=
    opcode.byte_facts
  have version : (instructionContext ctx request state).sigVersion = request.sigVersion := rfl
  have notPush : ¬ opcode.byte.toNat ≤ 78 := by omega
  have not79 : opcode.byte.toNat ≠ 79 := by omega
  unfold coreRawStep
  simp only [payload, byte, ByteArray.size_empty, maxScriptElementSize, enabled]
  simp [notPush, not79, notNumber, not65, not66, notSha1, notSeparator, unmodeled,
    runtimeStep, chargeOperations, ScriptCodeOracles.forStep, removeSignatures,
    runtimeInstruction, executeRuntimeElement, prepareValidationWeight, evaluate,
    ScriptElement.pushSize, ScriptElement.underTimelockFlags, version,
    bind, Except.bind, Except.mapError, Except.map, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  have whole : { state.runtime with operationCount := state.runtime.operationCount } =
      state.runtime := rfl
  by_cases skip : request.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 96
  · have notCounted : ¬ ((request.sigVersion != .tapscript) = true ∧ 96 < opcode.byte.toNat) := by
      rcases skip with tap | low
      · rw [tap]
        exact fun counted => absurd counted.1 (by decide)
      · omega
    rw [if_neg notCounted, if_pos skip, whole]
    by_cases inactive : false ∈ state.runtime.conditions <;> simp only [inactive, ↓reduceIte]
  · simp only [not_or] at skip
    have counted : (request.sigVersion != .tapscript) = true ∧ 96 < opcode.byte.toNat := by
      refine ⟨?_, by omega⟩
      cases versionEq : request.sigVersion <;> first | rfl | exact absurd versionEq skip.1
    rw [if_pos counted, if_neg (not_or.mpr skip)]
    by_cases over : maxOpsPerScript < state.runtime.operationCount + 1 <;>
      simp only [over, ↓reduceIte]
    by_cases inactive : false ∈ state.runtime.conditions <;> simp only [inactive, ↓reduceIte]

/-- An `illegalOpcode` byte is above OP_16, and Core's raw step rejects it as
`IllegalOpcode.error` does: a disabled opcode with DISABLED_OPCODE, OP_VERIF
and OP_VERNOTIF with BAD_OPCODE. -/
theorem _root_.LeanMiniscript.Script.IllegalOpcode.byte_facts (opcode : IllegalOpcode) :
    0x60 < opcode.byte.toNat ∧
      (coreLegacyDisabledOpcode opcode.byte.toNat = true ∧ opcode.error = .disabledOpcode ∨
        coreLegacyDisabledOpcode opcode.byte.toNat = false ∧
          (opcode.byte.toNat = 0x65 ∨ opcode.byte.toNat = 0x66) ∧
          opcode.error = .badOpcode) := by
  have illegal := opcode.isIllegal
  have bound := opcode.byte.toNat_lt
  simp only [isIllegalOpcodeByte] at illegal
  simp only [IllegalOpcode.error]
  generalize opcode.byte.toNat = value at illegal bound ⊢
  revert illegal
  revert bound
  revert value
  decide +kernel

/-- The raw step of an `illegalOpcode` byte is the typed step: outside
Tapscript the byte counts one operation, and in an executed or skipped branch
the step fails with `IllegalOpcode.error`. -/
theorem coreRawStep_illegalOpcode (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (opcode : IllegalOpcode)
    (byte : instruction.opcode = opcode.byte)
    (payload : instruction.payload = ByteArray.empty) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        (.illegalOpcode opcode) state.runtime flags.script
        (instructionContext ctx request state)).mapError CoreVerificationError.script).map
          fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  obtain ⟨high, rejected⟩ := opcode.byte_facts
  have version : (instructionContext ctx request state).sigVersion = request.sigVersion := rfl
  have typed : runtimeStep
      ⟨oracles request.sigVersion,
        request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
      (.illegalOpcode opcode) state.runtime flags.script (instructionContext ctx request state) =
        if request.sigVersion = .tapscript then .error opcode.error
        else if maxOpsPerScript < state.runtime.operationCount + 1 then .error .opCount
        else .error opcode.error := by
    by_cases tap : request.sigVersion = .tapscript
    · simp [tap, version, runtimeStep, chargeOperations, ScriptCodeOracles.forStep,
        removeSignatures, runtimeInstruction, executeRuntimeElement, ScriptElement.pushSize,
        bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    · by_cases over : maxOpsPerScript < state.runtime.operationCount + 1 <;>
        simp [tap, over, version, runtimeStep, chargeOperations, ScriptCodeOracles.forStep,
          removeSignatures, runtimeInstruction, executeRuntimeElement, ScriptElement.pushSize,
          bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [typed]
  unfold coreRawStep
  simp only [payload, byte, ByteArray.size_empty, maxScriptElementSize]
  have tapOff : (SignatureVersion.tapscript != SignatureVersion.tapscript) = false := by decide
  by_cases tap : request.sigVersion = .tapscript
  · rcases rejected with ⟨disabled, error⟩ | ⟨enabled, verif, error⟩ <;>
      simp [*, bind, Except.bind, Except.mapError, Except.map, throw, throwThe,
        MonadExceptOf.throw]
  · have counted : (request.sigVersion != .tapscript) = true := by
      cases versionEq : request.sigVersion <;> first | rfl | exact absurd versionEq tap
    by_cases over : maxOpsPerScript < state.runtime.operationCount + 1 <;>
      rcases rejected with ⟨disabled, error⟩ | ⟨enabled, verif, error⟩ <;>
      simp [*, bind, Except.bind, Except.mapError, Except.map, throw, throwThe,
        MonadExceptOf.throw]

/-- A `nonminimalPush` opcode is a push opcode that Core's raw step does not
take as minimal. -/
theorem _root_.LeanMiniscript.Script.NonminimalPush.byte_facts (push : NonminimalPush) :
    push.opcode.toNat ≤ 0x4e ∧ coreLegacyMinimalPush push.opcode.toNat push.data = false := by
  have nonminimal := push.isNonminimal
  simp only [isNonminimalPush, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at nonminimal
  refine ⟨?_, nonminimal.2⟩
  have fits := nonminimal.1
  split at fits
  · omega
  · split at fits
    · rename_i pushData1
      simp only [beq_iff_eq] at pushData1
      omega
    · split at fits
      · rename_i pushData2
        simp only [beq_iff_eq] at pushData2
        omega
      · simp only [Bool.and_eq_true, beq_iff_eq] at fits
        omega

/-- The typed step of a `nonminimalPush` is the step of a push of its data,
except that an executed push fails with MINIMALDATA when the flag is on. -/
theorem runtimeStep_nonminimalPush (oracles : ScriptCodeOracles) (push : NonminimalPush)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracles (.nonminimalPush push) state flags ctx =
      if push.data.size > maxScriptElementSize then .error .pushSize
      else if (state.conditions.all id && flags.minimalData) = true then .error .minimalData
      else runtimeStep (oracles.oracleFor oracles.scriptCode) (.pushData push.data)
        state flags ctx := by
  rw [runtimeStep_of_signatures _ _ _ _ _ (fun _ element => by cases element),
    runtimeStep_pushData]
  by_cases large : push.data.size > maxScriptElementSize
  · simp [large, runtimeStep, chargeOperations, runtimeInstruction, executeRuntimeElement,
      ScriptElement.pushSize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · by_cases inactive : false ∈ state.conditions <;>
      cases minimal : flags.minimalData <;>
      simp [large, inactive, minimal, runtimeStep, chargeOperations, runtimeInstruction,
        executeRuntimeElement, ScriptElement.pushSize, prepareValidationWeight, evaluate,
        ScriptElement.underTimelockFlags, bind, Except.bind, pure, Except.pure, throw,
        throwThe, MonadExceptOf.throw]

/-- The raw step of a push that is not minimal is the typed step: an oversized
push fails with PUSH_SIZE, an executed push fails with MINIMALDATA when the
flag is on and otherwise pushes its data, and a skipped push only checks the
stack size. -/
theorem coreRawStep_nonminimalPush (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (push : NonminimalPush)
    (byte : instruction.opcode = push.opcode)
    (payload : instruction.payload = push.data) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep
        ⟨oracles request.sigVersion,
          request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size⟩
        (.nonminimalPush push) state.runtime flags.script
        (instructionContext ctx request state)).mapError CoreVerificationError.script).map
          fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  obtain ⟨low, notMinimal⟩ := push.byte_facts
  have notDisabled : coreLegacyDisabledOpcode push.opcode.toNat = false := by
    simp [coreLegacyDisabledOpcode]
    omega
  have notSpecial : push.opcode.toNat ≠ 0x65 ∧ push.opcode.toNat ≠ 0x66 ∧
      push.opcode.toNat ≠ 0xab := by omega
  have uncounted : ¬ 0x60 < push.opcode.toNat := by omega
  rw [runtimeStep_nonminimalPush]
  by_cases large : push.data.size > maxScriptElementSize
  · simp [coreRawStep, payload, large, bind, Except.bind, Except.mapError, Except.map,
      throw, throwThe, MonadExceptOf.throw]
  · simp only [if_neg large]
    cases active : state.runtime.conditions.all id <;>
      cases minimal : flags.script.minimalData <;>
      simp +decide [coreRawStep, byte, payload, large, notDisabled, notSpecial.1,
        notSpecial.2.1, notSpecial.2.2, uncounted, low, notMinimal, active, minimal, bind,
        Except.bind, Except.mapError, Except.map, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]

private theorem coreRawStep_tapscript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (version : request.sigVersion = .tapscript)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff)
    (encoded : instruction.Encodes element) :
    coreRawStep flags ctx oracles request state instruction =
      ((runtimeStep (oracles .tapscript request.scriptBytes) element state.runtime
        flags.script (coreTapscriptContext ctx request)).mapError
          CoreVerificationError.script).map fun runtime =>
            { state with
              runtime := runtime
              offset := instruction.nextOffset
              opcodePosition := state.opcodePosition + 1 } := by
  have context : instructionContext ctx request state = coreTapscriptContext ctx request := by
    simp +decide [instructionContext, coreTapscriptContext, version, separatorPosition]
  have code : request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size =
      request.scriptBytes := by simp [separatorOffset]
  cases element with
  | badOpcode => exact encoded.elim
  | illegalOpcode => exact encoded.elim
  | nonminimalPush => exact encoded.elim
  | op opcode =>
      have notBase : (instructionContext ctx request state).sigVersion ≠ .base := by
        show request.sigVersion ≠ .base
        rw [version]
        decide
      rw [coreRawStep_op flags ctx oracles request state instruction opcode encoded,
        runtimeStep_of_ne_base _ _ _ _ notBase]
      dsimp only
      rw [context, code, version]
  | pushData data =>
      simp only [CoreRawInstruction.Encodes, encodesPush] at encoded
      split at encoded
      next push =>
        obtain ⟨payload, minimal⟩ := encoded
        have notDisabled : coreLegacyDisabledOpcode instruction.opcode.toNat = false := by
          simp [coreLegacyDisabledOpcode]
          omega
        have low : instruction.opcode.toNat ≠ 0x65 ∧ instruction.opcode.toNat ≠ 0x66 ∧
            instruction.opcode.toNat ≠ 0xab := by omega
        by_cases large : data.size > maxScriptElementSize
        · simp +decide [coreRawStep, payload, large, runtimeStep_pushData, runtimeInstruction,
            executeRuntimeElement, ScriptElement.pushSize, bind, Except.bind,
            Except.mapError, Except.map, pure, Except.pure, throw]
          rfl
        · simp +decide [coreRawStep, payload, version, context, code, notDisabled,
            low.1, low.2.1, low.2.2, push, minimal, large,
            bind, Except.bind, Except.mapError, Except.map, pure, Except.pure]
      next notPush =>
        split at encoded
        next numeric =>
          obtain ⟨payload, dataEq⟩ := encoded
          have numberBounds : instruction.opcode.toNat = 0x4f ∨
              (0x51 ≤ instruction.opcode.toNat ∧ instruction.opcode.toNat ≤ 0x60) := by
            simpa using numeric
          have notDisabled : coreLegacyDisabledOpcode instruction.opcode.toNat = false := by
            simp [coreLegacyDisabledOpcode]
            omega
          have low : instruction.opcode.toNat ≠ 0x65 ∧ instruction.opcode.toNat ≠ 0x66 ∧
              instruction.opcode.toNat ≠ 0xab := by omega
          simp +decide [coreRawStep, payload, version, context, code, notDisabled, low.1,
            low.2.1, low.2.2, notPush, numeric, maxScriptElementSize,
            runtimeStep_pushNum, ← dataEq, rawNumber, bind, Except.bind,
            Except.mapError, Except.map, pure, Except.pure]
        next => contradiction
  | pushNum number =>
      rw [runtimeStep_pushNum]
      exact coreRawStep_tapscript flags ctx oracles request state instruction
        (.pushData (scriptNum number)) version separatorOffset separatorPosition encoded
termination_by match element with | .pushNum _ => 1 | _ => 0

/-- The Core executor exposes the main stack or Script error. The runtime
also retains the alternate stack and remaining signature budget. -/
def coreRuntimeResult : WeightedResult → Except CoreVerificationError Stack
  | .success stack _ _ => .ok stack
  | .failure error => .error (.script error)

theorem CoreTapscriptEncoding.length_bound {bytes : ByteArray}
    {offset : Nat} {script : Script} (encoded : CoreTapscriptEncoding bytes offset script) :
    offset + script.length ≤ bytes.size := by
  induction script generalizing offset with
  | nil => simpa [CoreTapscriptEncoding] using Nat.le_of_eq encoded
  | cons element rest ih =>
      simp only [CoreTapscriptEncoding] at encoded
      cases decoded : readCoreRawInstruction bytes offset with
      | error error => simp [decoded] at encoded
      | ok instruction =>
          simp only [decoded] at encoded
          have tail := ih encoded.2.2.2
          simp only [List.length_cons]
          omega

private theorem executeCoreRawLoop_tapscript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest)
    (version : request.sigVersion = .tapscript)
    (script : Script) (state : CoreRawState) (fuel : Nat)
    (enough : script.length < fuel)
    (separatorOffset : state.codeSeparatorOffset = 0)
    (separatorPosition : state.codeSeparatorPosition = 0xffffffff)
    (encoded : CoreTapscriptEncoding request.scriptBytes state.offset script) :
    executeCoreRawLoop flags ctx oracles request fuel state =
      coreRuntimeResult (evaluateRuntime (oracles .tapscript request.scriptBytes)
        script state.runtime flags.script (coreTapscriptContext ctx request)) := by
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
              rw [coreRawStep_tapscript flags ctx oracles request state instruction element
                version separatorOffset separatorPosition encoded.2.2.1]
              cases stepped : runtimeStep (oracles .tapscript request.scriptBytes) element
                  state.runtime flags.script (coreTapscriptContext ctx request) with
              | error error =>
                  simp [Except.mapError, Except.map, evaluateRuntime, stepped, coreRuntimeResult]
              | ok next =>
                  simp only [Except.mapError, Except.map, evaluateRuntime, stepped]
                  exact ih _ fuel (by simpa using enough) separatorOffset separatorPosition encoded.2.2.2

/-- Original-byte Tapscript execution and the typed runtime have the same
main-stack result and exact Script error for every input stack and oracle.
The byte-only certificate excludes CODESEPARATOR and nonminimal pushes. Witness
commitments, OP_SUCCESS scanning and initial witness limits are caller checks. -/
theorem executeCoreScript_eq_runtime (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        script request.stack [] flags.script (coreTapscriptContext ctx request)
        request.validationWeight) := by
  have bound := encoded.length_bound
  simp only [executeCoreScript, version, show (SignatureVersion.tapscript != .tapscript) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, evaluateWithRuntimeLimits]
  exact executeCoreRawLoop_tapscript flags ctx oracles request version
    script _ _ (by omega) rfl rfl encoded

/-- Under the existing cryptographic refinement assumption, every successful
raw execution has the same main stack in the relational Script semantics. -/
theorem executeCoreScript_eval_success (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.script.checkLockTimeVerify = true)
    (sequence : flags.script.checkSequenceVerify = true)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script)
    (agreement : (oracles .tapscript request.scriptBytes).RefinesModel)
    (stack : Stack) (success : executeCoreScript flags ctx oracles request = .ok stack) :
    ∃ alt, Eval script request.stack [] flags.script (coreTapscriptContext ctx request)
      (.success stack alt) := by
  rw [executeCoreScript_eq_runtime flags ctx oracles request script version encoded] at success
  cases evaluated : evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
      script request.stack [] flags.script (coreTapscriptContext ctx request)
      request.validationWeight with
  | failure error => simp [evaluated, coreRuntimeResult] at success
  | success result alt weight =>
      simp only [evaluated, coreRuntimeResult, Except.ok.injEq] at success
      subst result
      exact ⟨alt, evaluateWithRuntimeLimits_eval_success agreement locktime sequence evaluated⟩

@[simp] private theorem singleton_size (byte : UInt8) : (⟨#[byte]⟩ : ByteArray).size = 1 := rfl
private theorem get_middle (before data after : ByteArray) (i : Nat) (small : i < data.size) :
    (before ++ data ++ after)[before.size + i]! = data[i]! := by
  have bound : before.size + i < (before ++ data ++ after).size := by simp; omega
  rw [getElem!_pos (before ++ data ++ after) (before.size + i) bound, getElem!_pos data i small]
  rw [ByteArray.getElem_append_left (by simp; omega),
    ByteArray.getElem_append_right (by omega)]
  simp
private theorem extract_middle (before data after : ByteArray) :
    (before ++ data ++ after).extract before.size (before.size + data.size) = data := by
  rw [ByteArray.extract_append]
  simp [ByteArray.extract_append_eq_right rfl rfl]
private theorem read_opcode (before after : ByteArray) (byte : UInt8) (high : byte.toNat > 0x4e) :
    readCoreRawInstruction (before ++ ⟨#[byte]⟩ ++ after) before.size =
      .ok ⟨byte, ByteArray.empty, before.size + 1⟩ := by
  have first : (before ++ ⟨#[byte]⟩ ++ after)[before.size]! = byte := by
    simpa [ByteArray.getElem_eq_getElem_data] using get_middle before ⟨#[byte]⟩ after 0 (by simp)
  simp [readCoreRawInstruction, first, high, bind, Except.bind, pure, Except.pure, Nat.add_assoc]
  omega
private theorem read_short (before data after : ByteArray) (small : data.size < 76) :
    readCoreRawInstruction (before ++ (⟨#[UInt8.ofNat data.size]⟩ ++ data) ++ after) before.size =
      .ok ⟨UInt8.ofNat data.size, data, before.size + 1 + data.size⟩ := by
  have byte : (UInt8.ofNat data.size).toNat = data.size := by
    simp [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show data.size < 256 by omega)]
  have first : (before ++ (⟨#[UInt8.ofNat data.size]⟩ ++ data) ++ after)[before.size]! =
      UInt8.ofNat data.size := by
    have found := get_middle before ⟨#[UInt8.ofNat data.size]⟩ (data ++ after) 0 (by simp)
    simpa [ByteArray.append_assoc, ByteArray.getElem_eq_getElem_data] using found
  have fits : before.size + 1 + data.size ≤
      (before ++ (⟨#[UInt8.ofNat data.size]⟩ ++ data) ++ after).size := by simp; omega
  have payload : (before ++ (⟨#[UInt8.ofNat data.size]⟩ ++ data) ++ after).extract
      (before.size + 1) (before.size + 1 + data.size) = data := by
    simpa [ByteArray.append_assoc] using extract_middle (before ++ ⟨#[UInt8.ofNat data.size]⟩) data after
  simp [readCoreRawInstruction, first, byte, show ¬ data.size > 78 by omega,
    show data.size ≤ 75 by omega, payload, bind, Except.bind, pure, Except.pure]
  repeat first | split | omega | rfl

private theorem singleton_of_size_one (data : ByteArray) (size : data.size = 1) :
    data = ⟨#[data.get! 0]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using size
  · intro index left right
    have zero : index = 0 := by
      have : index < 1 := by simpa using right
      omega
    subst index
    simp [ByteArray.get!, size]

private theorem read_serializePushData (data encoded : ByteArray)
    (small : data.size < 76) (serialized : serializePushData data = .ok encoded)
    (before after : ByteArray) :
    ∃ instruction,
      readCoreRawInstruction (before ++ encoded ++ after) before.size = .ok instruction ∧
      instruction.nextOffset = before.size + encoded.size ∧ 0 < encoded.size ∧
      instruction.Encodes (.pushData data) := by
  have byteSize : (UInt8.ofNat data.size).toNat = data.size := by
    simp [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show data.size < 256 by omega)]
  have ordinary (serialized : serializeLengthPrefixedPush data = .ok encoded)
      (minimal : coreLegacyMinimalPush data.size data = true) :
      ∃ instruction,
        readCoreRawInstruction (before ++ encoded ++ after) before.size = .ok instruction ∧
        instruction.nextOffset = before.size + encoded.size ∧ 0 < encoded.size ∧
        instruction.Encodes (.pushData data) := by
    have bytes : encoded = ⟨#[UInt8.ofNat data.size]⟩ ++ data := by
      simp only [serializeLengthPrefixedPush, pushDataPrefix, if_pos small,
        bind, Except.bind, pure, Except.pure, Except.ok.injEq] at serialized
      rw [← serialized]
      apply ByteArray.ext
      simp
    subst encoded
    refine ⟨_, read_short before data after small, ?_, ?_, ?_⟩
    · simp [Nat.add_assoc]
    · simp; omega
    · simp [CoreRawInstruction.Encodes, encodesPush, byteSize,
        show data.size ≤ 78 by omega, minimal]
  simp only [serializePushData] at serialized
  split at serialized
  next one =>
    split at serialized
    next positive =>
      simp only [pure, Except.pure, Except.ok.injEq] at serialized
      subst encoded
      have high : (UInt8.ofNat (0x50 + (data.get! 0).toNat)).toNat =
          0x50 + (data.get! 0).toNat := by
        exact UInt8.toNat_ofNat_of_lt' (by change 0x50 + (data.get! 0).toNat < 256; omega)
      refine ⟨_, read_opcode before after _ (by rw [high]; omega), by simp, by simp, ?_⟩
      have numbers : ∀ n : Fin 17, 1 ≤ n.val →
          scriptNum (n.val : Int) = ⟨#[UInt8.ofNat n.val]⟩ := by decide
      have repr : scriptNum ((data.get! 0).toNat : Int) = data := by
        rw [numbers ⟨(data.get! 0).toNat, by omega⟩ positive.1]
        simpa using (singleton_of_size_one data one).symm
      simp only [CoreRawInstruction.Encodes, encodesPush, high]
      rw [if_neg (by omega)]
      have numeric : (0x50 + (data.get! 0).toNat == 0x4f ||
          (0x51 ≤ 0x50 + (data.get! 0).toNat && 0x50 + (data.get! 0).toNat ≤ 0x60)) = true := by
        simp; omega
      rw [if_pos numeric]
      refine ⟨trivial, ?_⟩
      have value : rawNumber (0x50 + (data.get! 0).toNat) = (data.get! 0).toNat := by
        simp [rawNumber, show 0x50 + (data.get! 0).toNat ≠ 0x4f by omega]
        omega
      rw [value, repr]
    next notPositive =>
      split at serialized
      next negative =>
        simp only [pure, Except.pure, Except.ok.injEq] at serialized
        subst encoded
        refine ⟨_, read_opcode before after 0x4f (by decide), by simp, by simp, ?_⟩
        have dataEq : data = ⟨#[0x81]⟩ := by rw [singleton_of_size_one data one, negative]
        rw [dataEq]
        simp [CoreRawInstruction.Encodes, encodesPush, rawNumber]
        rfl
      next notNegative =>
        apply ordinary serialized
        simp [coreLegacyMinimalPush, one, notPositive, notNegative]
  next notOne =>
    apply ordinary serialized
    by_cases empty : data.size = 0 <;>
      simp [coreLegacyMinimalPush, notOne, empty, show data.size ≤ 75 by omega]

private theorem read_serializeElement (element : ScriptElement) (encoded : ByteArray)
    (small : element.pushSize < 76) (serialized : serializeElement element = .ok encoded)
    (before after : ByteArray) :
    ∃ instruction,
      readCoreRawInstruction (before ++ encoded ++ after) before.size = .ok instruction ∧
      instruction.nextOffset = before.size + encoded.size ∧ 0 < encoded.size ∧
      instruction.Encodes element := by
  cases element with
  | pushData data => exact read_serializePushData data encoded small serialized before after
  | pushNum number =>
      rw [serializeElement, serializePushNum_eq_serializePushData] at serialized
      exact read_serializePushData (scriptNum number) encoded small serialized before after
  | op opcode =>
      simp only [serializeElement, Except.ok.injEq] at serialized
      subst encoded
      refine ⟨_, read_opcode before after _ (by cases opcode <;> decide), by simp, by simp, ?_⟩
      exact ⟨rfl, rfl⟩
  | badOpcode opcode => simp [serializeElement] at serialized
  | illegalOpcode opcode => simp [serializeElement] at serialized
  | nonminimalPush push => simp [serializeElement] at serialized

/-- Canonical serialization supplies the byte-decoding certificate whenever
each pushed value fits in a direct push (at most 75 bytes). This covers the
keys, hashes and bounded integers emitted by validated Miniscript fragments.
The general execution theorem also accepts certificates for larger pushes. -/
theorem CoreTapscriptEncoding.of_serializeScript (script : Script) (bytes : ByteArray)
    (small : ∀ element ∈ script, element.pushSize < 76)
    (serialized : serializeScript script = .ok bytes) :
    CoreTapscriptEncoding bytes 0 script := by
  suffices ∀ before : ByteArray,
      CoreTapscriptEncoding (before ++ bytes) before.size script from by
    simpa using this ByteArray.empty
  induction script generalizing bytes with
  | nil =>
      simp only [serializeScript, Except.ok.injEq] at serialized
      subst bytes
      simp [CoreTapscriptEncoding]
  | cons element rest ih =>
      cases headEq : serializeElement element with
      | error error => simp [serializeScript, headEq, bind, Except.bind] at serialized
      | ok headBytes =>
          cases tailEq : serializeScript rest with
          | error error => simp [serializeScript, headEq, tailEq, bind, Except.bind] at serialized
          | ok tailBytes =>
              simp only [serializeScript, headEq, tailEq, bind, Except.bind,
                pure, Except.pure, Except.ok.injEq] at serialized
              subst bytes
              intro before
              obtain ⟨instruction, read, next, positive, encoded⟩ :=
                read_serializeElement element headBytes (small _ (by simp)) headEq before tailBytes
              simp only [CoreTapscriptEncoding, ← ByteArray.append_assoc, read]
              refine ⟨?_, ?_, encoded, ?_⟩
              · simp only [ByteArray.size_append]; omega
              · rw [next]; omega
              · rw [next]
                simpa using ih tailBytes (fun e member => small e (by simp [member])) tailEq
                  (before ++ headBytes)

/-- Successful canonical serialization discharges the decoding premise for
scripts with pushes of at most 75 bytes. Stack inputs, signature budgets and
cryptographic callbacks are unrestricted; exact execution errors are preserved. -/
theorem executeCoreScript_serializeScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (small : ∀ element ∈ script, element.pushSize < 76)
    (serialized : serializeScript script = .ok request.scriptBytes) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        script request.stack [] flags.script (coreTapscriptContext ctx request)
        request.validationWeight) :=
  executeCoreScript_eq_runtime flags ctx oracles request script version
    (CoreTapscriptEncoding.of_serializeScript script request.scriptBytes small serialized)

/-- Concrete Miniscript compilation followed by raw Tapscript execution has
the typed runtime's main stack or exact error, under the explicit push-size
and serialization premises. -/
theorem executeCoreScript_compileConcrete (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (fragment : Miniscript.CoreFragment)
    (version : request.sigVersion = .tapscript)
    (small : ∀ element ∈ Miniscript.compileConcrete fragment, element.pushSize < 76)
    (serialized : serializeScript (Miniscript.compileConcrete fragment) = .ok request.scriptBytes) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        (Miniscript.compileConcrete fragment) request.stack [] flags.script
        (coreTapscriptContext ctx request) request.validationWeight) :=
  executeCoreScript_serializeScript flags ctx oracles request _ version small serialized

end LeanMiniscript.Extraction
