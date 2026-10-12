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
Length-prefixed pushes must be minimal so MINIMALDATA is preserved as well. -/
def CoreRawInstruction.Encodes (instruction : CoreRawInstruction) : ScriptElement → Prop
  | .pushData data => encodesPush instruction data
  | .pushNum number => encodesPush instruction (scriptNum number)
  | .op opcode => instruction.opcode = opcodeByte opcode ∧
      instruction.payload = ByteArray.empty

instance (instruction : CoreRawInstruction) (element : ScriptElement) :
    Decidable (instruction.Encodes element) := by
  cases element <;> unfold CoreRawInstruction.Encodes encodesPush <;> infer_instance

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
  simp [runtimeStep, executeRuntimeElement, ScriptElement.pushSize,
    prepareValidationWeight, evaluate.eq_1, evaluate.eq_2, evaluate.eq_3]

set_option maxHeartbeats 2000000 in
private theorem coreRawStep_tapscript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) (element : ScriptElement)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
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
  | op opcode =>
      obtain ⟨byte, payload⟩ := encoded
      cases opcode <;>
        simp +decide [coreRawStep, byte, payload, version, locktime, sequence, context, code,
          opcodeByte, opcodeFromByte?, coreLegacyDisabledOpcode, maxScriptElementSize,
          removeSignatures, bind, Except.bind, Except.mapError, Except.map,
          pure, Except.pure]
      all_goals split <;> rfl
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
        · simp +decide [coreRawStep, payload, large, runtimeStep,
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
        (.pushData (scriptNum number)) version locktime sequence separatorOffset separatorPosition encoded
termination_by match element with | .pushNum _ => 1 | _ => 0

/-- The Core executor exposes the main stack or Script error. The runtime
also retains the alternate stack and remaining signature budget. -/
def coreRuntimeResult : WeightedResult → Except CoreVerificationError Stack
  | .success stack _ _ => .ok stack
  | .failure error => .error (.script error)

private theorem CoreTapscriptEncoding.length_bound {bytes : ByteArray}
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
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
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
                version locktime sequence separatorOffset separatorPosition encoded.2.2.1]
              cases stepped : runtimeStep (oracles .tapscript request.scriptBytes) element
                  state.runtime flags.script (coreTapscriptContext ctx request) with
              | error error =>
                  simp [Except.mapError, Except.map, evaluateRuntime, stepped, coreRuntimeResult]
              | ok next =>
                  simp only [Except.mapError, Except.map, evaluateRuntime, stepped]
                  exact ih _ fuel (by simpa using enough) separatorOffset separatorPosition encoded.2.2.2

/-- Original-byte Tapscript execution and the typed runtime have the same
main-stack result and exact Script error for every input stack and oracle.
The byte-only certificate excludes CODESEPARATOR and nonminimal pushes;
both timelock opcodes must be enabled, as in the typed evaluator. Witness
commitments, OP_SUCCESS scanning and initial witness limits are caller checks. -/
theorem executeCoreScript_eq_runtime (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        script request.stack [] flags.script (coreTapscriptContext ctx request)
        request.validationWeight) := by
  have bound := encoded.length_bound
  simp only [executeCoreScript, version, show (SignatureVersion.tapscript != .tapscript) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, evaluateWithRuntimeLimits]
  exact executeCoreRawLoop_tapscript flags ctx oracles request version locktime sequence
    script _ _ (by omega) rfl rfl encoded

/-- Under the existing cryptographic refinement assumption, every successful
raw execution has the same main stack in the relational Script semantics. -/
theorem executeCoreScript_eval_success (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script)
    (agreement : (oracles .tapscript request.scriptBytes).RefinesModel)
    (stack : Stack) (success : executeCoreScript flags ctx oracles request = .ok stack) :
    ∃ alt, Eval script request.stack [] flags.script (coreTapscriptContext ctx request)
      (.success stack alt) := by
  rw [executeCoreScript_eq_runtime flags ctx oracles request script version locktime sequence encoded]
    at success
  cases evaluated : evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
      script request.stack [] flags.script (coreTapscriptContext ctx request)
      request.validationWeight with
  | failure error => simp [evaluated, coreRuntimeResult] at success
  | success result alt weight =>
      simp only [evaluated, coreRuntimeResult, Except.ok.injEq] at success
      subst result
      exact ⟨alt, evaluateWithRuntimeLimits_eval_success agreement evaluated⟩

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
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (small : ∀ element ∈ script, element.pushSize < 76)
    (serialized : serializeScript script = .ok request.scriptBytes) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        script request.stack [] flags.script (coreTapscriptContext ctx request)
        request.validationWeight) :=
  executeCoreScript_eq_runtime flags ctx oracles request script version locktime sequence
    (CoreTapscriptEncoding.of_serializeScript script request.scriptBytes small serialized)

/-- Concrete Miniscript compilation followed by raw Tapscript execution has
the typed runtime's main stack or exact error, under the explicit push-size,
serialization and timelock-activation premises. -/
theorem executeCoreScript_compileConcrete (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (fragment : Miniscript.CoreFragment)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (small : ∀ element ∈ Miniscript.compileConcrete fragment, element.pushSize < 76)
    (serialized : serializeScript (Miniscript.compileConcrete fragment) = .ok request.scriptBytes) :
    executeCoreScript flags ctx oracles request =
      coreRuntimeResult (evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
        (Miniscript.compileConcrete fragment) request.stack [] flags.script
        (coreTapscriptContext ctx request) request.validationWeight) :=
  executeCoreScript_serializeScript flags ctx oracles request _ version locktime sequence small serialized

end LeanMiniscript.Extraction
