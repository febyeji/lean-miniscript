import LeanMiniscript.Extraction.BitcoinCoreRawScript
import LeanMiniscript.Extraction.BitcoinCoreLegacyScript
import LeanMiniscript.Extraction.BitcoinCoreVerificationTypes
import LeanMiniscript.Bitcoin.SHA1

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

private def removeSignatures (bytes : ByteArray) (signatures : Stack) : ByteArray × Nat :=
  signatures.foldl (fun (scriptCode, count) signature =>
    let (next, removed) := coreFindAndDelete scriptCode (coreSignaturePush signature)
    (next, count + removed)) (bytes, 0)

private structure CoreRawState where
  runtime : RuntimeState
  offset : Nat := 0
  opcodePosition : Nat := 0
  operationCount : Nat := 0
  codeSeparatorOffset : Nat := 0
  codeSeparatorPosition : UInt32 := 0xffffffff

private def instructionContext (ctx : TxContext) (request : CoreScriptExecutionRequest)
    (state : CoreRawState) : TxContext :=
  { ctx with
    sigVersion := request.sigVersion
    taproot := if request.sigVersion == .tapscript then ctx.taproot.map fun taproot =>
      { taproot with
        annex := request.annex
        spendPath := .scriptPath request.scriptBytes request.leafVersion state.codeSeparatorPosition }
      else none }

private def instructionSignatures (opcode : Opcode) (state : RuntimeState)
    (flags : ScriptFlags) : Stack :=
  match opcode with
  | .OP_CHECKSIG | .OP_CHECKSIGVERIFY =>
      match state.stack with
      | _ :: sig :: _ => [sig]
      | _ => []
  | .OP_CHECKMULTISIG | .OP_CHECKMULTISIGVERIFY =>
      match decodeCheckMultiSigOperands flags state.stack with
      | .ok operands => operands.signatures
      | .error _ => []
  | _ => []

private def coreRawStep (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracleForScript : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction) : Except CoreVerificationError CoreRawState := do
  if instruction.payload.size > maxScriptElementSize then throw (.script .pushSize)
  let value := instruction.opcode.toNat
  let active := state.runtime.conditions.all id
  let mut count := state.operationCount
  if request.sigVersion != .tapscript && value > 0x60 then
    count := count + 1
    if count > 201 then throw (.script .opCount)
  if coreLegacyDisabledOpcode value then throw (.script .disabledOpcode)
  if value == 0x65 || value == 0x66 then throw (.script .badOpcode)
  if value == 0xab && request.sigVersion == .base && flags.constScriptCode then
    throw .opCodeSeparator
  let mut next := { state with
    offset := instruction.nextOffset
    opcodePosition := state.opcodePosition + 1
    operationCount := count }
  let ctx := instructionContext ctx request state
  let scriptCode := request.scriptBytes.extract state.codeSeparatorOffset request.scriptBytes.size
  let fallbackOracle := oracleForScript request.sigVersion scriptCode
  if value ≤ 0x4e then
    if active && flags.script.minimalData && !coreLegacyMinimalPush value instruction.payload then
      throw (.script .minimalData)
    let runtime ← (runtimeStep fallbackOracle (.pushData instruction.payload)
      state.runtime flags.script ctx).mapError .script
    return { next with runtime := runtime }
  else if value == 0x4f || (0x51 ≤ value && value ≤ 0x60) then
    let number : Int := if value == 0x4f then -1 else value - 0x50
    let runtime ← (runtimeStep fallbackOracle (.pushNum number)
      state.runtime flags.script ctx).mapError .script
    return { next with runtime := runtime }
  else if value == 0xa7 then
    let runtime ← (if active then
        match state.runtime.stack with
        | [] => .error .stackUnderflow
        | top :: rest => checkRuntimeStack
            { state.runtime with stack := Bitcoin.SHA1.hash top :: rest }
      else checkRuntimeStack state.runtime).mapError CoreVerificationError.script
    return { next with runtime := runtime }
  else if value == 0xab then
    if active then
      next := { next with
        codeSeparatorOffset := instruction.nextOffset
        codeSeparatorPosition := UInt32.ofNat state.opcodePosition }
    let runtime ← (checkRuntimeStack state.runtime).mapError .script
    return { next with runtime := runtime }
  else
    match opcodeFromByte? value with
    | none =>
        if active then throw (.script .badOpcode)
        let runtime ← (checkRuntimeStack state.runtime).mapError .script
        return { next with runtime := runtime }
    | some opcode =>
        if request.sigVersion != .tapscript then
          -- This also charges active multisig key counts before the remaining operands.
          let total ← (coreLegacyNextCount (.modeled (.op opcode)) state.runtime
            flags.script state.operationCount).mapError .script
          next := { next with operationCount := total }
        let opcode := if (opcode == .OP_CHECKLOCKTIMEVERIFY && !flags.checkLockTimeVerify) ||
            (opcode == .OP_CHECKSEQUENCEVERIFY && !flags.checkSequenceVerify) then .OP_NOP else opcode
        let signatures := if active && request.sigVersion == .base then
            instructionSignatures opcode state.runtime flags.script else []
        let (scriptCode, removed) := removeSignatures scriptCode signatures
        if removed > 0 && flags.constScriptCode then throw .sigFindAndDelete
        let oracle := oracleForScript request.sigVersion scriptCode
        let runtime ← (runtimeStep oracle (.op opcode) state.runtime flags.script ctx).mapError .script
        return { next with runtime := runtime }

private def executeCoreRawLoop (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracleForScript : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) : Nat → CoreRawState → Except CoreVerificationError Stack
  | 0, _ => .error (.unsupported "raw script decoder fuel exhausted")
  | fuel + 1, state =>
      if state.offset ≥ request.scriptBytes.size then
        if state.runtime.conditions.isEmpty then .ok state.runtime.stack
        else .error (.script .unbalancedConditional)
      else do
        let instruction ← (readCoreRawInstruction request.scriptBytes state.offset).mapError .script
        let next ← coreRawStep flags ctx oracleForScript request state instruction
        executeCoreRawLoop flags ctx oracleForScript request fuel next

/-- Execute original bytes under the requested signature version. The witness
boundary performs Tapscript OP_SUCCESS scanning and initial witness limits.
BASE and witness-v0 retain script-size and operation-count limits. -/
def executeCoreScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracleForScript : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) : Except CoreVerificationError Stack :=
  if request.sigVersion != .tapscript && request.scriptBytes.size > 10000 then
    .error (.script .scriptSize)
  else executeCoreRawLoop flags ctx oracleForScript request (request.scriptBytes.size + 1)
    { runtime := { stack := request.stack, altStack := [], weight := request.validationWeight } }

end LeanMiniscript.Extraction
