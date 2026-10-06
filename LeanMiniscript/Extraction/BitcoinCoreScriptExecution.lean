import LeanMiniscript.Extraction.BitcoinCoreLegacyScript
import LeanMiniscript.Extraction.BitcoinCoreVerificationTypes
import LeanMiniscript.Bitcoin.SHA1
import LeanMiniscript.Bitcoin.ECDSA
import LeanMiniscript.Bitcoin.Schnorr
import LeanMiniscript.Extraction.CoreFixtureTransaction

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- One GetOp result, retaining the original byte boundary for signature hashing. -/
structure CoreRawInstruction where
  opcode : UInt8
  payload : ByteArray
  nextOffset : Nat
  deriving Repr

/-- Decode exactly one instruction. Truncated pushes fail when reached. -/
def readCoreRawInstruction (bytes : ByteArray) (offset : Nat) :
    Except ScriptError CoreRawInstruction := do
  if offset ≥ bytes.size then throw .badOpcode
  let opcode := bytes[offset]!
  let value := opcode.toNat
  if value > 0x4e then return ⟨opcode, ByteArray.empty, offset + 1⟩
  let width := if value ≤ 75 then 0 else if value == 0x4c then 1
    else if value == 0x4d then 2 else 4
  if offset + 1 + width > bytes.size then throw .badOpcode
  let size := if width == 0 then value else
    (List.range width).foldl (fun size i =>
      size + bytes[offset + 1 + i]!.toNat * 256 ^ i) 0
  let begin := offset + 1 + width
  if begin + size > bytes.size then throw .badOpcode
  return ⟨opcode, bytes.extract begin (begin + size), begin + size⟩

private def findAndDeleteLoop (bytes needle : ByteArray) :
    Nat → Nat → ByteArray → Nat → ByteArray × Nat
  | 0, offset, result, count => (result ++ bytes.extract offset bytes.size, count)
  | fuel + 1, offset, result, count =>
      if offset ≥ bytes.size then (result, count)
      else if offset + needle.size ≤ bytes.size &&
          bytes.extract offset (offset + needle.size) == needle then
        findAndDeleteLoop bytes needle fuel (offset + needle.size) result (count + 1)
      else match readCoreRawInstruction bytes offset with
      | .error _ => (result ++ bytes.extract offset bytes.size, count)
      | .ok instruction => findAndDeleteLoop bytes needle fuel instruction.nextOffset
          (result ++ bytes.extract offset instruction.nextOffset) count

/-- Core FindAndDelete matches complete byte strings only at opcode boundaries.
It preserves nonmatching pushes and undecodable suffix bytes exactly. -/
def coreFindAndDelete (bytes needle : ByteArray) : ByteArray × Nat :=
  if needle.size == 0 then (bytes, 0)
  else findAndDeleteLoop bytes needle (bytes.size + 1) 0 ByteArray.empty 0

/-- CScript's vector insertion uses a length prefix, including for 0x01..0x10. -/
def coreSignaturePush (signature : ByteArray) : ByteArray :=
  (serializeLengthPrefixedPush signature).toOption.getD ByteArray.empty

private def removeSignatures (bytes : ByteArray) (signatures : Stack) : ByteArray × Nat :=
  signatures.foldl (fun (scriptCode, count) signature =>
    let (next, removed) := coreFindAndDelete scriptCode (coreSignaturePush signature)
    (next, count + removed)) (bytes, 0)

private def disabledOpcode (opcode : Nat) : Bool :=
  [0x7e, 0x7f, 0x80, 0x81, 0x83, 0x84, 0x85, 0x86,
    0x8d, 0x8e, 0x95, 0x96, 0x97, 0x98, 0x99].contains opcode

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
  if disabledOpcode value then throw (.script .disabledOpcode)
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

private def fixtureSignatureOracle (fixture : CoreFixtureTransaction)
    (version : SignatureVersion) (scriptCode : ByteArray) : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun signature publicKey _ =>
      if signature.size == 0 then false
      else
        let hashType := UInt32.ofNat signature[signature.size - 1]!.toNat
        let digest := if version == .witnessV0 then
            Bitcoin.witnessV0SignatureHash fixture.spend fixture.inputIndex scriptCode
              fixture.amount hashType
          else Bitcoin.legacySignatureHash fixture.spend fixture.inputIndex scriptCode hashType
        match digest with
        | .error _ => false
        | .ok digest => Bitcoin.ECDSA.verify
            (signature.extract 0 (signature.size - 1)) publicKey digest)
    Bitcoin.Schnorr.verify

/-- Concrete fixture execution computes each reached signature's transaction
hash from its own hash-type byte and the retained original scriptCode. -/
def executeCoreFixtureScript (fixture : CoreFixtureTransaction)
    (flags : CoreVerificationFlags) : CoreScriptExecutor :=
  let ctx : TxContext := {
    version := fixture.spend.signedVersion
    locktime := fixture.spend.locktime.toNat
    sequence := (fixture.spend.inputs[fixture.inputIndex]!).sequence.toNat
    sigHash := ByteArray.empty
    taproot := some {
      transaction := fixture.spend
      spentOutputs := fixture.spentOutputs
      inputIndex := fixture.inputIndex } }
  executeCoreScript flags ctx (fixtureSignatureOracle fixture)

/-- Concrete BIP341 key-path verification shares the exact fixture transaction
and amount with script-path and witness-v0 execution. -/
def checkCoreFixtureKeyPath (fixture : CoreFixtureTransaction) : CoreKeyPathChecker :=
  fun signature publicKey annex => do
    (checkSchnorrSignatureEncoding signature).mapError .script
    let context : Bitcoin.TaprootSigHashContext := {
      transaction := fixture.spend
      spentOutputs := fixture.spentOutputs
      inputIndex := fixture.inputIndex
      annex := annex }
    let digest ← (Bitcoin.taprootSignatureHash context
      (if signature.size == 65 then signature[64]! else 0)).mapError
        (fun _ => CoreVerificationError.script .schnorrSigHashType)
    if Bitcoin.Schnorr.verify (signature.extract 0 64) publicKey digest then return ()
    else throw (.script .schnorrSig)

end LeanMiniscript.Extraction
