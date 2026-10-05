import LeanMiniscript.Script.Codec.Deserialization
import LeanMiniscript.Script.RuntimeLimits

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-!
Legacy fixture byte interpretation preserves parse and execution failures in
source order. Disabled, reserved and invalid bytes remain outside the shared
Script opcode type: several of these bytes have OP_SUCCESS semantics in
Tapscript, which this fixture boundary does not model.
-/

/-- Conditions excluded from the raw legacy fixture execution boundary. -/
inductive CoreLegacyUnsupported where
  | opcode (offset : Nat) (byte : UInt8)
  | signatureOpcode
  deriving Repr, DecidableEq

/-- One source instruction with original push minimality or a legacy failure.
A malformed push terminates decoding with a failure marker; earlier execution
can therefore fail before that marker is reached. -/
inductive CoreLegacyInstruction where
  | modeled (element : ScriptElement) (minimalPush : Bool := true)
  | failure (error : ScriptError) (activeOnly : Bool) (counted : Bool)
  deriving Repr

/-- Decoded legacy instructions with the original byte length. -/
structure CoreLegacyProgram where
  instructions : List CoreLegacyInstruction
  byteSize : Nat := 0
  deriving Repr

private def legacyDisabledByte (byte : Nat) : Bool :=
  [0x7e, 0x7f, 0x80, 0x81, 0x83, 0x84, 0x85, 0x86,
    0x8d, 0x8e, 0x95, 0x96, 0x97, 0x98, 0x99].contains byte

private def legacyReservedByte (byte : Nat) : Bool :=
  [0x50, 0x62, 0x89, 0x8a].contains byte

/-- Exact minimal-push rule for the retained original opcode and payload. -/
def coreLegacyMinimalPush (opcode : Nat) (data : ByteArray) : Bool :=
  if data.size = 0 then opcode == 0
  else if data.size = 1 && 1 ≤ (data.get! 0).toNat && (data.get! 0).toNat ≤ 16 then
    opcode == (data.get! 0).toNat + 0x50
  else if data.size = 1 && data.get! 0 == 0x81 then opcode == 0x4f
  else if data.size ≤ 75 then opcode == data.size
  else if data.size ≤ 255 then opcode == 0x4c
  else if data.size ≤ 65535 then opcode == 0x4d
  else true

private def malformedLegacyPush : List CoreLegacyInstruction :=
  [.failure .badOpcode false false]

/-- Decode source instructions without promoting legacy-only bytes into Script.
Unmodeled valid operations such as SHA1 and CODESEPARATOR are unsupported. -/
def decodeCoreLegacyList (bytes : List UInt8) (offset : Nat) :
    Except CoreLegacyUnsupported (List CoreLegacyInstruction) :=
  match bytes with
  | [] => .ok []
  | byte :: rest => do
      let value := byte.toNat
      if value = 0 then
        return .modeled (.pushNum 0) :: (← decodeCoreLegacyList rest (offset + 1))
      else if value ≤ 75 then
        if valid : value ≤ rest.length then
          let data : ByteArray := ⟨(rest.take value).toArray⟩
          return .modeled (.pushData data) (coreLegacyMinimalPush value data) ::
            (← decodeCoreLegacyList (rest.drop value) (offset + 1 + value))
        else return malformedLegacyPush
      else if value = 0x4c then
        match rest with
        | [] => return malformedLegacyPush
        | sizeByte :: payload =>
            let size := sizeByte.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              return .modeled (.pushData data) (coreLegacyMinimalPush value data) ::
                (← decodeCoreLegacyList (payload.drop size) (offset + 2 + size))
            else return malformedLegacyPush
      else if value = 0x4d then
        match rest with
        | low :: high :: payload =>
            let size := low.toNat + 256 * high.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              return .modeled (.pushData data) (coreLegacyMinimalPush value data) ::
                (← decodeCoreLegacyList (payload.drop size) (offset + 3 + size))
            else return malformedLegacyPush
        | _ => return malformedLegacyPush
      else if value = 0x4e then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: payload =>
            let size := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
              16777216 * b3.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              return .modeled (.pushData data) (coreLegacyMinimalPush value data) ::
                (← decodeCoreLegacyList (payload.drop size) (offset + 5 + size))
            else return malformedLegacyPush
        | _ => return malformedLegacyPush
      else if value = 0x4f then
        return .modeled (.pushNum (-1)) :: (← decodeCoreLegacyList rest (offset + 1))
      else if 0x51 ≤ value ∧ value ≤ 0x60 then
        return .modeled (.pushNum (value - 0x50)) ::
          (← decodeCoreLegacyList rest (offset + 1))
      else if legacyDisabledByte value then
        return .failure .disabledOpcode false true ::
          (← decodeCoreLegacyList rest (offset + 1))
      else if value = 0x65 ∨ value = 0x66 then
        return .failure .badOpcode false true ::
          (← decodeCoreLegacyList rest (offset + 1))
      else if legacyReservedByte value || value ≥ 0xba then
        return .failure .badOpcode true (value > 0x60) ::
          (← decodeCoreLegacyList rest (offset + 1))
      else
        match opcodeFromByte? value with
        | some opcode =>
            return .modeled (.op opcode) :: (← decodeCoreLegacyList rest (offset + 1))
        | none => throw (.opcode offset byte)
termination_by bytes.length
decreasing_by
  all_goals simp_wf <;> omega

def CoreLegacyInstruction.opcodeCount : CoreLegacyInstruction → Nat
  | .modeled (.op opcode) _ => if (opcodeByte opcode).toNat > 0x60 then 1 else 0
  | .modeled _ _ => 0
  | .failure _ _ counted => if counted then 1 else 0

/-- Decode supported legacy instructions and preserve the exact serialized size.
Script-size and opcode-count failures belong to execution, not admission. -/
def decodeCoreLegacyScript (bytes : ByteArray) :
    Except CoreLegacyUnsupported CoreLegacyProgram := do
  if bytes.size > 10000 then return ⟨[], bytes.size⟩
  let instructions ← decodeCoreLegacyList bytes.data.toList 0
  return ⟨instructions, bytes.size⟩

/-- Identify a modeled opcode retained in a prepared raw program. -/
def CoreLegacyProgram.containsOpcode (program : CoreLegacyProgram) (wanted : Opcode) : Bool :=
  program.instructions.any fun
    | .modeled (.op opcode) _ => opcode == wanted
    | _ => false

/-- Recognize the exact P2SH script pattern before allowing legacy execution. -/
def CoreLegacyProgram.isP2SH (program : CoreLegacyProgram) : Bool :=
  match program.instructions with
  | [.modeled (.op .OP_HASH160) _, .modeled (.pushData hash) true,
      .modeled (.op .OP_EQUAL) _] => hash.size == 20
  | _ => false

/-- One instruction in the legacy-only fixture path. Unconditional errors are
visited even in inactive branches; skipped reserved bytes still check stack
size. Original push minimality is enforced only in active code, after the
unconditional push-size check and before the post-instruction stack check. -/
def coreLegacyStep (oracle : CryptoOracle) (instruction : CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState :=
  match instruction with
  | .modeled (.pushData data) minimal =>
      if data.size > maxScriptElementSize then .error .pushSize
      else if state.conditions.all id && flags.minimalData && !minimal then .error .minimalData
      else runtimeStep oracle (.pushData data) state flags { ctx with sigVersion := .base }
  | .modeled element _ => runtimeStep oracle element state flags { ctx with sigVersion := .base }
  | .failure error activeOnly _ =>
      if !activeOnly || state.conditions.all id then .error error
      else checkRuntimeStack state

/-- Oversized retained pushes fail before the minimality or branch checks. -/
theorem coreLegacyStep_pushSize (oracle : CryptoOracle) (data : ByteArray)
    (minimal : Bool) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (oversized : data.size > maxScriptElementSize) :
    coreLegacyStep oracle (.modeled (.pushData data) minimal) state flags ctx =
      .error .pushSize := by
  simp [coreLegacyStep, oversized]

/-- A bounded, active, nonminimal push fails before execution and stack growth. -/
theorem coreLegacyStep_nonMinimalPush (oracle : CryptoOracle) (data : ByteArray)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (bounded : data.size ≤ maxScriptElementSize)
    (active : state.conditions.all id = true) (enforced : flags.minimalData = true) :
    coreLegacyStep oracle (.modeled (.pushData data) false) state flags ctx =
      .error .minimalData := by
  simp [coreLegacyStep, Nat.not_lt.mpr bounded, active, enforced]

/-- Inactive bounded pushes retain the shared runtime's branch and stack checks. -/
theorem coreLegacyStep_inactivePush (oracle : CryptoOracle) (data : ByteArray)
    (minimal : Bool) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (bounded : data.size ≤ maxScriptElementSize)
    (inactive : state.conditions.all id = false) :
    coreLegacyStep oracle (.modeled (.pushData data) minimal) state flags ctx =
      runtimeStep oracle (.pushData data) state flags { ctx with sigVersion := .base } := by
  simp [coreLegacyStep, Nat.not_lt.mpr bounded, inactive]

/-- Disabling MINIMALDATA leaves bounded pushes to the shared runtime. -/
theorem coreLegacyStep_minimalDataDisabled (oracle : CryptoOracle) (data : ByteArray)
    (minimal : Bool) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (bounded : data.size ≤ maxScriptElementSize) (disabled : flags.minimalData = false) :
    coreLegacyStep oracle (.modeled (.pushData data) minimal) state flags ctx =
      runtimeStep oracle (.pushData data) state flags { ctx with sigVersion := .base } := by
  simp [coreLegacyStep, Nat.not_lt.mpr bounded, disabled]

/-- A minimal encoding reaches the shared runtime regardless of MINIMALDATA. -/
theorem coreLegacyStep_minimalPush (oracle : CryptoOracle) (data : ByteArray)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (bounded : data.size ≤ maxScriptElementSize) :
    coreLegacyStep oracle (.modeled (.pushData data) true) state flags ctx =
      runtimeStep oracle (.pushData data) state flags { ctx with sigVersion := .base } := by
  simp [coreLegacyStep, Nat.not_lt.mpr bounded]

/-- Execute prepared instructions in source order under the BASE signature
version, retaining branch-sensitive original push minimality. -/
def evaluateCoreLegacy (oracle : CryptoOracle) : List CoreLegacyInstruction → RuntimeState →
    ScriptFlags → TxContext → Except ScriptError RuntimeState
  | [], state, _, _ =>
      if state.conditions.isEmpty then .ok state else .error .unbalancedConditional
  | instruction :: rest, state, flags, ctx => do
      let next ← coreLegacyStep oracle instruction state flags ctx
      evaluateCoreLegacy oracle rest next flags ctx

/-- A reached unconditional legacy failure terminates before the suffix. -/
theorem evaluateCoreLegacy_unconditionalFailure (oracle : CryptoOracle)
    (error : ScriptError) (counted : Bool) (rest : List CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    evaluateCoreLegacy oracle (.failure error false counted :: rest) state flags ctx =
      .error error := by
  simp [evaluateCoreLegacy, coreLegacyStep, bind, Except.bind]

/-- A reached active-only failure terminates when its branch executes. -/
theorem evaluateCoreLegacy_activeFailure (oracle : CryptoOracle)
    (error : ScriptError) (counted : Bool) (rest : List CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (active : state.conditions.all id = true) :
    evaluateCoreLegacy oracle (.failure error true counted :: rest) state flags ctx =
      .error error := by
  simp [evaluateCoreLegacy, coreLegacyStep, active, bind, Except.bind]

/-- Skipping a reserved or invalid byte retains the shared stack-size check. -/
theorem coreLegacyStep_inactiveFailure (oracle : CryptoOracle)
    (error : ScriptError) (counted : Bool) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext)
    (inactive : state.conditions.all id = false) :
    coreLegacyStep oracle (.failure error true counted) state flags ctx =
      checkRuntimeStack state := by
  simp [coreLegacyStep, inactive]

/-- The BASE limits count every opcode above OP_16, including inactive code.
An active multisig adds its decoded public-key count before the remaining
operands are checked. Malformed pushes and oversized elements precede counting. -/
def coreLegacyNextCount (instruction : CoreLegacyInstruction) (state : RuntimeState)
    (flags : ScriptFlags) (count : Nat) : Except ScriptError Nat := do
  match instruction with
  | .modeled element _ =>
      if element.pushSize > maxScriptElementSize then throw .pushSize
  | .failure .badOpcode false false => throw .badOpcode
  | _ => pure ()
  let next := count + instruction.opcodeCount
  if next > 201 then throw .opCount
  match instruction with
  | .modeled (.op .OP_CHECKMULTISIG) _ | .modeled (.op .OP_CHECKMULTISIGVERIFY) _ =>
      if state.conditions.all id then
        let keyBytes ← match state.stack with
          | [] => throw .stackUnderflow
          | top :: _ => pure top
        let keys ← decodeScriptNum keyBytes flags.minimalData maxArithmeticScriptNumBytes
        if keys < 0 ∨ (maxPubKeysPerMultiSig : Int) < keys then throw .pubkeyCount
        let total := next + keys.toNat
        if total > 201 then throw .opCount
        return total
      else return next
  | _ => return next

/-- Source-order BASE execution with the per-script operation counter. -/
def evaluateCoreLegacyWithLimits (oracle : CryptoOracle) :
    List CoreLegacyInstruction → RuntimeState → ScriptFlags → TxContext → Nat →
      Except ScriptError RuntimeState
  | [], state, _, _, _ =>
      if state.conditions.isEmpty then .ok state else .error .unbalancedConditional
  | instruction :: rest, state, flags, ctx, count => do
      let nextCount ← coreLegacyNextCount instruction state flags count
      let next ← coreLegacyStep oracle instruction state flags ctx
      evaluateCoreLegacyWithLimits oracle rest next flags ctx nextCount

/-- Whether an active signature instruction reaches a cryptographic callback.
Operand and first-pair encoding failures, and zero-signature multisig, are
independent of that callback. Inactive instructions never call it. -/
def coreLegacyNeedsVerifier (instruction : CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) : Bool :=
  if !state.conditions.all id then false
  else match instruction with
  | .modeled (.op .OP_CHECKSIG) _ | .modeled (.op .OP_CHECKSIGVERIFY) _ =>
      match state.stack with
      | pubkey :: sig :: _ => (checkECDSAEncoding flags sig pubkey).isOk
      | _ => false
  | .modeled (.op .OP_CHECKMULTISIG) _ | .modeled (.op .OP_CHECKMULTISIGVERIFY) _ =>
      match decodeCheckMultiSigOperands flags state.stack with
      | .error _ => false
      | .ok operands =>
          match operands.signatures, operands.pubkeys with
          | sig :: _, pubkey :: _ => (checkECDSAEncoding flags sig pubkey).isOk
          | _, _ => false
  | _ => false

/-- Admission follows the same resource checks and stops at the first reached
verifier call. The supplied oracle supplies only hashes on admitted paths. -/
def evaluateCoreLegacyWithoutVerifier (oracle : CryptoOracle) :
    List CoreLegacyInstruction → RuntimeState → ScriptFlags → TxContext → Nat →
      Except CoreLegacyUnsupported (Except ScriptError RuntimeState)
  | [], state, _, _, _ =>
      .ok (if state.conditions.isEmpty then .ok state else .error .unbalancedConditional)
  | instruction :: rest, state, flags, ctx, count =>
      match coreLegacyNextCount instruction state flags count with
      | .error error => .ok (.error error)
      | .ok nextCount =>
          if coreLegacyNeedsVerifier instruction state flags then .error .signatureOpcode
          else match coreLegacyStep oracle instruction state flags ctx with
          | .error error => .ok (.error error)
          | .ok next => evaluateCoreLegacyWithoutVerifier oracle rest next flags ctx nextCount

/-- Each scriptSig/scriptPubKey starts with empty alternate and condition
stacks and a fresh operation counter. Only the main stack crosses the boundary.
The original script-size check precedes every instruction. -/
def runCoreLegacyScript (oracle : CryptoOracle) (program : CoreLegacyProgram)
    (stack : Stack) (flags : ScriptFlags) (ctx : TxContext) : Except ScriptError Stack := do
  if program.byteSize > 10000 then throw .scriptSize
  let result ← evaluateCoreLegacyWithLimits oracle program.instructions
    { stack := stack, altStack := [], conditions := [], weight := 0 } flags ctx 0
  return result.stack

/-- Run the same script boundary while admitting only verifier-independent paths. -/
def checkCoreLegacyWithoutVerifier (oracle : CryptoOracle) (program : CoreLegacyProgram)
    (stack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    Except CoreLegacyUnsupported (Except ScriptError Stack) :=
  if program.byteSize > 10000 then .ok (.error .scriptSize)
  else (evaluateCoreLegacyWithoutVerifier oracle program.instructions
    { stack := stack, altStack := [], conditions := [], weight := 0 } flags ctx 0).map
      (fun result => result.map (·.stack))

end LeanMiniscript.Extraction
