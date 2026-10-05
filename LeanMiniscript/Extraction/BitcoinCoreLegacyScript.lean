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
  | scriptSize (size : Nat)
  | opcodeCount (count : Nat)
  deriving Repr, DecidableEq

/-- One source instruction with original push minimality or a legacy failure.
A malformed push terminates decoding with a failure marker; earlier execution
can therefore fail before that marker is reached. -/
inductive CoreLegacyInstruction where
  | modeled (element : ScriptElement) (minimalPush : Bool := true)
  | failure (error : ScriptError) (activeOnly : Bool) (counted : Bool)
  deriving Repr

/-- Decoded legacy instructions after script-size and opcode-count admission. -/
structure CoreLegacyProgram where
  instructions : List CoreLegacyInstruction
  deriving Repr

private def legacyDisabledByte (byte : Nat) : Bool :=
  [0x7e, 0x7f, 0x80, 0x81, 0x83, 0x84, 0x85, 0x86,
    0x8d, 0x8e, 0x95, 0x96, 0x97, 0x98, 0x99].contains byte

private def legacyReservedByte (byte : Nat) : Bool :=
  [0x50, 0x62, 0x89, 0x8a].contains byte

private def legacySignatureOpcode : Opcode → Bool
  | .OP_CHECKSIG | .OP_CHECKSIGVERIFY | .OP_CHECKSIGADD |
      .OP_CHECKMULTISIG | .OP_CHECKMULTISIGVERIFY => true
  | _ => false

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
            if legacySignatureOpcode opcode then throw .signatureOpcode
            return .modeled (.op opcode) :: (← decodeCoreLegacyList rest (offset + 1))
        | none => throw (.opcode offset byte)
termination_by bytes.length
decreasing_by
  all_goals simp_wf <;> omega

private def CoreLegacyInstruction.opcodeCount : CoreLegacyInstruction → Nat
  | .modeled (.op opcode) _ => if (opcodeByte opcode).toNat > 0x60 then 1 else 0
  | .modeled _ _ => 0
  | .failure _ _ counted => if counted then 1 else 0

/-- Admit bounded, signature-free legacy bytecode. Resource conditions whose
Core errors are not represented here remain explicit unsupported cases. -/
def decodeCoreLegacyScript (bytes : ByteArray) :
    Except CoreLegacyUnsupported CoreLegacyProgram := do
  if bytes.size > 10000 then throw (.scriptSize bytes.size)
  let instructions ← decodeCoreLegacyList bytes.data.toList 0
  let count := instructions.foldl (fun count instruction => count + instruction.opcodeCount) 0
  if count > 201 then throw (.opcodeCount count)
  return ⟨instructions⟩

/-- The raw fixture preparer rejects nonminimal pushes whenever MINIMALDATA is
requested, including pushes in inactive code, matching its conservative AST
admission rule. Execution is reached only after this preparation check. -/
def CoreLegacyProgram.hasNonMinimalPush (program : CoreLegacyProgram) : Bool :=
  program.instructions.any fun
    | .modeled _ minimal => !minimal
    | .failure _ _ _ => false

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
size. Modeled instructions retain the shared runtime's error order. -/
def coreLegacyStep (oracle : CryptoOracle) (instruction : CoreLegacyInstruction)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState :=
  match instruction with
  | .modeled element _ => runtimeStep oracle element state flags { ctx with sigVersion := .base }
  | .failure error activeOnly _ =>
      if !activeOnly || state.conditions.all id then .error error
      else checkRuntimeStack state

/-- Execute prepared instructions in source order under the BASE signature
version. The fixture preparer separately enforces retained push minimality. -/
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

/-- Each scriptSig/scriptPubKey execution starts with an empty alternate and
condition stack, preserving only the main stack across the two boundaries. -/
def runCoreLegacyScript (oracle : CryptoOracle) (program : CoreLegacyProgram)
    (stack : Stack) (flags : ScriptFlags) (ctx : TxContext) : Except ScriptError Stack := do
  let result ← evaluateCoreLegacy oracle program.instructions
    { stack := stack, altStack := [], conditions := [], weight := 0 } flags ctx
  return result.stack

end LeanMiniscript.Extraction
