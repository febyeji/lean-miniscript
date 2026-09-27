import LeanMiniscript.Script.Codec.Serialization

namespace LeanMiniscript.Script

/-!
# Bitcoin Script deserialization

This module decodes serialized Script bytes into the opcode subset represented
by `Script`. Push encodings are accepted independently of minimality; callers
which enforce policy rules retain the original bytes for that separate check.
-/

/-- A malformed push encoding or an opcode outside the modeled Script subset. -/
inductive DeserializationError where
  | truncatedPushLength (offset width remaining : Nat)
  | truncatedPushData (offset expected remaining : Nat)
  | unsupportedOpcode (offset : Nat) (byte : UInt8)
  deriving Repr, DecidableEq

/-- Inverse lookup for the byte values assigned by `opcodeByte`. -/
def opcodeFromByte? : Nat → Option Opcode
  | 0x61 => some .OP_NOP
  | 0x63 => some .OP_IF
  | 0x64 => some .OP_NOTIF
  | 0x67 => some .OP_ELSE
  | 0x68 => some .OP_ENDIF
  | 0x73 => some .OP_IFDUP
  | 0x75 => some .OP_DROP
  | 0x76 => some .OP_DUP
  | 0x7c => some .OP_SWAP
  | 0x6b => some .OP_TOALTSTACK
  | 0x6c => some .OP_FROMALTSTACK
  | 0x93 => some .OP_ADD
  | 0x9a => some .OP_BOOLAND
  | 0x9b => some .OP_BOOLOR
  | 0x92 => some .OP_0NOTEQUAL
  | 0x87 => some .OP_EQUAL
  | 0x88 => some .OP_EQUALVERIFY
  | 0x9c => some .OP_NUMEQUAL
  | 0x9d => some .OP_NUMEQUALVERIFY
  | 0xa8 => some .OP_SHA256
  | 0xaa => some .OP_HASH256
  | 0xa6 => some .OP_RIPEMD160
  | 0xa9 => some .OP_HASH160
  | 0xac => some .OP_CHECKSIG
  | 0xad => some .OP_CHECKSIGVERIFY
  | 0xba => some .OP_CHECKSIGADD
  | 0xae => some .OP_CHECKMULTISIG
  | 0xaf => some .OP_CHECKMULTISIGVERIFY
  | 0xb2 => some .OP_CHECKSEQUENCEVERIFY
  | 0xb1 => some .OP_CHECKLOCKTIMEVERIFY
  | 0x69 => some .OP_VERIFY
  | 0x82 => some .OP_SIZE
  | _ => none

/-- Decode a byte list at the supplied source offset. Recursive calls consume
    at least the leading opcode or push-length byte, so termination follows
    from the remaining byte count without a trusted fuel parameter. -/
def deserializeScriptList (bytes : List UInt8) (offset : Nat) :
    Except DeserializationError Script :=
  match bytes with
  | [] => .ok []
  | byte :: rest => do
      let value := byte.toNat
      if value = 0 then
        return .pushNum 0 ::
          (← deserializeScriptList rest (offset + 1))
      else if value ≤ 75 then
        if valid : value ≤ rest.length then
          let data : ByteArray := ⟨(rest.take value).toArray⟩
          let tail := rest.drop value
          return .pushData data ::
            (← deserializeScriptList tail (offset + 1 + value))
        else
          throw (.truncatedPushData offset value rest.length)
      else if value = 0x4c then
        match rest with
        | [] => throw (.truncatedPushLength offset 1 0)
        | sizeByte :: payload =>
            let size := sizeByte.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              let tail := payload.drop size
              return .pushData data ::
                (← deserializeScriptList tail (offset + 2 + size))
            else throw (.truncatedPushData offset size payload.length)
      else if value = 0x4d then
        match rest with
        | low :: high :: payload =>
            let size := low.toNat + 256 * high.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              let tail := payload.drop size
              return .pushData data ::
                (← deserializeScriptList tail (offset + 3 + size))
            else throw (.truncatedPushData offset size payload.length)
        | _ => throw (.truncatedPushLength offset 2 rest.length)
      else if value = 0x4e then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: payload =>
            let size := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
              16777216 * b3.toNat
            if valid : size ≤ payload.length then
              let data : ByteArray := ⟨(payload.take size).toArray⟩
              let tail := payload.drop size
              return .pushData data ::
                (← deserializeScriptList tail (offset + 5 + size))
            else throw (.truncatedPushData offset size payload.length)
        | _ => throw (.truncatedPushLength offset 4 rest.length)
      else if value = 0x4f then
        return .pushNum (-1) ::
          (← deserializeScriptList rest (offset + 1))
      else if 0x51 ≤ value ∧ value ≤ 0x60 then
        return .pushNum (value - 0x50) ::
          (← deserializeScriptList rest (offset + 1))
      else
        match opcodeFromByte? value with
        | some opcode =>
            return .op opcode ::
              (← deserializeScriptList rest (offset + 1))
        | none => throw (.unsupportedOpcode offset byte)
termination_by bytes.length
decreasing_by
  all_goals simp_wf <;> omega

/-- Decode serialized Bitcoin Script bytes into the modeled Script AST. -/
def deserializeScript (bytes : ByteArray) :
    Except DeserializationError Script :=
  deserializeScriptList bytes.data.toList 0

/-- AST form chosen when a canonical data push is decoded. The dedicated
    numeric opcodes erase the distinction between those byte vectors and
    numeric pushes, while every other vector remains `pushData`. -/
def normalizeSerializedData (data : ByteArray) : ScriptElement :=
  if data.size = 0 then
    .pushNum 0
  else if data.size = 1 then
    let byte := data.get! 0
    if 1 ≤ byte.toNat ∧ byte.toNat ≤ 16 then
      .pushNum byte.toNat
    else if byte = 0x81 then
      .pushNum (-1)
    else
      .pushData data
  else
    .pushData data

/-- Normalize one source element to the AST representation recovered from its
    canonical serialization. Large numeric pushes become data pushes because
    their wire encoding does not retain the source-level numeric annotation. -/
def normalizeSerializedElement : ScriptElement → ScriptElement
  | .op opcode => .op opcode
  | .pushData data => normalizeSerializedData data
  | .pushNum value =>
      if value = 0 ∨ value = -1 ∨ (1 ≤ value ∧ value ≤ 16) then
        .pushNum value
      else
        normalizeSerializedData (scriptNum value)

/-- Canonical AST representative recovered after a serialize/deserialize
    round trip. -/
def normalizeSerializedScript (script : Script) : Script :=
  script.map normalizeSerializedElement

end LeanMiniscript.Script
