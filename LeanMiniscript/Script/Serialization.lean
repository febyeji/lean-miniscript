import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-- Serialization can only encode data-push lengths representable by Bitcoin
    Script's four-byte `OP_PUSHDATA4` prefix. -/
inductive SerializationError where
  | pushDataTooLarge (size : Nat)
  deriving Repr, DecidableEq

/-- Largest byte-vector length representable by an `OP_PUSHDATA4` prefix. -/
def MAX_PUSHDATA_SIZE : Nat := 4294967295

/-- Byte value assigned to each modeled Bitcoin Script opcode. -/
def opcodeByte : Opcode → UInt8
  | .OP_IF => 0x63
  | .OP_NOTIF => 0x64
  | .OP_ELSE => 0x67
  | .OP_ENDIF => 0x68
  | .OP_IFDUP => 0x73
  | .OP_DUP => 0x76
  | .OP_SWAP => 0x7c
  | .OP_TOALTSTACK => 0x6b
  | .OP_FROMALTSTACK => 0x6c
  | .OP_ADD => 0x93
  | .OP_BOOLAND => 0x9a
  | .OP_BOOLOR => 0x9b
  | .OP_0NOTEQUAL => 0x92
  | .OP_EQUAL => 0x87
  | .OP_EQUALVERIFY => 0x88
  | .OP_NUMEQUAL => 0x9c
  | .OP_SHA256 => 0xa8
  | .OP_HASH256 => 0xaa
  | .OP_RIPEMD160 => 0xa6
  | .OP_HASH160 => 0xa9
  | .OP_CHECKSIG => 0xac
  | .OP_CHECKSIGADD => 0xba
  | .OP_CHECKMULTISIG => 0xae
  | .OP_CHECKSEQUENCEVERIFY => 0xb2
  | .OP_CHECKLOCKTIMEVERIFY => 0xb1
  | .OP_VERIFY => 0x69
  | .OP_SIZE => 0x82

/-- Encode the low two bytes of a natural number in little-endian order. -/
def uint16LE (n : Nat) : List UInt8 :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256)]

/-- Encode the low four bytes of a natural number in little-endian order. -/
def uint32LE (n : Nat) : List UInt8 :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 16777216)]

/-- Minimal length prefix used by `CScript` for a raw byte-vector push. -/
def pushDataPrefix (size : Nat) : Except SerializationError (List UInt8) :=
  if size < 76 then
    .ok [UInt8.ofNat size]
  else if size ≤ 255 then
    .ok [0x4c, UInt8.ofNat size]
  else if size ≤ 65535 then
    .ok (0x4d :: uint16LE size)
  else if size ≤ MAX_PUSHDATA_SIZE then
    .ok (0x4e :: uint32LE size)
  else
    .error (.pushDataTooLarge size)

/-- Serialize a byte-vector with the shortest available length prefix. -/
private def serializeLengthPrefixedPush
    (data : ByteArray) : Except SerializationError ByteArray := do
  let lengthPrefix ← pushDataPrefix data.size
  pure ⟨(lengthPrefix ++ data.data.toList).toArray⟩

/-- Serialize a byte-vector push using Bitcoin Script's minimal-push rules.

    Single-byte encodings of `1` through `16` and `-1` use their dedicated
    opcodes; all other values use the shortest available length prefix. -/
def serializePushData (data : ByteArray) : Except SerializationError ByteArray := do
  if data.size = 1 then
    let byte := data.get! 0
    if 1 ≤ byte.toNat ∧ byte.toNat ≤ 16 then
      pure ⟨#[UInt8.ofNat (0x50 + byte.toNat)]⟩
    else if byte = 0x81 then
      pure ⟨#[0x4f]⟩
    else
      serializeLengthPrefixedPush data
  else
    serializeLengthPrefixedPush data

/-- Serialize a numeric push using `OP_0`, `OP_1NEGATE`, or `OP_1` through
    `OP_16` when possible, and otherwise push the canonical Script-number
    encoding. -/
def serializePushNum (n : Int) : Except SerializationError ByteArray :=
  if n = 0 then
    .ok ⟨#[0x00]⟩
  else if n = -1 then
    .ok ⟨#[0x4f]⟩
  else if 1 ≤ n ∧ n ≤ 16 then
    .ok ⟨#[UInt8.ofNat (0x50 + n.toNat)]⟩
  else
    serializePushData (scriptNum n)

/-- Serialize one modeled Script element. -/
def serializeElement : ScriptElement → Except SerializationError ByteArray
  | .op opcode => .ok ⟨#[opcodeByte opcode]⟩
  | .pushData data => serializePushData data
  | .pushNum n => serializePushNum n

/-- Serialize a modeled Script to canonical Bitcoin Script bytes. -/
def serializeScript (script : Script) : Except SerializationError ByteArray :=
  script.foldlM (fun bytes element => do
      let elementBytes ← serializeElement element
      pure (bytes ++ elementBytes)) ByteArray.empty

/-- Exact serialized byte size of a modeled Script. -/
def serializedScriptSize (script : Script) : Except SerializationError Nat :=
  (serializeScript script).map ByteArray.size

theorem serializedScriptSize_eq (script : Script) :
    serializedScriptSize script = (serializeScript script).map ByteArray.size := by
  rfl

end LeanMiniscript.Script
