import LeanMiniscript.Script.Serialization
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Script

open LeanMiniscript.Miniscript

/-! Build-checked serialization fixtures for opcode values, push boundaries,
numeric encodings, and representative compiler outputs. -/

def opcodeSerializationFixtures : List (Opcode × UInt8) :=
  [(.OP_IF, 0x63), (.OP_NOTIF, 0x64), (.OP_ELSE, 0x67), (.OP_ENDIF, 0x68),
   (.OP_IFDUP, 0x73), (.OP_DUP, 0x76), (.OP_SWAP, 0x7c),
   (.OP_TOALTSTACK, 0x6b), (.OP_FROMALTSTACK, 0x6c),
   (.OP_ADD, 0x93), (.OP_BOOLAND, 0x9a), (.OP_BOOLOR, 0x9b),
   (.OP_0NOTEQUAL, 0x92), (.OP_EQUAL, 0x87), (.OP_EQUALVERIFY, 0x88),
   (.OP_NUMEQUAL, 0x9c), (.OP_SHA256, 0xa8), (.OP_HASH256, 0xaa),
   (.OP_RIPEMD160, 0xa6), (.OP_HASH160, 0xa9), (.OP_CHECKSIG, 0xac),
   (.OP_CHECKSIGADD, 0xba), (.OP_CHECKMULTISIG, 0xae),
   (.OP_CHECKSEQUENCEVERIFY, 0xb2), (.OP_CHECKLOCKTIMEVERIFY, 0xb1),
   (.OP_VERIFY, 0x69), (.OP_SIZE, 0x82)]

example : ∀ opcode, ∃ byte, (opcode, byte) ∈ opcodeSerializationFixtures := by
  intro opcode
  cases opcode <;> simp [opcodeSerializationFixtures]

example : opcodeSerializationFixtures.all
    (fun fixture => opcodeByte fixture.1 == fixture.2) = true := by
  rfl

example : pushDataPrefix 0 = .ok [0x00] := by rfl
example : pushDataPrefix 1 = .ok [0x01] := by rfl
example : pushDataPrefix 75 = .ok [0x4b] := by rfl
example : pushDataPrefix 76 = .ok [0x4c, 0x4c] := by rfl
example : pushDataPrefix 255 = .ok [0x4c, 0xff] := by rfl
example : pushDataPrefix 256 = .ok [0x4d, 0x00, 0x01] := by rfl
example : pushDataPrefix 65535 = .ok [0x4d, 0xff, 0xff] := by rfl
example : pushDataPrefix 65536 = .ok [0x4e, 0x00, 0x00, 0x01, 0x00] := by
  rfl
example : pushDataPrefix (MAX_PUSHDATA_SIZE + 1) =
    .error (.pushDataTooLarge (MAX_PUSHDATA_SIZE + 1)) := by
  rfl

def repeatedByte (count : Nat) (byte : UInt8) : ByteArray :=
  ⟨(List.replicate count byte).toArray⟩

example : (serializePushData (repeatedByte 0 0xaa)).map ByteArray.size = .ok 1 := by
  rfl
example : (serializePushData (repeatedByte 1 0xaa)).map ByteArray.size = .ok 2 := by
  rfl
example : serializePushData ⟨#[0x01]⟩ = .ok ⟨#[0x51]⟩ := by
  rfl
example : serializePushData ⟨#[0x10]⟩ = .ok ⟨#[0x60]⟩ := by
  rfl
example : serializePushData ⟨#[0x11]⟩ = .ok ⟨#[0x01, 0x11]⟩ := by
  rfl
example : serializePushData ⟨#[0x81]⟩ = .ok ⟨#[0x4f]⟩ := by
  rfl
example : serializePushData ⟨#[0x80]⟩ = .ok ⟨#[0x01, 0x80]⟩ := by
  rfl
example : (serializePushData (repeatedByte 75 0xaa)).map ByteArray.size = .ok 76 := by
  rfl
example : (serializePushData (repeatedByte 76 0xaa)).map ByteArray.size = .ok 78 := by
  rfl
set_option maxRecDepth 2048 in
example : (serializePushData (repeatedByte 255 0xaa)).map ByteArray.size = .ok 257 := by
  rfl
set_option maxRecDepth 2048 in
example : (serializePushData (repeatedByte 256 0xaa)).map ByteArray.size = .ok 259 := by
  rfl

example : serializePushNum 0 = .ok ⟨#[0x00]⟩ := by rfl
example : serializePushNum (-1) = .ok ⟨#[0x4f]⟩ := by rfl
example : serializePushNum 1 = .ok ⟨#[0x51]⟩ := by rfl
example : serializePushNum 16 = .ok ⟨#[0x60]⟩ := by rfl
example : serializePushNum 17 = .ok ⟨#[0x01, 0x11]⟩ := by rfl
example : serializePushNum 127 = .ok ⟨#[0x01, 0x7f]⟩ := by rfl
example : serializePushNum 128 = .ok ⟨#[0x02, 0x80, 0x00]⟩ := by rfl

def serializationKeyA : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0x11).toArray⟩

def serializationKeyB : PubKey :=
  PubKey.ofBytes ⟨#[0x03] ++ (List.replicate 32 0x22).toArray⟩

def serializationXOnlyKeyA : PubKey := PubKey.ofBytes (repeatedByte 32 0x11)
def serializationXOnlyKeyB : PubKey := PubKey.ofBytes (repeatedByte 32 0x22)
def serializationHash256 : Hash256 := Hash256.ofBytes (repeatedByte 32 0xaa)

example : serializeScript (compile .zero) = .ok ⟨#[0x00]⟩ := by
  rfl

example : serializeScript (compile .one) = .ok ⟨#[0x51]⟩ := by
  rfl

example : (match serializeScript (compile (.pk_k serializationKeyA)) with
    | .ok bytes => bytes.data == (#[0x21] ++ serializationKeyA.data)
    | .error _ => false) = true := by
  native_decide

example : serializeScript (compile (.older 42)) = .ok ⟨#[0x01, 0x2a, 0xb2]⟩ := by
  rfl

example : serializeScript (compile (.after 500000000)) =
    .ok ⟨#[0x04, 0x00, 0x65, 0xcd, 0x1d, 0xb1]⟩ := by
  rfl

example : serializedScriptSize (compile (.sha256 serializationHash256)) = .ok 39 := by
  rfl

example : serializedScriptSize
    (compile (.multi 2 [serializationKeyA, serializationKeyB])) = .ok 71 := by
  rfl

example : serializedScriptSize
    (compile (.multi_a 2 [serializationXOnlyKeyA, serializationXOnlyKeyB])) = .ok 70 := by
  rfl

def maxSerializedScriptFixture : Script :=
  List.replicate 10000 (.op .OP_DUP)

example : (match serializedScriptSize maxSerializedScriptFixture with
    | .ok size => size == 10000
    | .error _ => false) = true := by
  native_decide

end LeanMiniscript.Script
