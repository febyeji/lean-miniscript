import LeanMiniscript.Script.Codec.Serialization

/-!
Original-byte Script operations shared by execution, witness scanning,
and legacy fixture decoding. Push boundaries and minimality retain the
original encoding.
-/

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

/-- Opcodes disabled unconditionally during legacy Script execution. -/
def coreLegacyDisabledOpcode (opcode : Nat) : Bool :=
  [0x7e, 0x7f, 0x80, 0x81, 0x83, 0x84, 0x85, 0x86,
    0x8d, 0x8e, 0x95, 0x96, 0x97, 0x98, 0x99].contains opcode

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

end LeanMiniscript.Extraction
