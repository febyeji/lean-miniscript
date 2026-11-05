import LeanMiniscript.Script.ScriptCode

/-!
Original-byte opcode rules of Core's legacy execution loop: disabled opcodes
and minimal pushes. GetOp and FindAndDelete are in `Script.ScriptCode`.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

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
