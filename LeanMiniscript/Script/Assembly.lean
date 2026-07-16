import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-!
# Readable Bitcoin Script assembly

This module renders the modeled Script subset in the notation used by the BIP
379 translation table: opcode names omit the `OP_` prefix, numeric pushes are
decimal, and byte-vector pushes are lowercase hexadecimal wrapped in angle
brackets.
-/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- Render one byte as exactly two lowercase hexadecimal digits. -/
def byteHex (byte : UInt8) : String :=
  String.ofList [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

/-- Render a byte vector as lowercase hexadecimal without a prefix. -/
def byteArrayHex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map byteHex)

/-- BIP-style mnemonic for a modeled opcode. -/
def opcodeAssembly : Opcode → String
  | .OP_IF => "IF"
  | .OP_NOTIF => "NOTIF"
  | .OP_ELSE => "ELSE"
  | .OP_ENDIF => "ENDIF"
  | .OP_IFDUP => "IFDUP"
  | .OP_DUP => "DUP"
  | .OP_SWAP => "SWAP"
  | .OP_TOALTSTACK => "TOALTSTACK"
  | .OP_FROMALTSTACK => "FROMALTSTACK"
  | .OP_ADD => "ADD"
  | .OP_BOOLAND => "BOOLAND"
  | .OP_BOOLOR => "BOOLOR"
  | .OP_0NOTEQUAL => "0NOTEQUAL"
  | .OP_EQUAL => "EQUAL"
  | .OP_EQUALVERIFY => "EQUALVERIFY"
  | .OP_NUMEQUAL => "NUMEQUAL"
  | .OP_SHA256 => "SHA256"
  | .OP_HASH256 => "HASH256"
  | .OP_RIPEMD160 => "RIPEMD160"
  | .OP_HASH160 => "HASH160"
  | .OP_CHECKSIG => "CHECKSIG"
  | .OP_CHECKSIGADD => "CHECKSIGADD"
  | .OP_CHECKMULTISIG => "CHECKMULTISIG"
  | .OP_CHECKSEQUENCEVERIFY => "CHECKSEQUENCEVERIFY"
  | .OP_CHECKLOCKTIMEVERIFY => "CHECKLOCKTIMEVERIFY"
  | .OP_VERIFY => "VERIFY"
  | .OP_SIZE => "SIZE"

/-- Render one Script element in BIP-style assembly notation. -/
def elementAssembly : ScriptElement → String
  | .op opcode => opcodeAssembly opcode
  | .pushData data => "<" ++ byteArrayHex data ++ ">"
  | .pushNum number => toString number

/-- Render a Script as a space-separated BIP-style assembly string. -/
def toAssembly (script : Script) : String :=
  String.intercalate " " (script.map elementAssembly)

example : byteHex 0x00 = "00" := by rfl
example : byteHex 0xaf = "af" := by rfl
example : byteArrayHex ⟨#[0x00, 0xaf, 0x10]⟩ = "00af10" := by rfl
example : toAssembly [.pushNum 2, .op .OP_DUP, .pushData ⟨#[0xaa]⟩] =
    "2 DUP <aa>" := by
  rfl

end LeanMiniscript.Script
