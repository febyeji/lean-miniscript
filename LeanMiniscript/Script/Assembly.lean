import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-!
# Readable Bitcoin Script assembly

This module renders the modeled Script subset in the notation used by the BIP
379 translation table: opcode names omit the `OP_` prefix, numeric pushes are
decimal, and byte-vector pushes are lowercase hexadecimal wrapped in angle
brackets.
-/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- Render one byte as exactly two lowercase hexadecimal characters. -/
def byteHexChars (byte : UInt8) : List Char :=
  [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

/-- Render one byte as exactly two lowercase hexadecimal digits. -/
def byteHex (byte : UInt8) : String :=
  String.ofList (byteHexChars byte)

/-- Render a byte vector as lowercase hexadecimal without a prefix. -/
def byteArrayHex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap byteHexChars)

/-- BIP-style mnemonic for a modeled opcode. -/
def opcodeAssembly : Opcode → String
  | .OP_NOP => "NOP"
  | .OP_IF => "IF"
  | .OP_NOTIF => "NOTIF"
  | .OP_ELSE => "ELSE"
  | .OP_ENDIF => "ENDIF"
  | .OP_2DROP => "2DROP"
  | .OP_2DUP => "2DUP"
  | .OP_3DUP => "3DUP"
  | .OP_2OVER => "2OVER"
  | .OP_2ROT => "2ROT"
  | .OP_2SWAP => "2SWAP"
  | .OP_IFDUP => "IFDUP"
  | .OP_DEPTH => "DEPTH"
  | .OP_DROP => "DROP"
  | .OP_DUP => "DUP"
  | .OP_NIP => "NIP"
  | .OP_OVER => "OVER"
  | .OP_ROT => "ROT"
  | .OP_SWAP => "SWAP"
  | .OP_TUCK => "TUCK"
  | .OP_TOALTSTACK => "TOALTSTACK"
  | .OP_FROMALTSTACK => "FROMALTSTACK"
  | .OP_1ADD => "1ADD"
  | .OP_1SUB => "1SUB"
  | .OP_NEGATE => "NEGATE"
  | .OP_ABS => "ABS"
  | .OP_ADD => "ADD"
  | .OP_SUB => "SUB"
  | .OP_BOOLAND => "BOOLAND"
  | .OP_BOOLOR => "BOOLOR"
  | .OP_NOT => "NOT"
  | .OP_0NOTEQUAL => "0NOTEQUAL"
  | .OP_EQUAL => "EQUAL"
  | .OP_EQUALVERIFY => "EQUALVERIFY"
  | .OP_NUMEQUAL => "NUMEQUAL"
  | .OP_NUMEQUALVERIFY => "NUMEQUALVERIFY"
  | .OP_NUMNOTEQUAL => "NUMNOTEQUAL"
  | .OP_LESSTHAN => "LESSTHAN"
  | .OP_GREATERTHAN => "GREATERTHAN"
  | .OP_LESSTHANOREQUAL => "LESSTHANOREQUAL"
  | .OP_GREATERTHANOREQUAL => "GREATERTHANOREQUAL"
  | .OP_WITHIN => "WITHIN"
  | .OP_SHA256 => "SHA256"
  | .OP_HASH256 => "HASH256"
  | .OP_RIPEMD160 => "RIPEMD160"
  | .OP_HASH160 => "HASH160"
  | .OP_CHECKSIG => "CHECKSIG"
  | .OP_CHECKSIGVERIFY => "CHECKSIGVERIFY"
  | .OP_CHECKSIGADD => "CHECKSIGADD"
  | .OP_CHECKMULTISIG => "CHECKMULTISIG"
  | .OP_CHECKMULTISIGVERIFY => "CHECKMULTISIGVERIFY"
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
