instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray#{repr ba.data}"

namespace LeanMiniscript.Script

/-- Bitcoin Script opcodes represented by the current execution model.
    The compiler emits the BIP 379 subset; additional opcodes support
    differential execution against Bitcoin Core fixtures. -/
inductive Opcode where
  -- Flow control
  | OP_NOP
  | OP_NOP1
  | OP_NOP4
  | OP_NOP5
  | OP_NOP6
  | OP_NOP7
  | OP_NOP8
  | OP_NOP9
  | OP_NOP10
  | OP_RETURN
  | OP_IF
  | OP_NOTIF
  | OP_ELSE
  | OP_ENDIF
  -- Stack manipulation
  | OP_2DROP
  | OP_2DUP
  | OP_3DUP
  | OP_2OVER
  | OP_2ROT
  | OP_2SWAP
  | OP_IFDUP
  | OP_DEPTH
  | OP_DROP
  | OP_DUP
  | OP_NIP
  | OP_OVER
  | OP_PICK
  | OP_ROLL
  | OP_ROT
  | OP_SWAP
  | OP_TUCK
  | OP_TOALTSTACK
  | OP_FROMALTSTACK
  -- Arithmetic / Logic
  | OP_1ADD
  | OP_1SUB
  | OP_NEGATE
  | OP_ABS
  | OP_ADD
  | OP_SUB
  | OP_BOOLAND
  | OP_BOOLOR
  | OP_NOT
  | OP_0NOTEQUAL
  -- Comparison
  | OP_EQUAL
  | OP_EQUALVERIFY
  | OP_NUMEQUAL
  | OP_NUMEQUALVERIFY
  | OP_NUMNOTEQUAL
  | OP_LESSTHAN
  | OP_GREATERTHAN
  | OP_LESSTHANOREQUAL
  | OP_GREATERTHANOREQUAL
  | OP_MIN
  | OP_MAX
  | OP_WITHIN
  -- Cryptographic hash
  | OP_SHA256
  | OP_HASH256
  | OP_RIPEMD160
  | OP_HASH160
  | OP_SHA1
  -- Signature verification
  | OP_CHECKSIG
  | OP_CHECKSIGVERIFY
  | OP_CHECKSIGADD    -- Tapscript (BIP 342)
  | OP_CHECKMULTISIG  -- Legacy only
  | OP_CHECKMULTISIGVERIFY -- Legacy only
  -- Timelock
  | OP_CHECKSEQUENCEVERIFY
  | OP_CHECKLOCKTIMEVERIFY
  -- Verification
  | OP_VERIFY
  -- Other
  | OP_SIZE
  deriving Repr, DecidableEq, BEq

/-- The bytes Core rejects with BAD_OPCODE only in an executed branch:
OP_RESERVED (0x50), OP_VER (0x62), OP_RESERVED1 (0x89), OP_RESERVED2 (0x8a),
the undefined bytes 0xbb–0xfe, and OP_INVALIDOPCODE (0xff). In an unexecuted
branch Core passes over them. -/
def isBadOpcodeByte (byte : UInt8) : Bool :=
  let value := byte.toNat
  value == 0x50 || value == 0x62 || value == 0x89 || value == 0x8a || 0xbb ≤ value

/-- A byte of `isBadOpcodeByte`. -/
structure BadOpcode where
  byte : UInt8
  isBad : isBadOpcodeByte byte = true
  deriving Repr, DecidableEq

/-- The bytes Core rejects wherever they appear, in an unexecuted branch as
well: OP_VERIF (0x65), OP_VERNOTIF (0x66), and the 15 disabled opcodes OP_CAT
(0x7e), OP_SUBSTR, OP_LEFT, OP_RIGHT, OP_INVERT (0x83), OP_AND, OP_OR, OP_XOR,
OP_2MUL (0x8d), OP_2DIV, OP_MUL (0x95), OP_DIV, OP_MOD, OP_LSHIFT, and
OP_RSHIFT. -/
def isIllegalOpcodeByte (byte : UInt8) : Bool :=
  let value := byte.toNat
  value == 0x65 || value == 0x66 || (0x7e ≤ value && value ≤ 0x81) ||
    (0x83 ≤ value && value ≤ 0x86) || value == 0x8d || value == 0x8e ||
    (0x95 ≤ value && value ≤ 0x99)

/-- A byte of `isIllegalOpcodeByte`. -/
structure IllegalOpcode where
  byte : UInt8
  isIllegal : isIllegalOpcodeByte byte = true
  deriving Repr, DecidableEq

/-- A script element is an opcode, a data push, a byte that fails when
executed, or a byte that fails wherever it appears. -/
inductive ScriptElement where
  | op : Opcode → ScriptElement
  | pushData : ByteArray → ScriptElement
  | pushNum : Int → ScriptElement
  /-- Fails with BAD_OPCODE in an executed branch. -/
  | badOpcode : BadOpcode → ScriptElement
  /-- Fails with DISABLED_OPCODE or BAD_OPCODE in any branch. -/
  | illegalOpcode : IllegalOpcode → ScriptElement
  deriving Repr

/-- A Bitcoin Script is a list of script elements. -/
abbrev Script := List ScriptElement

-- Serialization and deserialization are defined in `Script.Codec`.
-- Witness ordering and the execution-stack boundary are defined in
-- `Miniscript.Witness`.

end LeanMiniscript.Script
