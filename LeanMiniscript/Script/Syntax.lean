instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray#{repr ba.data}"

namespace LeanMiniscript.Script

/-- Bitcoin Script opcodes represented by the current execution model.
    The compiler emits the BIP 379 subset; additional opcodes support
    differential execution against Bitcoin Core fixtures. -/
inductive Opcode where
  -- Flow control
  | OP_NOP
  | OP_IF
  | OP_NOTIF
  | OP_ELSE
  | OP_ENDIF
  -- Stack manipulation
  | OP_IFDUP
  | OP_DUP
  | OP_SWAP
  | OP_TOALTSTACK
  | OP_FROMALTSTACK
  -- Arithmetic / Logic
  | OP_ADD
  | OP_BOOLAND
  | OP_BOOLOR
  | OP_0NOTEQUAL
  -- Comparison
  | OP_EQUAL
  | OP_EQUALVERIFY
  | OP_NUMEQUAL
  -- Cryptographic hash
  | OP_SHA256
  | OP_HASH256
  | OP_RIPEMD160
  | OP_HASH160
  -- Signature verification
  | OP_CHECKSIG
  | OP_CHECKSIGADD    -- Tapscript (BIP 342)
  | OP_CHECKMULTISIG  -- Legacy only
  -- Timelock
  | OP_CHECKSEQUENCEVERIFY
  | OP_CHECKLOCKTIMEVERIFY
  -- Verification
  | OP_VERIFY
  -- Other
  | OP_SIZE
  deriving Repr, DecidableEq, BEq

/-- A script element is either an opcode or a data push. -/
inductive ScriptElement where
  | op : Opcode → ScriptElement
  | pushData : ByteArray → ScriptElement
  | pushNum : Int → ScriptElement
  deriving Repr

/-- A Bitcoin Script is a list of script elements. -/
abbrev Script := List ScriptElement

-- Serialization is defined in `Script.Serialization`.
-- TODO: Define script deserialization.
-- Witness ordering and the execution-stack boundary are defined in
-- `Miniscript.Witness`.

end LeanMiniscript.Script
