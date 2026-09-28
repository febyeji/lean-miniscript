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
  | OP_2DROP
  | OP_2DUP
  | OP_2ROT
  | OP_IFDUP
  | OP_DEPTH
  | OP_DROP
  | OP_DUP
  | OP_NIP
  | OP_OVER
  | OP_ROT
  | OP_SWAP
  | OP_TUCK
  | OP_TOALTSTACK
  | OP_FROMALTSTACK
  -- Arithmetic / Logic
  | OP_ADD
  | OP_BOOLAND
  | OP_BOOLOR
  | OP_NOT
  | OP_0NOTEQUAL
  -- Comparison
  | OP_EQUAL
  | OP_EQUALVERIFY
  | OP_NUMEQUAL
  | OP_NUMEQUALVERIFY
  | OP_WITHIN
  -- Cryptographic hash
  | OP_SHA256
  | OP_HASH256
  | OP_RIPEMD160
  | OP_HASH160
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

/-- A script element is either an opcode or a data push. -/
inductive ScriptElement where
  | op : Opcode → ScriptElement
  | pushData : ByteArray → ScriptElement
  | pushNum : Int → ScriptElement
  deriving Repr

/-- A Bitcoin Script is a list of script elements. -/
abbrev Script := List ScriptElement

-- Serialization and deserialization are defined in `Script.Codec`.
-- Witness ordering and the execution-stack boundary are defined in
-- `Miniscript.Witness`.

end LeanMiniscript.Script
