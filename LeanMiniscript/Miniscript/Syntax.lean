import LeanMiniscript.Script.Syntax  -- for Repr ByteArray instance

namespace LeanMiniscript.Miniscript

/-- Resolved public-key bytes. Context-specific length and serialization-shape
    checks remain in `Miniscript.Context`, while this wrapper prevents hashes
    and arbitrary stack elements from being used as keys accidentally. -/
structure PubKey where
  bytes : ByteArray
  deriving Repr

/-- A SHA256/HASH256 digest boundary. Length validity remains an explicit
    `WellFormed` obligation. -/
structure Hash256 where
  bytes : ByteArray
  deriving Repr

/-- A HASH160/RIPEMD160 digest boundary. Length validity remains an explicit
    `WellFormed` obligation. -/
structure Hash160 where
  bytes : ByteArray
  deriving Repr

namespace PubKey

def ofBytes (bytes : ByteArray) : PubKey := ⟨bytes⟩
def size (key : PubKey) : Nat := key.bytes.size
def data (key : PubKey) : Array UInt8 := key.bytes.data

instance : Coe PubKey ByteArray := ⟨PubKey.bytes⟩

end PubKey

namespace Hash256

def ofBytes (bytes : ByteArray) : Hash256 := ⟨bytes⟩
def size (hash : Hash256) : Nat := hash.bytes.size
def data (hash : Hash256) : Array UInt8 := hash.bytes.data

instance : Coe Hash256 ByteArray := ⟨Hash256.bytes⟩

end Hash256

namespace Hash160

def ofBytes (bytes : ByteArray) : Hash160 := ⟨bytes⟩
def size (hash : Hash160) : Nat := hash.bytes.size
def data (hash : Hash160) : Array UInt8 := hash.bytes.data

instance : Coe Hash160 ByteArray := ⟨Hash160.bytes⟩

end Hash160

/-- Core Miniscript fragment AST.

    Core fragments are the primitive layer used by typing, compilation, and
    future proofs. Surface-only sugar such as `pk`, `pkh`, `and_n`, `t:`,
    `l:`, and `u:` is represented by `SurfaceFragment` and lowered through
    `desugar`. -/
inductive CoreFragment where
  -- Leaves
  | zero : CoreFragment                               -- 0
  | one : CoreFragment                                -- 1
  | pk_k : PubKey → CoreFragment                      -- <key>
  | pk_h : PubKey → CoreFragment                      -- OP_DUP OP_HASH160 <HASH160(key)> OP_EQUALVERIFY
  | older : Nat → CoreFragment                        -- <n> OP_CHECKSEQUENCEVERIFY
  | after : Nat → CoreFragment                        -- <n> OP_CHECKLOCKTIMEVERIFY
  | sha256 : Hash256 → CoreFragment                   -- OP_SIZE <32> OP_EQUALVERIFY OP_SHA256 <hash> OP_EQUAL
  | hash256 : Hash256 → CoreFragment                  -- OP_SIZE <32> OP_EQUALVERIFY OP_HASH256 <hash> OP_EQUAL
  | ripemd160 : Hash160 → CoreFragment                -- OP_SIZE <32> OP_EQUALVERIFY OP_RIPEMD160 <hash> OP_EQUAL
  | hash160 : Hash160 → CoreFragment                  -- OP_SIZE <32> OP_EQUALVERIFY OP_HASH160 <hash> OP_EQUAL
  -- Connectives
  | and_v : CoreFragment → CoreFragment → CoreFragment -- [X] [Y]
  | and_b : CoreFragment → CoreFragment → CoreFragment -- [X] [Y] OP_BOOLAND
  | or_b : CoreFragment → CoreFragment → CoreFragment  -- [X] [Y] OP_BOOLOR
  | or_c : CoreFragment → CoreFragment → CoreFragment  -- [X] OP_NOTIF [Y] OP_ENDIF
  | or_d : CoreFragment → CoreFragment → CoreFragment  -- [X] OP_IFDUP OP_NOTIF [Y] OP_ENDIF
  | or_i : CoreFragment → CoreFragment → CoreFragment  -- OP_IF [X] OP_ELSE [Y] OP_ENDIF
  | andor : CoreFragment → CoreFragment → CoreFragment → CoreFragment
                                                        -- [X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF
  -- Wrappers
  | a : CoreFragment → CoreFragment                    -- OP_TOALTSTACK [X] OP_FROMALTSTACK
  | s : CoreFragment → CoreFragment                    -- OP_SWAP [X]
  | c : CoreFragment → CoreFragment                    -- [X] OP_CHECKSIG
  | d : CoreFragment → CoreFragment                    -- OP_DUP OP_IF [X] OP_ENDIF
  | v : CoreFragment → CoreFragment                    -- [X] OP_VERIFY (or replace last OP_CHECKSIG with OP_CHECKSIGVERIFY)
  | j : CoreFragment → CoreFragment                    -- OP_SIZE OP_0NOTEQUAL OP_IF [X] OP_ENDIF
  | n : CoreFragment → CoreFragment                    -- [X] OP_0NOTEQUAL
  -- Threshold
  | thresh : Nat → List CoreFragment → CoreFragment    -- k-of-n threshold
  | multi : Nat → List PubKey → CoreFragment           -- OP_CHECKMULTISIG (legacy)
  | multi_a : Nat → List PubKey → CoreFragment         -- OP_CHECKSIGADD based (tapscript)
  deriving Repr

/-- BIP 379 surface Miniscript AST.

    Core fragments are embedded with `core`; surface-only syntactic sugar is
    represented explicitly and lowered by `desugar`. -/
inductive SurfaceFragment where
  | core : CoreFragment → SurfaceFragment
  | pk : PubKey → SurfaceFragment                     -- c:pk_k(key)
  | pkh : PubKey → SurfaceFragment                    -- c:pk_h(key)
  | and_n : SurfaceFragment → SurfaceFragment → SurfaceFragment
  | t : SurfaceFragment → SurfaceFragment
  | l : SurfaceFragment → SurfaceFragment
  | u : SurfaceFragment → SurfaceFragment
  deriving Repr

/-- Lower BIP 379 surface syntax into the core fragment language. -/
def SurfaceFragment.desugar : SurfaceFragment → CoreFragment
  | .core fragment => fragment
  | .pk key => .c (.pk_k key)
  | .pkh key => .c (.pk_h key)
  | .and_n x y => .andor x.desugar y.desugar .zero
  | .t x => .and_v x.desugar .one
  | .l x => .or_i .zero x.desugar
  | .u x => .or_i x.desugar .zero

/-- Lower BIP 379 surface syntax into the core fragment language. -/
def desugar : SurfaceFragment → CoreFragment := SurfaceFragment.desugar

/-- Policy language (high-level spending conditions). -/
inductive Policy where
  | key : PubKey → Policy
  | older : Nat → Policy
  | after : Nat → Policy
  | sha256 : Hash256 → Policy
  | hash256 : Hash256 → Policy
  | ripemd160 : Hash160 → Policy
  | hash160 : Hash160 → Policy
  | and : Policy → Policy → Policy
  | or : Policy → Policy → Policy
  | thresh : Nat → List Policy → Policy
  deriving Repr

-- AST side conditions live in `Miniscript.Validation`.
-- Structural metrics live in `Miniscript.Metrics`.

end LeanMiniscript.Miniscript
