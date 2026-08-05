import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Script.Assembly
import LeanMiniscript.Script.Serialization

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Compilation conformance fixtures

Build-checked assembly and serialized-byte fixtures for every constructor in
`CoreFragment` and `SurfaceFragment`.

The expected bytes were generated from the BIP 379 translation table pinned at
`bitcoin/bips@c021a5f51ae9d3e71a41eac3dda6dc060fead35d` and cross-checked with
`rust-miniscript` 13.1.0 at commit
`c9ed0006144ad92436191047edd4132f79e5916a`.

`Script.hash160` remains deliberately opaque for formal semantics. The `pk_h`
and `pkh` byte fixtures use `compileConcrete`, backed by the pinned pure Lean
`lean-hash160` package, exercising the executable compiler boundary without a
new axiom or fixture-specific resolver.
-/

private def rawBytes (data : Array UInt8) : ByteArray := ⟨data⟩

private def joinBytes (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) ByteArray.empty

/-- A direct push used by the pinned fixtures, whose payloads are all shorter
than `OP_PUSHDATA1`'s 76-byte boundary. -/
private def directPush (payload : ByteArray) : ByteArray :=
  rawBytes #[UInt8.ofNat payload.size] ++ payload

private def scriptBytesMatch (script : Script) (expected : ByteArray) : Bool :=
  match serializeScript script with
  | .ok actual => actual.data == expected.data
  | .error _ => false

def oracleKeyA : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0x02, 0xd7, 0x92, 0x4d, 0x4f, 0x7d, 0x43, 0xea, 0x96, 0x5a, 0x46,
    0x5a, 0xe3, 0x09, 0x5f, 0xf4, 0x11, 0x31, 0xe5, 0x94, 0x6f, 0x3c,
    0x85, 0xf7, 0x9e, 0x44, 0xad, 0xbc, 0xf8, 0xe2, 0x7e, 0x08, 0x0e]

def oracleKeyB : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0x03, 0xb5, 0x06, 0xa1, 0xdb, 0xe5, 0x7b, 0x4b, 0xf4, 0x8c, 0x95,
    0xe0, 0xc7, 0xd4, 0x17, 0xb8, 0x7d, 0xd3, 0xb4, 0x34, 0x9d, 0x29,
    0x0d, 0x2e, 0x7e, 0x9b, 0xa7, 0x2c, 0x91, 0x26, 0x52, 0xd8, 0x0a]

def oracleKeyC : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0,
    0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d,
    0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98]

def oracleXOnlyKeyA : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0xd7, 0x92, 0x4d, 0x4f, 0x7d, 0x43, 0xea, 0x96, 0x5a, 0x46, 0x5a,
    0xe3, 0x09, 0x5f, 0xf4, 0x11, 0x31, 0xe5, 0x94, 0x6f, 0x3c, 0x85,
    0xf7, 0x9e, 0x44, 0xad, 0xbc, 0xf8, 0xe2, 0x7e, 0x08, 0x0e]

def oracleXOnlyKeyB : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0xb5, 0x06, 0xa1, 0xdb, 0xe5, 0x7b, 0x4b, 0xf4, 0x8c, 0x95, 0xe0,
    0xc7, 0xd4, 0x17, 0xb8, 0x7d, 0xd3, 0xb4, 0x34, 0x9d, 0x29, 0x0d,
    0x2e, 0x7e, 0x9b, 0xa7, 0x2c, 0x91, 0x26, 0x52, 0xd8, 0x0a]

def oracleXOnlyKeyC : PubKey :=
  PubKey.ofBytes <| rawBytes #[
    0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62,
    0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce,
    0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98]

def oracleHash256 : Hash256 :=
  Hash256.ofBytes <| rawBytes #[
    0x4a, 0xe8, 0x15, 0x72, 0xf0, 0x6e, 0x1b, 0x88, 0xfd, 0x5c, 0xed,
    0x7a, 0x1a, 0x00, 0x09, 0x45, 0x43, 0x2e, 0x83, 0xe1, 0x55, 0x1e,
    0x6f, 0x72, 0x1e, 0xe9, 0xc0, 0x0b, 0x8c, 0xc3, 0x32, 0x60]

def oracleHash160 : Hash160 :=
  Hash160.ofBytes <| rawBytes #[
    0x4a, 0xe8, 0x15, 0x72, 0xf0, 0x6e, 0x1b, 0x88, 0xfd, 0x5c,
    0xed, 0x7a, 0x1a, 0x00, 0x09, 0x45, 0x43, 0xa0, 0x00, 0x69]

/-- HASH160 of `oracleKeyA`, computed by rust-miniscript's rust-bitcoin
dependency. This value is kept distinct from `oracleHash160`, which is the
literal hash-lock argument used by other fixtures. -/
def oracleKeyAHash160 : Hash160 :=
  Hash160.ofBytes <| rawBytes #[
    0x9f, 0xc5, 0xdb, 0xe5, 0xef, 0xdc, 0xe1, 0x03, 0x74, 0xa4,
    0xdd, 0x40, 0x53, 0xc9, 0x3a, 0xf5, 0x40, 0x21, 0x17, 0x18]

example : ((LeanHash160.hash160 oracleKeyA).data == oracleKeyAHash160.data) = true := by
  native_decide

private def pkA : CoreFragment := .c (.pk_k oracleKeyA)
private def pkB : CoreFragment := .c (.pk_k oracleKeyB)
private def pkC : CoreFragment := .c (.pk_k oracleKeyC)
private def verifiedOlder : CoreFragment := .v (.older 42)

private def pkABytes : ByteArray :=
  joinBytes [directPush oracleKeyA, rawBytes #[0xac]]

private def pkBBytes : ByteArray :=
  joinBytes [directPush oracleKeyB, rawBytes #[0xac]]

private def pkCBytes : ByteArray :=
  joinBytes [directPush oracleKeyC, rawBytes #[0xac]]

private def verifiedOlderBytes : ByteArray := rawBytes #[0x01, 0x2a, 0xb2, 0x69]

/-! ## Coverage indexes -/

inductive CoreConstructorTag where
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 | hash160
  | andV | andB | orB | orC | orD | orI | andor
  | a | s | c | d | v | j | n
  | thresh | multi | multiA
  deriving DecidableEq

inductive SurfaceConstructorTag where
  | core | pk | pkh | andN | t | l | u
  deriving DecidableEq

/-- The top-level constructor represented by a core fragment. Keeping this
mapping total makes fixture coverage fail to build when the core AST grows. -/
private def CoreFragment.constructorTag : CoreFragment → CoreConstructorTag
  | .zero => .zero
  | .one => .one
  | .pk_k _ => .pkK
  | .pk_h _ => .pkH
  | .older _ => .older
  | .after _ => .after
  | .sha256 _ => .sha256
  | .hash256 _ => .hash256
  | .ripemd160 _ => .ripemd160
  | .hash160 _ => .hash160
  | .and_v _ _ => .andV
  | .and_b _ _ => .andB
  | .or_b _ _ => .orB
  | .or_c _ _ => .orC
  | .or_d _ _ => .orD
  | .or_i _ _ => .orI
  | .andor _ _ _ => .andor
  | .a _ => .a
  | .s _ => .s
  | .c _ => .c
  | .d _ => .d
  | .v _ => .v
  | .j _ => .j
  | .n _ => .n
  | .thresh _ _ => .thresh
  | .multi _ _ => .multi
  | .multi_a _ _ => .multiA

/-- The top-level constructor represented by a surface fragment. -/
private def SurfaceFragment.constructorTag : SurfaceFragment → SurfaceConstructorTag
  | .core _ => .core
  | .pk _ => .pk
  | .pkh _ => .pkh
  | .and_n _ _ => .andN
  | .t _ => .t
  | .l _ => .l
  | .u _ => .u

/-! ## Core leaf fixtures -/

example : compile .zero = [.pushNum 0] := by rfl
example : scriptBytesMatch (compile .zero) (rawBytes #[0x00]) = true := by native_decide

example : compile .one = [.pushNum 1] := by rfl
example : scriptBytesMatch (compile .one) (rawBytes #[0x51]) = true := by native_decide

example : compile (.pk_k oracleKeyA) = [.pushData oracleKeyA] := by rfl
example : scriptBytesMatch (compile (.pk_k oracleKeyA))
    (directPush oracleKeyA) = true := by
  native_decide

example : compile (.pk_h oracleKeyA) =
    [.op .OP_DUP, .op .OP_HASH160, .pushData (hash160 oracleKeyA),
      .op .OP_EQUALVERIFY] := by
  rfl

example : compileConcrete (.pk_h oracleKeyA) =
      [.op .OP_DUP, .op .OP_HASH160,
        .pushData (LeanHash160.hash160 oracleKeyA),
        .op .OP_EQUALVERIFY] := by
  rfl

example : scriptBytesMatch (compileConcrete (.pk_h oracleKeyA))
      (joinBytes [rawBytes #[0x76, 0xa9], directPush oracleKeyAHash160,
        rawBytes #[0x88]]) = true := by
  native_decide

example : compile (.older 42) = [.pushNum 42, .op .OP_CHECKSEQUENCEVERIFY] := by rfl
example : scriptBytesMatch (compile (.older 42))
    (rawBytes #[0x01, 0x2a, 0xb2]) = true := by
  native_decide

example : compile (.after 500000000) =
    [.pushNum 500000000, .op .OP_CHECKLOCKTIMEVERIFY] := by
  rfl
example : scriptBytesMatch (compile (.after 500000000))
    (rawBytes #[0x04, 0x00, 0x65, 0xcd, 0x1d, 0xb1]) = true := by
  native_decide

example : compile (.sha256 oracleHash256) =
    [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_SHA256,
      .pushData oracleHash256, .op .OP_EQUAL] := by
  rfl
example : scriptBytesMatch (compile (.sha256 oracleHash256))
    (joinBytes [rawBytes #[0x82, 0x01, 0x20, 0x88, 0xa8],
      directPush oracleHash256, rawBytes #[0x87]]) = true := by
  native_decide

example : compile (.hash256 oracleHash256) =
    [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH256,
      .pushData oracleHash256, .op .OP_EQUAL] := by
  rfl
example : scriptBytesMatch (compile (.hash256 oracleHash256))
    (joinBytes [rawBytes #[0x82, 0x01, 0x20, 0x88, 0xaa],
      directPush oracleHash256, rawBytes #[0x87]]) = true := by
  native_decide

example : compile (.ripemd160 oracleHash160) =
    [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_RIPEMD160,
      .pushData oracleHash160, .op .OP_EQUAL] := by
  rfl
example : scriptBytesMatch (compile (.ripemd160 oracleHash160))
    (joinBytes [rawBytes #[0x82, 0x01, 0x20, 0x88, 0xa6],
      directPush oracleHash160, rawBytes #[0x87]]) = true := by
  native_decide

example : compile (.hash160 oracleHash160) =
    [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH160,
      .pushData oracleHash160, .op .OP_EQUAL] := by
  rfl
example : scriptBytesMatch (compile (.hash160 oracleHash160))
    (joinBytes [rawBytes #[0x82, 0x01, 0x20, 0x88, 0xa9],
      directPush oracleHash160, rawBytes #[0x87]]) = true := by
  native_decide

/-! ## Core connective fixtures -/

example : compile (.and_v verifiedOlder pkB) =
    [.pushNum 42, .op .OP_CHECKSEQUENCEVERIFY, .op .OP_VERIFY,
      .pushData oracleKeyB, .op .OP_CHECKSIG] := by
  rfl
example : scriptBytesMatch (compile (.and_v verifiedOlder pkB))
    (joinBytes [verifiedOlderBytes, pkBBytes]) = true := by
  native_decide

example : compile (.and_b pkA (.s pkB)) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_SWAP,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_BOOLAND] := by
  rfl
example : scriptBytesMatch (compile (.and_b pkA (.s pkB)))
    (joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes, rawBytes #[0x9a]]) = true := by
  native_decide

example : compile (.or_b pkA (.s pkB)) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_SWAP,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_BOOLOR] := by
  rfl
example : scriptBytesMatch (compile (.or_b pkA (.s pkB)))
    (joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes, rawBytes #[0x9b]]) = true := by
  native_decide

example : compile (.or_c pkA verifiedOlder) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_NOTIF,
      .pushNum 42, .op .OP_CHECKSEQUENCEVERIFY, .op .OP_VERIFY,
      .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.or_c pkA verifiedOlder))
    (joinBytes [pkABytes, rawBytes #[0x64], verifiedOlderBytes, rawBytes #[0x68]]) = true := by
  native_decide

example : compile (.or_d pkA pkB) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_IFDUP, .op .OP_NOTIF,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.or_d pkA pkB))
    (joinBytes [pkABytes, rawBytes #[0x73, 0x64], pkBBytes, rawBytes #[0x68]]) = true := by
  native_decide

example : compile (.or_i pkA pkB) =
    [.op .OP_IF, .pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_ELSE,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.or_i pkA pkB))
    (joinBytes [rawBytes #[0x63], pkABytes, rawBytes #[0x67], pkBBytes,
      rawBytes #[0x68]]) = true := by
  native_decide

example : compile (.andor pkA pkB pkC) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_NOTIF,
      .pushData oracleKeyC, .op .OP_CHECKSIG, .op .OP_ELSE,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.andor pkA pkB pkC))
    (joinBytes [pkABytes, rawBytes #[0x64], pkCBytes, rawBytes #[0x67],
      pkBBytes, rawBytes #[0x68]]) = true := by
  native_decide

/-! ## Core wrapper fixtures -/

example : compile (.a pkA) =
    [.op .OP_TOALTSTACK, .pushData oracleKeyA, .op .OP_CHECKSIG,
      .op .OP_FROMALTSTACK] := by
  rfl
example : scriptBytesMatch (compile (.a pkA))
    (joinBytes [rawBytes #[0x6b], pkABytes, rawBytes #[0x6c]]) = true := by
  native_decide

example : compile (.s pkA) =
    [.op .OP_SWAP, .pushData oracleKeyA, .op .OP_CHECKSIG] := by
  rfl
example : scriptBytesMatch (compile (.s pkA))
    (joinBytes [rawBytes #[0x7c], pkABytes]) = true := by
  native_decide

example : compile (.c (.pk_k oracleKeyA)) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG] := by
  rfl
example : scriptBytesMatch (compile (.c (.pk_k oracleKeyA))) pkABytes = true := by
  native_decide

example : compile (.d verifiedOlder) =
    [.op .OP_DUP, .op .OP_IF, .pushNum 42, .op .OP_CHECKSEQUENCEVERIFY,
      .op .OP_VERIFY, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.d verifiedOlder))
    (joinBytes [rawBytes #[0x76, 0x63], verifiedOlderBytes, rawBytes #[0x68]]) = true := by
  native_decide

example : compile verifiedOlder =
    [.pushNum 42, .op .OP_CHECKSEQUENCEVERIFY, .op .OP_VERIFY] := by
  rfl
example : scriptBytesMatch (compile verifiedOlder) verifiedOlderBytes = true := by
  native_decide

example : compile (.j pkA) =
    [.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF,
      .pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compile (.j pkA))
    (joinBytes [rawBytes #[0x82, 0x92, 0x63], pkABytes, rawBytes #[0x68]]) = true := by
  native_decide

example : compile (.n pkA) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_0NOTEQUAL] := by
  rfl
example : scriptBytesMatch (compile (.n pkA))
    (joinBytes [pkABytes, rawBytes #[0x92]]) = true := by
  native_decide

/-! ## Threshold and multisig fixtures -/

example : compile (.thresh 2 [pkA, .s pkB]) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_SWAP,
      .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_ADD,
      .pushNum 2, .op .OP_EQUAL] := by
  rfl
example : scriptBytesMatch (compile (.thresh 2 [pkA, .s pkB]))
    (joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes,
      rawBytes #[0x93, 0x52, 0x87]]) = true := by
  native_decide

example : compile (.multi 2 [oracleKeyA, oracleKeyB, oracleKeyC]) =
    [.pushNum 2, .pushData oracleKeyA, .pushData oracleKeyB, .pushData oracleKeyC,
      .pushNum 3, .op .OP_CHECKMULTISIG] := by
  rfl
example : scriptBytesMatch (compile (.multi 2 [oracleKeyA, oracleKeyB, oracleKeyC]))
    (joinBytes [rawBytes #[0x52], directPush oracleKeyA, directPush oracleKeyB,
      directPush oracleKeyC, rawBytes #[0x53, 0xae]]) = true := by
  native_decide

example : compile (.multi_a 2 [oracleXOnlyKeyA, oracleXOnlyKeyB, oracleXOnlyKeyC]) =
    [.pushData oracleXOnlyKeyA, .op .OP_CHECKSIG,
      .pushData oracleXOnlyKeyB, .op .OP_CHECKSIGADD,
      .pushData oracleXOnlyKeyC, .op .OP_CHECKSIGADD,
      .pushNum 2, .op .OP_NUMEQUAL] := by
  rfl
example : scriptBytesMatch
    (compile (.multi_a 2 [oracleXOnlyKeyA, oracleXOnlyKeyB, oracleXOnlyKeyC]))
    (joinBytes [directPush oracleXOnlyKeyA, rawBytes #[0xac],
      directPush oracleXOnlyKeyB, rawBytes #[0xba], directPush oracleXOnlyKeyC,
      rawBytes #[0xba, 0x52, 0x9c]]) = true := by
  native_decide

/-! ## Surface fixtures -/

example : compileSurface (.core .one) = [.pushNum 1] := by rfl
example : scriptBytesMatch (compileSurface (.core .one)) (rawBytes #[0x51]) = true := by
  native_decide

example : desugar (.pk oracleKeyA) = .c (.pk_k oracleKeyA) := by rfl
example : compileSurface (.pk oracleKeyA) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG] := by
  rfl
example : scriptBytesMatch (compileSurface (.pk oracleKeyA)) pkABytes = true := by
  native_decide

example : desugar (.pkh oracleKeyA) = .c (.pk_h oracleKeyA) := by rfl
example : compileSurface (.pkh oracleKeyA) =
    [.op .OP_DUP, .op .OP_HASH160, .pushData (hash160 oracleKeyA),
      .op .OP_EQUALVERIFY, .op .OP_CHECKSIG] := by
  rfl

example : compileSurfaceConcrete (.pkh oracleKeyA) =
    [.op .OP_DUP, .op .OP_HASH160,
      .pushData (LeanHash160.hash160 oracleKeyA),
      .op .OP_EQUALVERIFY, .op .OP_CHECKSIG] := by
  rfl

example : scriptBytesMatch
    (compileSurfaceConcrete (.pkh oracleKeyA))
      (joinBytes [rawBytes #[0x76, 0xa9], directPush oracleKeyAHash160,
        rawBytes #[0x88, 0xac]]) = true := by
  native_decide

example : desugar (.and_n (.pk oracleKeyA) (.pk oracleKeyB)) =
    .andor pkA pkB .zero := by
  rfl
example : compileSurface (.and_n (.pk oracleKeyA) (.pk oracleKeyB)) =
    [.pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_NOTIF, .pushNum 0,
      .op .OP_ELSE, .pushData oracleKeyB, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch
    (compileSurface (.and_n (.pk oracleKeyA) (.pk oracleKeyB)))
    (joinBytes [pkABytes, rawBytes #[0x64, 0x00, 0x67], pkBBytes,
      rawBytes #[0x68]]) = true := by
  native_decide

example : desugar (.t (.core verifiedOlder)) = .and_v verifiedOlder .one := by rfl
example : compileSurface (.t (.core verifiedOlder)) =
    [.pushNum 42, .op .OP_CHECKSEQUENCEVERIFY, .op .OP_VERIFY, .pushNum 1] := by
  rfl
example : scriptBytesMatch (compileSurface (.t (.core verifiedOlder)))
    (joinBytes [verifiedOlderBytes, rawBytes #[0x51]]) = true := by
  native_decide

example : desugar (.l (.pk oracleKeyA)) = .or_i .zero pkA := by rfl
example : compileSurface (.l (.pk oracleKeyA)) =
    [.op .OP_IF, .pushNum 0, .op .OP_ELSE,
      .pushData oracleKeyA, .op .OP_CHECKSIG, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compileSurface (.l (.pk oracleKeyA)))
    (joinBytes [rawBytes #[0x63, 0x00, 0x67], pkABytes, rawBytes #[0x68]]) = true := by
  native_decide

example : desugar (.u (.pk oracleKeyA)) = .or_i pkA .zero := by rfl
example : compileSurface (.u (.pk oracleKeyA)) =
    [.op .OP_IF, .pushData oracleKeyA, .op .OP_CHECKSIG,
      .op .OP_ELSE, .pushNum 0, .op .OP_ENDIF] := by
  rfl
example : scriptBytesMatch (compileSurface (.u (.pk oracleKeyA)))
    (joinBytes [rawBytes #[0x63], pkABytes, rawBytes #[0x67, 0x00, 0x68]]) = true := by
  native_decide

/-! ## Constructor-linked fixture matrix -/

private def keyAHex : String :=
  "02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e"

private def keyBHex : String :=
  "03b506a1dbe57b4bf48c95e0c7d417b87dd3b4349d290d2e7e9ba72c912652d80a"

private def keyCHex : String :=
  "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def xOnlyKeyAHex : String :=
  "d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e"

private def xOnlyKeyBHex : String :=
  "b506a1dbe57b4bf48c95e0c7d417b87dd3b4349d290d2e7e9ba72c912652d80a"

private def xOnlyKeyCHex : String :=
  "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def hash256Hex : String :=
  "4ae81572f06e1b88fd5ced7a1a000945432e83e1551e6f721ee9c00b8cc33260"

private def hash160Hex : String :=
  "4ae81572f06e1b88fd5ced7a1a00094543a00069"

private def keyAHash160Hex : String :=
  "9fc5dbe5efdce10374a4dd4053c93af540211718"

private def pushed (hex : String) : String := "<" ++ hex ++ ">"
private def pkAAssembly : String := pushed keyAHex ++ " CHECKSIG"
private def pkBAssembly : String := pushed keyBHex ++ " CHECKSIG"
private def pkCAssembly : String := pushed keyCHex ++ " CHECKSIG"
private def verifiedOlderAssembly : String := "42 CHECKSEQUENCEVERIFY VERIFY"

private def hashLockBytes (opcode : UInt8) (hash : ByteArray) : ByteArray :=
  joinBytes [rawBytes #[0x82, 0x01, 0x20, 0x88, opcode], directPush hash,
    rawBytes #[0x87]]

structure CoreConformanceFixture where
  tag : CoreConstructorTag
  fragment : CoreFragment
  expectedAssembly : String
  expectedBytes : ByteArray

private def CoreConformanceFixture.matches
    (fixture : CoreConformanceFixture) : Bool :=
  let script := compileConcrete fixture.fragment
  decide (fixture.fragment.constructorTag = fixture.tag) &&
    toAssembly script == fixture.expectedAssembly &&
    scriptBytesMatch script fixture.expectedBytes

def coreConformanceFixtures : List CoreConformanceFixture :=
  [
    { tag := .zero, fragment := .zero, expectedAssembly := "0",
      expectedBytes := rawBytes #[0x00] },
    { tag := .one, fragment := .one, expectedAssembly := "1",
      expectedBytes := rawBytes #[0x51] },
    { tag := .pkK, fragment := .pk_k oracleKeyA,
      expectedAssembly := pushed keyAHex, expectedBytes := directPush oracleKeyA },
    { tag := .pkH, fragment := .pk_h oracleKeyA,
      expectedAssembly := "DUP HASH160 " ++ pushed keyAHash160Hex ++ " EQUALVERIFY",
      expectedBytes := joinBytes [rawBytes #[0x76, 0xa9], directPush oracleKeyAHash160,
        rawBytes #[0x88]] },
    { tag := .older, fragment := .older 42,
      expectedAssembly := "42 CHECKSEQUENCEVERIFY",
      expectedBytes := rawBytes #[0x01, 0x2a, 0xb2] },
    { tag := .after, fragment := .after 500000000,
      expectedAssembly := "500000000 CHECKLOCKTIMEVERIFY",
      expectedBytes := rawBytes #[0x04, 0x00, 0x65, 0xcd, 0x1d, 0xb1] },
    { tag := .sha256, fragment := .sha256 oracleHash256,
      expectedAssembly := "SIZE 32 EQUALVERIFY SHA256 " ++ pushed hash256Hex ++ " EQUAL",
      expectedBytes := hashLockBytes 0xa8 oracleHash256 },
    { tag := .hash256, fragment := .hash256 oracleHash256,
      expectedAssembly := "SIZE 32 EQUALVERIFY HASH256 " ++ pushed hash256Hex ++ " EQUAL",
      expectedBytes := hashLockBytes 0xaa oracleHash256 },
    { tag := .ripemd160, fragment := .ripemd160 oracleHash160,
      expectedAssembly := "SIZE 32 EQUALVERIFY RIPEMD160 " ++ pushed hash160Hex ++ " EQUAL",
      expectedBytes := hashLockBytes 0xa6 oracleHash160 },
    { tag := .hash160, fragment := .hash160 oracleHash160,
      expectedAssembly := "SIZE 32 EQUALVERIFY HASH160 " ++ pushed hash160Hex ++ " EQUAL",
      expectedBytes := hashLockBytes 0xa9 oracleHash160 },
    { tag := .andV, fragment := .and_v verifiedOlder pkB,
      expectedAssembly := verifiedOlderAssembly ++ " " ++ pkBAssembly,
      expectedBytes := joinBytes [verifiedOlderBytes, pkBBytes] },
    { tag := .andB, fragment := .and_b pkA (.s pkB),
      expectedAssembly := pkAAssembly ++ " SWAP " ++ pkBAssembly ++ " BOOLAND",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes,
        rawBytes #[0x9a]] },
    { tag := .orB, fragment := .or_b pkA (.s pkB),
      expectedAssembly := pkAAssembly ++ " SWAP " ++ pkBAssembly ++ " BOOLOR",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes,
        rawBytes #[0x9b]] },
    { tag := .orC, fragment := .or_c pkA verifiedOlder,
      expectedAssembly := pkAAssembly ++ " NOTIF " ++ verifiedOlderAssembly ++ " ENDIF",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x64], verifiedOlderBytes,
        rawBytes #[0x68]] },
    { tag := .orD, fragment := .or_d pkA pkB,
      expectedAssembly := pkAAssembly ++ " IFDUP NOTIF " ++ pkBAssembly ++ " ENDIF",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x73, 0x64], pkBBytes,
        rawBytes #[0x68]] },
    { tag := .orI, fragment := .or_i pkA pkB,
      expectedAssembly := "IF " ++ pkAAssembly ++ " ELSE " ++ pkBAssembly ++ " ENDIF",
      expectedBytes := joinBytes [rawBytes #[0x63], pkABytes, rawBytes #[0x67],
        pkBBytes, rawBytes #[0x68]] },
    { tag := .andor, fragment := .andor pkA pkB pkC,
      expectedAssembly := pkAAssembly ++ " NOTIF " ++ pkCAssembly ++ " ELSE " ++
        pkBAssembly ++ " ENDIF",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x64], pkCBytes,
        rawBytes #[0x67], pkBBytes, rawBytes #[0x68]] },
    { tag := .a, fragment := .a pkA,
      expectedAssembly := "TOALTSTACK " ++ pkAAssembly ++ " FROMALTSTACK",
      expectedBytes := joinBytes [rawBytes #[0x6b], pkABytes, rawBytes #[0x6c]] },
    { tag := .s, fragment := .s pkA,
      expectedAssembly := "SWAP " ++ pkAAssembly,
      expectedBytes := joinBytes [rawBytes #[0x7c], pkABytes] },
    { tag := .c, fragment := .c (.pk_k oracleKeyA),
      expectedAssembly := pkAAssembly, expectedBytes := pkABytes },
    { tag := .d, fragment := .d verifiedOlder,
      expectedAssembly := "DUP IF " ++ verifiedOlderAssembly ++ " ENDIF",
      expectedBytes := joinBytes [rawBytes #[0x76, 0x63], verifiedOlderBytes,
        rawBytes #[0x68]] },
    { tag := .v, fragment := verifiedOlder,
      expectedAssembly := verifiedOlderAssembly, expectedBytes := verifiedOlderBytes },
    { tag := .j, fragment := .j pkA,
      expectedAssembly := "SIZE 0NOTEQUAL IF " ++ pkAAssembly ++ " ENDIF",
      expectedBytes := joinBytes [rawBytes #[0x82, 0x92, 0x63], pkABytes,
        rawBytes #[0x68]] },
    { tag := .n, fragment := .n pkA,
      expectedAssembly := pkAAssembly ++ " 0NOTEQUAL",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x92]] },
    { tag := .thresh, fragment := .thresh 2 [pkA, .s pkB],
      expectedAssembly := pkAAssembly ++ " SWAP " ++ pkBAssembly ++ " ADD 2 EQUAL",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x7c], pkBBytes,
        rawBytes #[0x93, 0x52, 0x87]] },
    { tag := .multi, fragment := .multi 2 [oracleKeyA, oracleKeyB, oracleKeyC],
      expectedAssembly := "2 " ++ pushed keyAHex ++ " " ++ pushed keyBHex ++
        " " ++ pushed keyCHex ++ " 3 CHECKMULTISIG",
      expectedBytes := joinBytes [rawBytes #[0x52], directPush oracleKeyA,
        directPush oracleKeyB, directPush oracleKeyC, rawBytes #[0x53, 0xae]] },
    { tag := .multiA,
      fragment := .multi_a 2 [oracleXOnlyKeyA, oracleXOnlyKeyB, oracleXOnlyKeyC],
      expectedAssembly := pushed xOnlyKeyAHex ++ " CHECKSIG " ++ pushed xOnlyKeyBHex ++
        " CHECKSIGADD " ++ pushed xOnlyKeyCHex ++ " CHECKSIGADD 2 NUMEQUAL",
      expectedBytes := joinBytes [directPush oracleXOnlyKeyA, rawBytes #[0xac],
        directPush oracleXOnlyKeyB, rawBytes #[0xba], directPush oracleXOnlyKeyC,
        rawBytes #[0xba, 0x52, 0x9c]] }
  ]

def coveredCoreConstructors : List CoreConstructorTag :=
  coreConformanceFixtures.map (·.tag)

theorem coveredCoreConstructors_complete (tag : CoreConstructorTag) :
    tag ∈ coveredCoreConstructors := by
  cases tag <;> native_decide

theorem coreConformanceFixtures_match :
    coreConformanceFixtures.all CoreConformanceFixture.matches = true := by
  native_decide

example : coreConformanceFixtures.length = 27 := by native_decide

structure SurfaceConformanceFixture where
  tag : SurfaceConstructorTag
  fragment : SurfaceFragment
  expectedAssembly : String
  expectedBytes : ByteArray

private def SurfaceConformanceFixture.matches
    (fixture : SurfaceConformanceFixture) : Bool :=
  let script := compileSurfaceConcrete fixture.fragment
  decide (fixture.fragment.constructorTag = fixture.tag) &&
    toAssembly script == fixture.expectedAssembly &&
    scriptBytesMatch script fixture.expectedBytes

def surfaceConformanceFixtures : List SurfaceConformanceFixture :=
  [
    { tag := .core, fragment := .core .one, expectedAssembly := "1",
      expectedBytes := rawBytes #[0x51] },
    { tag := .pk, fragment := .pk oracleKeyA, expectedAssembly := pkAAssembly,
      expectedBytes := pkABytes },
    { tag := .pkh, fragment := .pkh oracleKeyA,
      expectedAssembly := "DUP HASH160 " ++ pushed keyAHash160Hex ++
        " EQUALVERIFY CHECKSIG",
      expectedBytes := joinBytes [rawBytes #[0x76, 0xa9], directPush oracleKeyAHash160,
        rawBytes #[0x88, 0xac]] },
    { tag := .andN, fragment := .and_n (.pk oracleKeyA) (.pk oracleKeyB),
      expectedAssembly := pkAAssembly ++ " NOTIF 0 ELSE " ++ pkBAssembly ++ " ENDIF",
      expectedBytes := joinBytes [pkABytes, rawBytes #[0x64, 0x00, 0x67],
        pkBBytes, rawBytes #[0x68]] },
    { tag := .t, fragment := .t (.core verifiedOlder),
      expectedAssembly := verifiedOlderAssembly ++ " 1",
      expectedBytes := joinBytes [verifiedOlderBytes, rawBytes #[0x51]] },
    { tag := .l, fragment := .l (.pk oracleKeyA),
      expectedAssembly := "IF 0 ELSE " ++ pkAAssembly ++ " ENDIF",
      expectedBytes := joinBytes [rawBytes #[0x63, 0x00, 0x67], pkABytes,
        rawBytes #[0x68]] },
    { tag := .u, fragment := .u (.pk oracleKeyA),
      expectedAssembly := "IF " ++ pkAAssembly ++ " ELSE 0 ENDIF",
      expectedBytes := joinBytes [rawBytes #[0x63], pkABytes,
        rawBytes #[0x67, 0x00, 0x68]] }
  ]

def coveredSurfaceConstructors : List SurfaceConstructorTag :=
  surfaceConformanceFixtures.map (·.tag)

theorem coveredSurfaceConstructors_complete (tag : SurfaceConstructorTag) :
    tag ∈ coveredSurfaceConstructors := by
  cases tag <;> native_decide

theorem surfaceConformanceFixtures_match :
    surfaceConformanceFixtures.all SurfaceConformanceFixture.matches = true := by
  native_decide

example : surfaceConformanceFixtures.length = 7 := by native_decide

end LeanMiniscript.Miniscript
