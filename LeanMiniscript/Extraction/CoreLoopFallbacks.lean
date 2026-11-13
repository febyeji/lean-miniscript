import LeanMiniscript.Extraction.ScriptEquivalence

/-!
# Instructions that sent a script to Core's raw loop

`coreLoopFallbacks` lists the kinds of instruction that once left a script
without a typed reading, so that `executeTypedScript` ran it on Core's raw
loop: each opcode byte whose one-instruction script had none, a truncated push,
and a nonminimal push, each with a name and a representative script. Every
byte string now has a typed reading (`runsOnCoreLoop_eq_false`), and
`executeTypedScript` no longer runs Core's raw loop.

`scripts/core_loop_fallbacks.lean` prints how many representatives still run
on Core's raw loop. It fails when the list misses a push kind or an opcode
byte whose one-instruction script runs there, lists a kind twice, or has a
representative of another kind, and when one of the nine script equivalence
obligations lacks a proof.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- The one-instruction script of an opcode byte. A push opcode pushes as
many zero bytes as it encodes minimally: 0x01–0x4b push that many,
OP_PUSHDATA1 76, OP_PUSHDATA2 256, and OP_PUSHDATA4 65,536. OP_0 and the
other bytes stand alone. -/
def oneInstructionScript (byte : UInt8) : ByteArray :=
  let value := byte.toNat
  let push (sizePrefix : Array UInt8) (size : Nat) : ByteArray :=
    ⟨#[byte] ++ sizePrefix ++ Array.replicate size 0⟩
  if value == 0 || value > 0x4e then ⟨#[byte]⟩
  else if value ≤ 0x4b then push #[] value
  else if value == 0x4c then push #[76] 76
  else if value == 0x4d then push #[0x00, 0x01] 256
  else push #[0x00, 0x00, 0x01, 0x00] 65536

/-- The bytes have no typed reading. -/
def runsOnCoreLoop (bytes : ByteArray) : Bool :=
  (decodeTypedScript? bytes).isNone

theorem runsOnCoreLoop_eq_false (bytes : ByteArray) : runsOnCoreLoop bytes = false := by
  simp [runsOnCoreLoop, decodeTypedScript?_eq]

/-- A kind of instruction that can leave a script without a typed reading. -/
inductive CoreLoopFallbackKind where
  /-- The one-instruction script of this opcode byte. -/
  | opcode (byte : UInt8)
  /-- A push whose length prefix or data runs past the end of the script. -/
  | truncatedPush
  /-- A complete push that does not use the shortest encoding of its data. -/
  | nonminimalPush
  deriving DecidableEq, Repr

/-- A kind with its name and representative script. -/
structure CoreLoopFallback where
  kind : CoreLoopFallbackKind
  name : String
  bytes : ByteArray

/-- The representative script has the entry's kind: the opcode byte's
one-instruction script, a push opcode whose length prefix or data is cut off,
or one nonminimal push and nothing after it. -/
def CoreLoopFallback.hasKind (fallback : CoreLoopFallback) : Bool :=
  let isPush := fallback.bytes.size > 0 && fallback.bytes[0]!.toNat ≤ 0x4e
  match fallback.kind, readCoreRawInstruction fallback.bytes 0 with
  | .opcode byte, _ => fallback.bytes == oneInstructionScript byte
  | .truncatedPush, .error _ => isPush
  | .truncatedPush, .ok _ => false
  | .nonminimalPush, .error _ => false
  | .nonminimalPush, .ok instruction =>
      isPush && instruction.nextOffset == fallback.bytes.size &&
        !coreLegacyMinimalPush instruction.opcode.toNat instruction.payload

/-- The 94 kinds: the 92 opcode bytes whose one-instruction script had no
typed reading when the list was made, a one-byte push without its byte, and a
one-byte push of 0x05, which OP_5 encodes minimally. -/
def coreLoopFallbacks : List CoreLoopFallback := [
  ⟨.truncatedPush, "truncated push", ⟨#[0x01]⟩⟩,
  ⟨.nonminimalPush, "nonminimal push", ⟨#[0x01, 0x05]⟩⟩,
  ⟨.opcode 0x50, "OP_RESERVED", ⟨#[0x50]⟩⟩,
  ⟨.opcode 0x62, "OP_VER", ⟨#[0x62]⟩⟩,
  ⟨.opcode 0x65, "OP_VERIF", ⟨#[0x65]⟩⟩,
  ⟨.opcode 0x66, "OP_VERNOTIF", ⟨#[0x66]⟩⟩,
  ⟨.opcode 0x7e, "OP_CAT", ⟨#[0x7e]⟩⟩,
  ⟨.opcode 0x7f, "OP_SUBSTR", ⟨#[0x7f]⟩⟩,
  ⟨.opcode 0x80, "OP_LEFT", ⟨#[0x80]⟩⟩,
  ⟨.opcode 0x81, "OP_RIGHT", ⟨#[0x81]⟩⟩,
  ⟨.opcode 0x83, "OP_INVERT", ⟨#[0x83]⟩⟩,
  ⟨.opcode 0x84, "OP_AND", ⟨#[0x84]⟩⟩,
  ⟨.opcode 0x85, "OP_OR", ⟨#[0x85]⟩⟩,
  ⟨.opcode 0x86, "OP_XOR", ⟨#[0x86]⟩⟩,
  ⟨.opcode 0x89, "OP_RESERVED1", ⟨#[0x89]⟩⟩,
  ⟨.opcode 0x8a, "OP_RESERVED2", ⟨#[0x8a]⟩⟩,
  ⟨.opcode 0x8d, "OP_2MUL", ⟨#[0x8d]⟩⟩,
  ⟨.opcode 0x8e, "OP_2DIV", ⟨#[0x8e]⟩⟩,
  ⟨.opcode 0x95, "OP_MUL", ⟨#[0x95]⟩⟩,
  ⟨.opcode 0x96, "OP_DIV", ⟨#[0x96]⟩⟩,
  ⟨.opcode 0x97, "OP_MOD", ⟨#[0x97]⟩⟩,
  ⟨.opcode 0x98, "OP_LSHIFT", ⟨#[0x98]⟩⟩,
  ⟨.opcode 0x99, "OP_RSHIFT", ⟨#[0x99]⟩⟩,
  ⟨.opcode 0xa7, "OP_SHA1", ⟨#[0xa7]⟩⟩,
  ⟨.opcode 0xab, "OP_CODESEPARATOR", ⟨#[0xab]⟩⟩,
  ⟨.opcode 0xbb, "OP_UNKNOWN_0xbb", ⟨#[0xbb]⟩⟩,
  ⟨.opcode 0xbc, "OP_UNKNOWN_0xbc", ⟨#[0xbc]⟩⟩,
  ⟨.opcode 0xbd, "OP_UNKNOWN_0xbd", ⟨#[0xbd]⟩⟩,
  ⟨.opcode 0xbe, "OP_UNKNOWN_0xbe", ⟨#[0xbe]⟩⟩,
  ⟨.opcode 0xbf, "OP_UNKNOWN_0xbf", ⟨#[0xbf]⟩⟩,
  ⟨.opcode 0xc0, "OP_UNKNOWN_0xc0", ⟨#[0xc0]⟩⟩,
  ⟨.opcode 0xc1, "OP_UNKNOWN_0xc1", ⟨#[0xc1]⟩⟩,
  ⟨.opcode 0xc2, "OP_UNKNOWN_0xc2", ⟨#[0xc2]⟩⟩,
  ⟨.opcode 0xc3, "OP_UNKNOWN_0xc3", ⟨#[0xc3]⟩⟩,
  ⟨.opcode 0xc4, "OP_UNKNOWN_0xc4", ⟨#[0xc4]⟩⟩,
  ⟨.opcode 0xc5, "OP_UNKNOWN_0xc5", ⟨#[0xc5]⟩⟩,
  ⟨.opcode 0xc6, "OP_UNKNOWN_0xc6", ⟨#[0xc6]⟩⟩,
  ⟨.opcode 0xc7, "OP_UNKNOWN_0xc7", ⟨#[0xc7]⟩⟩,
  ⟨.opcode 0xc8, "OP_UNKNOWN_0xc8", ⟨#[0xc8]⟩⟩,
  ⟨.opcode 0xc9, "OP_UNKNOWN_0xc9", ⟨#[0xc9]⟩⟩,
  ⟨.opcode 0xca, "OP_UNKNOWN_0xca", ⟨#[0xca]⟩⟩,
  ⟨.opcode 0xcb, "OP_UNKNOWN_0xcb", ⟨#[0xcb]⟩⟩,
  ⟨.opcode 0xcc, "OP_UNKNOWN_0xcc", ⟨#[0xcc]⟩⟩,
  ⟨.opcode 0xcd, "OP_UNKNOWN_0xcd", ⟨#[0xcd]⟩⟩,
  ⟨.opcode 0xce, "OP_UNKNOWN_0xce", ⟨#[0xce]⟩⟩,
  ⟨.opcode 0xcf, "OP_UNKNOWN_0xcf", ⟨#[0xcf]⟩⟩,
  ⟨.opcode 0xd0, "OP_UNKNOWN_0xd0", ⟨#[0xd0]⟩⟩,
  ⟨.opcode 0xd1, "OP_UNKNOWN_0xd1", ⟨#[0xd1]⟩⟩,
  ⟨.opcode 0xd2, "OP_UNKNOWN_0xd2", ⟨#[0xd2]⟩⟩,
  ⟨.opcode 0xd3, "OP_UNKNOWN_0xd3", ⟨#[0xd3]⟩⟩,
  ⟨.opcode 0xd4, "OP_UNKNOWN_0xd4", ⟨#[0xd4]⟩⟩,
  ⟨.opcode 0xd5, "OP_UNKNOWN_0xd5", ⟨#[0xd5]⟩⟩,
  ⟨.opcode 0xd6, "OP_UNKNOWN_0xd6", ⟨#[0xd6]⟩⟩,
  ⟨.opcode 0xd7, "OP_UNKNOWN_0xd7", ⟨#[0xd7]⟩⟩,
  ⟨.opcode 0xd8, "OP_UNKNOWN_0xd8", ⟨#[0xd8]⟩⟩,
  ⟨.opcode 0xd9, "OP_UNKNOWN_0xd9", ⟨#[0xd9]⟩⟩,
  ⟨.opcode 0xda, "OP_UNKNOWN_0xda", ⟨#[0xda]⟩⟩,
  ⟨.opcode 0xdb, "OP_UNKNOWN_0xdb", ⟨#[0xdb]⟩⟩,
  ⟨.opcode 0xdc, "OP_UNKNOWN_0xdc", ⟨#[0xdc]⟩⟩,
  ⟨.opcode 0xdd, "OP_UNKNOWN_0xdd", ⟨#[0xdd]⟩⟩,
  ⟨.opcode 0xde, "OP_UNKNOWN_0xde", ⟨#[0xde]⟩⟩,
  ⟨.opcode 0xdf, "OP_UNKNOWN_0xdf", ⟨#[0xdf]⟩⟩,
  ⟨.opcode 0xe0, "OP_UNKNOWN_0xe0", ⟨#[0xe0]⟩⟩,
  ⟨.opcode 0xe1, "OP_UNKNOWN_0xe1", ⟨#[0xe1]⟩⟩,
  ⟨.opcode 0xe2, "OP_UNKNOWN_0xe2", ⟨#[0xe2]⟩⟩,
  ⟨.opcode 0xe3, "OP_UNKNOWN_0xe3", ⟨#[0xe3]⟩⟩,
  ⟨.opcode 0xe4, "OP_UNKNOWN_0xe4", ⟨#[0xe4]⟩⟩,
  ⟨.opcode 0xe5, "OP_UNKNOWN_0xe5", ⟨#[0xe5]⟩⟩,
  ⟨.opcode 0xe6, "OP_UNKNOWN_0xe6", ⟨#[0xe6]⟩⟩,
  ⟨.opcode 0xe7, "OP_UNKNOWN_0xe7", ⟨#[0xe7]⟩⟩,
  ⟨.opcode 0xe8, "OP_UNKNOWN_0xe8", ⟨#[0xe8]⟩⟩,
  ⟨.opcode 0xe9, "OP_UNKNOWN_0xe9", ⟨#[0xe9]⟩⟩,
  ⟨.opcode 0xea, "OP_UNKNOWN_0xea", ⟨#[0xea]⟩⟩,
  ⟨.opcode 0xeb, "OP_UNKNOWN_0xeb", ⟨#[0xeb]⟩⟩,
  ⟨.opcode 0xec, "OP_UNKNOWN_0xec", ⟨#[0xec]⟩⟩,
  ⟨.opcode 0xed, "OP_UNKNOWN_0xed", ⟨#[0xed]⟩⟩,
  ⟨.opcode 0xee, "OP_UNKNOWN_0xee", ⟨#[0xee]⟩⟩,
  ⟨.opcode 0xef, "OP_UNKNOWN_0xef", ⟨#[0xef]⟩⟩,
  ⟨.opcode 0xf0, "OP_UNKNOWN_0xf0", ⟨#[0xf0]⟩⟩,
  ⟨.opcode 0xf1, "OP_UNKNOWN_0xf1", ⟨#[0xf1]⟩⟩,
  ⟨.opcode 0xf2, "OP_UNKNOWN_0xf2", ⟨#[0xf2]⟩⟩,
  ⟨.opcode 0xf3, "OP_UNKNOWN_0xf3", ⟨#[0xf3]⟩⟩,
  ⟨.opcode 0xf4, "OP_UNKNOWN_0xf4", ⟨#[0xf4]⟩⟩,
  ⟨.opcode 0xf5, "OP_UNKNOWN_0xf5", ⟨#[0xf5]⟩⟩,
  ⟨.opcode 0xf6, "OP_UNKNOWN_0xf6", ⟨#[0xf6]⟩⟩,
  ⟨.opcode 0xf7, "OP_UNKNOWN_0xf7", ⟨#[0xf7]⟩⟩,
  ⟨.opcode 0xf8, "OP_UNKNOWN_0xf8", ⟨#[0xf8]⟩⟩,
  ⟨.opcode 0xf9, "OP_UNKNOWN_0xf9", ⟨#[0xf9]⟩⟩,
  ⟨.opcode 0xfa, "OP_UNKNOWN_0xfa", ⟨#[0xfa]⟩⟩,
  ⟨.opcode 0xfb, "OP_UNKNOWN_0xfb", ⟨#[0xfb]⟩⟩,
  ⟨.opcode 0xfc, "OP_UNKNOWN_0xfc", ⟨#[0xfc]⟩⟩,
  ⟨.opcode 0xfd, "OP_UNKNOWN_0xfd", ⟨#[0xfd]⟩⟩,
  ⟨.opcode 0xfe, "OP_UNKNOWN_0xfe", ⟨#[0xfe]⟩⟩,
  ⟨.opcode 0xff, "OP_INVALIDOPCODE", ⟨#[0xff]⟩⟩
]

end LeanMiniscript.Extraction
