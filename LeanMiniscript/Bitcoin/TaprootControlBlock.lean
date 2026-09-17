import LeanMiniscript.Bitcoin.Secp256k1
import LeanMiniscript.Bitcoin.TaprootSighash

namespace LeanMiniscript.Bitcoin
open Secp256k1

inductive TaprootControlError where
  | controlSize
  | internalKey
  | tweakSize
  | tweakRange
  | infiniteOutput
  | outputKeySize
  | commitmentMismatch
  deriving Repr, DecidableEq, BEq

/-- Exact Core error tags for consensus commitment failures. Helper-only byte
shape errors use MODEL tags, outside Core's already-fixed 32-byte boundary. -/
def TaprootControlError.coreTag : TaprootControlError → String
  | .controlSize => "TAPROOT_WRONG_CONTROL_SIZE"
  | .tweakSize => "MODEL_TAPROOT_TWEAK_SIZE"
  | .outputKeySize => "MODEL_TAPROOT_OUTPUT_KEY_SIZE"
  | _ => "WITNESS_PROGRAM_MISMATCH"

structure TaprootControlBlock where
  leafVersion : UInt8
  outputParity : Bool
  internalKey : ByteArray
  merklePath : List ByteArray
  deriving Repr

/-- Parse the 33 + 32*m byte control block, with 0 ≤ m ≤ 128. -/
def parseTaprootControlBlock (bytes : ByteArray) : Except TaprootControlError TaprootControlBlock :=
  if bytes.size < 33 || bytes.size > 4129 || (bytes.size - 33) % 32 ≠ 0 then
    .error .controlSize
  else .ok {
    leafVersion := bytes[0]! &&& 0xfe
    outputParity := (bytes[0]! &&& 1) == 1
    internalKey := bytes.extract 1 33
    merklePath := (List.range ((bytes.size - 33) / 32)).map
      (fun i => bytes.extract (33 + 32 * i) (65 + 32 * i)) }

/-- TapBranch hash of two 32-byte hashes, sorted in byte lexicographic order.
For fixed-size hashes, their big-endian numeric order is identical. -/
def tapbranchHash (a b : ByteArray) : ByteArray :=
  taggedHash "TapBranch" (if decodeBE a < decodeBE b then a ++ b else b ++ a)

def taprootControlMerkleRoot (control : TaprootControlBlock) (leafHash : ByteArray) : ByteArray :=
  control.merklePath.foldl tapbranchHash leafHash

/-- Public-input x-only key tweaking. Reject, rather than reduce, tweaks ≥ n;
reject invalid internal keys and an infinity result. No curve proof is claimed. -/
def taprootTweakPoint (internalKey tweak : ByteArray) : Except TaprootControlError (Nat × Nat) := do
  if internalKey.size ≠ 32 then throw .internalKey
  if tweak.size ≠ 32 then throw .tweakSize
  let scalar := decodeBE tweak
  if scalar ≥ order then throw .tweakRange
  let point ← match liftX (decodeBE internalKey) with
    | none => throw .internalKey
    | some point => pure point
  match pointAdd (some point) (pointMul generator scalar) with
  | none => throw .infiniteOutput
  | some result => pure result

structure TaprootCommitment where
  leafVersion : UInt8
  leafHash : ByteArray
  merkleRoot : ByteArray
  deriving Repr

/-- Verify the script's commitment to a 32-byte Taproot output key. All leaf
versions are hashed using the masked control byte; executing future versions
is separate from this commitment check. Coverage is by official vectors, not
a general proof of BIP341 or curve correctness. -/
def verifyTaprootControlBlock (outputKey scriptBytes controlBytes : ByteArray) :
    Except TaprootControlError TaprootCommitment := do
  let control ← parseTaprootControlBlock controlBytes
  if outputKey.size ≠ 32 then throw .outputKeySize
  let leafHash := tapleafHash scriptBytes control.leafVersion
  let root := taprootControlMerkleRoot control leafHash
  let (x, y) ← taprootTweakPoint control.internalKey
    (taggedHash "TapTweak" (control.internalKey ++ root))
  if x ≠ decodeBE outputKey || (y % 2 == 1) != control.outputParity then
    throw .commitmentMismatch
  return { leafVersion := control.leafVersion, leafHash := leafHash, merkleRoot := root }

end LeanMiniscript.Bitcoin
