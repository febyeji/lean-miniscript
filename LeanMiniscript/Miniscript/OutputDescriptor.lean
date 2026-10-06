import LeanMiniscript.Bitcoin.KeyEncoding
import LeanMiniscript.Bitcoin.TaprootControlBlock
import LeanMiniscript.Miniscript.Checked
import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Miniscript.Malleability
import LeanMiniscript.Script.Codec.Serialization

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Bitcoin

/-- An explicitly grouped Taproot script tree. Each leaf is a Tapscript
Miniscript expression with leaf version `0xc0`. -/
inductive DescriptorTree where
  | leaf (fragment : SurfaceFragment)
  | branch (left right : DescriptorTree)
  deriving Repr

/-- Supported output wrappers after resolving descriptor keys. -/
inductive OutputDescriptor where
  | wsh (fragment : SurfaceFragment)
  | shWsh (fragment : SurfaceFragment)
  | tr (internalKey : PubKey) (tree : Option DescriptorTree)
  deriving Repr

/-- Output bytes and scripts committed to by a descriptor. A Taproot result
retains the output key and optional tree root; spending data is a separate API. -/
structure CompiledDescriptor where
  scriptPubKey : ByteArray
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  taprootOutputKey : Option ByteArray := none
  taprootMerkleRoot : Option ByteArray := none
  deriving Repr

private def validCurveKey (ctx : ScriptContext) (key : PubKey) : Bool :=
  match ctx with
  | .p2wsh => key.size == 33 && KeyEncoding.validatePublicKey key.bytes
  | .tapscript => key.size == 32 &&
      (Secp256k1.liftX (Secp256k1.decodeBE key.bytes)).isSome

private def compileDescriptorFragment (ctx : ScriptContext)
    (fragment : SurfaceFragment) : Except String ByteArray := do
  let some checked := CheckedSurfaceFragment.ofRaw? ctx fragment
    | throw "Descriptor fragment must be well-formed and typed in its script context"
  if checked.ty.base != .B then
    throw "Descriptor fragment must have Miniscript base type B"
  if !(desugar fragment).keys.all (validCurveKey ctx) then
    throw "Descriptor fragment contains an invalid curve point"
  match LeanMiniscript.Script.serializeScript (compileSurfaceConcrete fragment) with
  | .ok bytes => return bytes
  | .error _ => throw "Descriptor script cannot be serialized"

private def descriptorTreeRoot : Nat → DescriptorTree → Except String ByteArray
  | _, .leaf fragment => do
      return tapleafHash (← compileDescriptorFragment .tapscript fragment) 0xc0
  | 0, .branch _ _ => .error "Taproot tree exceeds 128 branch levels"
  | remaining + 1, .branch left right => do
      let leftHash ← descriptorTreeRoot remaining left
      let rightHash ← descriptorTreeRoot remaining right
      return tapbranchHash leftHash rightHash

private def descriptorInternalKey (key : PubKey) : Except String ByteArray := do
  if key.size == 32 then
    if (Secp256k1.liftX (Secp256k1.decodeBE key.bytes)).isNone then
      throw "Invalid Taproot internal key"
    return key.bytes
  if key.size == 33 && KeyEncoding.validatePublicKey key.bytes then
    return key.bytes.extract 1 33
  throw "Taproot internal key must be a valid x-only or compressed public key"

private def encodeOutputX (x : Nat) : ByteArray :=
  ⟨(List.range 32).toArray.map (fun i => UInt8.ofNat (x / 256 ^ (31 - i)))⟩

/-- Compile P2WSH, P2SH-P2WSH, or P2TR output bytes. Raw AST inputs are checked
for context, correctness type B, and curve membership. Taproot preserves the
given tree grouping and permits at most 128 branches on each leaf path.
These checks do not establish wallet policy or cryptographic correctness. -/
def compileOutputDescriptor (descriptor : OutputDescriptor) :
    Except String CompiledDescriptor := do
  match descriptor with
  | .wsh fragment | .shWsh fragment =>
      let witnessScript ← compileDescriptorFragment .p2wsh fragment
      let program := ByteArray.mk #[0x00, 0x20] ++ LeanHash160.SHA256.hash witnessScript
      match descriptor with
      | .shWsh _ =>
          return {
            scriptPubKey := ByteArray.mk #[0xa9, 0x14] ++
              LeanHash160.hash160 program ++ ByteArray.mk #[0x87]
            redeemScript := some program
            witnessScript := some witnessScript }
      | _ => return { scriptPubKey := program, witnessScript := some witnessScript }
  | .tr internalKey tree =>
      let internalBytes ← descriptorInternalKey internalKey
      let root ← match tree with
        | none => pure none
        | some tree => some <$> descriptorTreeRoot 128 tree
      let tweak := taggedHash "TapTweak" (internalBytes ++ root.getD ByteArray.empty)
      let point ← match taprootTweakPoint internalBytes tweak with
        | .ok point => pure point
        | .error _ => throw "Taproot tweak is out of range or produces an infinite point"
      let outputKey := encodeOutputX point.1
      return {
        scriptPubKey := ByteArray.mk #[0x51, 0x20] ++ outputKey
        taprootOutputKey := some outputKey
        taprootMerkleRoot := root }

end LeanMiniscript.Miniscript
