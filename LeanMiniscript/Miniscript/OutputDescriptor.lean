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

/-- Source leaves in descriptor order, retaining repeated occurrences. -/
def DescriptorTree.fragments : DescriptorTree → List SurfaceFragment
  | .leaf fragment => [fragment]
  | .branch left right => left.fragments ++ right.fragments

/-- Supported output wrappers after resolving descriptor keys.

The legacy forms use the same B-typed Miniscript fragments as P2WSH for
script-hash spends.  Raw scripts remain available as an explicit byte
boundary, while the single-key and P2WPKH forms are represented directly so
their key encoding rules can follow Bitcoin Core's descriptor rules. -/
inductive OutputDescriptor where
  | raw (script : ByteArray)
  | shRaw (script : ByteArray)
  | pk (key : PubKey)
  | multi (threshold : Nat) (keys : List PubKey)
  | pkh (key : PubKey)
  | wpkh (key : PubKey)
  | shWpkh (key : PubKey)
  | sh (fragment : SurfaceFragment)
  | wsh (fragment : SurfaceFragment)
  | shWsh (fragment : SurfaceFragment)
  | tr (internalKey : PubKey) (tree : Option DescriptorTree)
  deriving Repr

/-- One compiled leaf occurrence with its original surface expression.
Siblings run from the leaf toward the root. -/
structure DescriptorLeafInfo where
  fragment : SurfaceFragment
  script : ByteArray
  merklePath : List ByteArray := []
  deriving Repr

/-- A checked tree's root and leaves in left-to-right descriptor order.
Repeated scripts retain one entry for each occurrence in the tree. -/
structure DescriptorTreeInfo where
  merkleRoot : ByteArray
  leaves : List DescriptorLeafInfo
  deriving Repr

/-- Add a parent branch's sibling after the leaf's existing path. -/
def DescriptorLeafInfo.withSibling (leaf : DescriptorLeafInfo)
    (sibling : ByteArray) : DescriptorLeafInfo :=
  { leaf with merklePath := leaf.merklePath ++ [sibling] }

/-- Combine checked subtrees while retaining their leaf order and multiplicity. -/
def DescriptorTreeInfo.branch (left right : DescriptorTreeInfo) : DescriptorTreeInfo :=
  { merkleRoot := tapbranchHash left.merkleRoot right.merkleRoot
    leaves := left.leaves.map (·.withSibling right.merkleRoot) ++
      right.leaves.map (·.withSibling left.merkleRoot) }

/-- A version-0xc0 leaf occurrence and its serialized control block.
The script and control block are the final two script-path witness items
when no annex is present; the satisfaction stack is supplied separately. -/
structure TaprootLeafSpendInfo extends DescriptorLeafInfo where
  controlBlock : ByteArray
  deriving Repr

/-- Serialize spending data for a compiled leaf with a validated 32-byte
internal key, the tweaked output's parity, and at most 128 sibling hashes. -/
def DescriptorLeafInfo.spendInfo (leaf : DescriptorLeafInfo)
    (internalKey : ByteArray) (outputParity : Bool) : TaprootLeafSpendInfo :=
  { toDescriptorLeafInfo := leaf
    controlBlock := leaf.merklePath.foldl (· ++ ·)
      (ByteArray.mk #[if outputParity then 0xc1 else 0xc0] ++ internalKey) }

/-- Output bytes and scripts committed to by a descriptor. Taproot leaves
include script-path spending data in left-to-right order, including duplicates.
Key-only Taproot and WSH descriptors have no Taproot leaf entries. -/
structure CompiledDescriptor where
  scriptPubKey : ByteArray
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  taprootOutputKey : Option ByteArray := none
  taprootMerkleRoot : Option ByteArray := none
  taprootLeaves : List TaprootLeafSpendInfo := []
  deriving Repr

private def validCurveKey (ctx : ScriptContext) (key : PubKey) : Bool :=
  match ctx with
  | .p2wsh => key.size == 33 && KeyEncoding.validatePublicKey key.bytes
  | .tapscript => key.size == 32 &&
      (Secp256k1.liftX (Secp256k1.decodeBE key.bytes)).isSome

private def validLegacyKey (key : PubKey) : Bool :=
  KeyEncoding.validatePublicKey key.bytes

private def legacyPushData (data : ByteArray) : ByteArray :=
  if data.size < 76 then ⟨#[UInt8.ofNat data.size]⟩ ++ data
  else if data.size < 256 then ⟨#[0x4c, UInt8.ofNat data.size]⟩ ++ data
  else ⟨#[0x4d] ++ (unsignedLE 2 data.size).toArray⟩ ++ data

private def legacyP2sh (script : ByteArray) : ByteArray :=
  ⟨#[0xa9, 0x14]⟩ ++ LeanHash160.hash160 script ++ ⟨#[0x87]⟩

private def legacyP2pkh (key : PubKey) : ByteArray :=
  ⟨#[0x76, 0xa9, 0x14]⟩ ++ LeanHash160.hash160 key.bytes ++ ⟨#[0x88, 0xac]⟩

private def legacyP2pk (key : PubKey) : ByteArray :=
  legacyPushData key.bytes ++ ⟨#[0xac]⟩

private def witnessP2wpkh (key : PubKey) : ByteArray :=
  ⟨#[0x00, 0x14]⟩ ++ LeanHash160.hash160 key.bytes

/-- Validate a descriptor leaf and serialize its concrete compilation. -/
def compileDescriptorFragment (ctx : ScriptContext)
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

/-- Legacy descriptor scripts permit uncompressed SEC keys in `pk`, `pkh`,
and `multi`. Other fragments use the existing P2WSH typing boundary and are
executed with BASE signature hashing by the legacy finalizer. -/
def compileLegacyDescriptorFragment (fragment : SurfaceFragment) : Except String ByteArray := do
  match fragment with
  | .pk key | .pkh key =>
      if !validLegacyKey key then throw "Legacy descriptor key is not a valid SEC public key"
  | .core (.multi threshold keys) =>
      if threshold == 0 || threshold > keys.length || keys.length > 20 then
        throw "Invalid legacy multisig threshold or key count"
      if !keys.all validLegacyKey then throw "Legacy multisig contains an invalid SEC public key"
  | _ => return ← compileDescriptorFragment .p2wsh fragment
  (LeanMiniscript.Script.serializeScript (compileSurfaceConcrete fragment)).mapError
    (fun _ => "Legacy descriptor script cannot be serialized")

/-- Compile leaves and build their Merkle paths. The depth budget counts
branches, so a single leaf uses zero. Output descriptors use a budget of 128. -/
def DescriptorTree.compile (tree : DescriptorTree) (maxDepth : Nat := 128) :
    Except String DescriptorTreeInfo :=
  match tree, maxDepth with
  | .leaf fragment, _ => do
      let script ← compileDescriptorFragment .tapscript fragment
      return { merkleRoot := tapleafHash script 0xc0, leaves := [{ fragment, script }] }
  | .branch _ _, 0 => .error "Taproot tree exceeds the branch depth budget"
  | .branch left right, remaining + 1 => do
      let leftInfo ← left.compile remaining
      let rightInfo ← right.compile remaining
      return leftInfo.branch rightInfo

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

/-- Compile legacy, P2WPKH, P2WSH, P2SH, or P2TR output bytes. Raw AST inputs
are checked for context, correctness type B, and curve membership. Taproot
preserves the given tree grouping and permits at most 128 branches on each
leaf path. These checks do not establish wallet policy or cryptographic
correctness. -/
def compileOutputDescriptor (descriptor : OutputDescriptor) :
    Except String CompiledDescriptor := do
  match descriptor with
  | .raw script =>
      return { scriptPubKey := script }
  | .shRaw script =>
      if script.size > 520 then throw "P2SH redeem script exceeds 520 bytes"
      return { scriptPubKey := legacyP2sh script, redeemScript := some script }
  | .pk key =>
      if !validLegacyKey key then throw "Legacy descriptor key is not a valid SEC public key"
      return { scriptPubKey := legacyP2pk key }
  | .pkh key =>
      if !validLegacyKey key then throw "Legacy descriptor key is not a valid SEC public key"
      return { scriptPubKey := legacyP2pkh key }
  | .wpkh key =>
      if key.size != 33 || !KeyEncoding.validatePublicKey key.bytes then
        throw "wpkh requires a valid compressed public key"
      return { scriptPubKey := witnessP2wpkh key }
  | .shWpkh key =>
      if key.size != 33 || !KeyEncoding.validatePublicKey key.bytes then
        throw "sh(wpkh) requires a valid compressed public key"
      let program := witnessP2wpkh key
      return { scriptPubKey := legacyP2sh program
               redeemScript := some program }
  | .multi threshold keys =>
      if keys.length > 3 then throw "Bare multisig descriptors allow at most three keys"
      return { scriptPubKey := ← compileLegacyDescriptorFragment (.core (.multi threshold keys)) }
  | .sh fragment =>
      let redeemScript ← compileLegacyDescriptorFragment fragment
      if redeemScript.size > 520 then throw "P2SH redeem script exceeds 520 bytes"
      return { scriptPubKey := legacyP2sh redeemScript
               redeemScript := some redeemScript }
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
      let treeInfo ← match tree with
        | none => pure none
        | some tree => some <$> tree.compile
      let root := treeInfo.map (·.merkleRoot)
      let tweak := taggedHash "TapTweak" (internalBytes ++ root.getD ByteArray.empty)
      let point ← match taprootTweakPoint internalBytes tweak with
        | .ok point => pure point
        | .error _ => throw "Taproot tweak is out of range or produces an infinite point"
      let outputKey := encodeOutputX point.1
      return {
        scriptPubKey := ByteArray.mk #[0x51, 0x20] ++ outputKey
        taprootOutputKey := some outputKey
        taprootMerkleRoot := root
        taprootLeaves := (treeInfo.toList.flatMap (·.leaves)).map
          (·.spendInfo internalBytes (point.2 % 2 == 1)) }

end LeanMiniscript.Miniscript
