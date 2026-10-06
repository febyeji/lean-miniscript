import LeanMiniscript.Bitcoin.KeyEncoding
import LeanMiniscript.Bitcoin.SHA512
import LeanMiniscript.Bitcoin.ECDSA

namespace LeanMiniscript.Bitcoin.BIP32

/-! Executable BIP32 import, serialization and exact-index key derivation.
All entry points validate caller-constructed keys. Invalid child derivations
return an error so descriptor indices never silently change. The affine
curve operations have no constant-time guarantee or cryptographic proof. -/

inductive KeyMaterial where
  | secret (bytes : ByteArray)
  | publicKey (bytes : ByteArray)

structure ExtendedKey where
  network : KeyEncoding.Network
  depth : Nat
  parentFingerprint : ByteArray
  childNumber : Nat
  chainCode : ByteArray
  material : KeyMaterial

def ExtendedKey.isPrivate (key : ExtendedKey) : Bool :=
  match key.material with
  | .secret _ => true
  | .publicKey _ => false

private def encodeBE (size value : Nat) : ByteArray :=
  ⟨((List.range size).map
    (fun index => UInt8.ofNat (value / 256 ^ (size - 1 - index) % 256))).toArray⟩

private def validate (key : ExtendedKey) : Except String Unit := do
  if key.depth > 255 then throw "BIP32 depth exceeds one byte"
  if key.parentFingerprint.size != 4 then throw "BIP32 parent fingerprint must contain four bytes"
  if key.childNumber ≥ 0x100000000 then throw "BIP32 child number exceeds uint32"
  if key.depth == 0 &&
      (Secp256k1.decodeBE key.parentFingerprint != 0 || key.childNumber != 0) then
    throw "BIP32 master keys require zero parent fingerprint and child number"
  if key.chainCode.size != 32 then throw "BIP32 chain code must contain 32 bytes"
  match key.material with
  | .secret bytes =>
      if !KeyEncoding.validateSecret bytes then throw "Invalid BIP32 secret scalar"
  | .publicKey bytes =>
      if bytes.size != 33 || !KeyEncoding.validatePublicKey bytes then
        throw "BIP32 public keys require a compressed secp256k1 point"

private def rawPublicKey (key : ExtendedKey) : Except String ByteArray :=
  match key.material with
  | .secret bytes => KeyEncoding.publicKeyFromSecret bytes
  | .publicKey bytes => pure bytes

/-- The compressed public key belonging to a validated extended key. -/
def publicKey (key : ExtendedKey) : Except String ByteArray := do
  validate key
  rawPublicKey key

/-- Import xprv/xpub/tprv/tpub with checksum, metadata and key validation. -/
def parse (text : String) : Except String ExtendedKey := do
  let bytes ← KeyEncoding.decodeBase58Check text
  if bytes.size != 78 then throw "BIP32 payload must contain exactly 78 bytes"
  let version := Secp256k1.decodeBE (bytes.extract 0 4)
  let (network, secret) ←
    if version == 0x0488ade4 then pure (KeyEncoding.Network.mainnet, true)
    else if version == 0x0488b21e then pure (KeyEncoding.Network.mainnet, false)
    else if version == 0x04358394 then pure (KeyEncoding.Network.testnet, true)
    else if version == 0x043587cf then pure (KeyEncoding.Network.testnet, false)
    else throw "Unsupported BIP32 network or key version"
  let material ← if secret then do
      if bytes[45]! != 0 then throw "BIP32 private key data requires the zero prefix"
      pure (KeyMaterial.secret (bytes.extract 46 78))
    else pure (KeyMaterial.publicKey (bytes.extract 45 78))
  let key : ExtendedKey := {
    network, depth := bytes[4]!.toNat,
    parentFingerprint := bytes.extract 5 9,
    childNumber := Secp256k1.decodeBE (bytes.extract 9 13),
    chainCode := bytes.extract 13 45, material }
  validate key
  return key

/-- Serialize a validated extended key with the BIP32 network version. -/
def serialize (key : ExtendedKey) : Except String String := do
  validate key
  let version := match key.network, key.isPrivate with
    | .mainnet, true => 0x0488ade4
    | .mainnet, false => 0x0488b21e
    | .testnet, true => 0x04358394
    | .testnet, false => 0x043587cf
  let material := match key.material with
    | .secret bytes => ⟨#[0]⟩ ++ bytes
    | .publicKey bytes => bytes
  return KeyEncoding.encodeBase58Check
    (encodeBE 4 version ++ ⟨#[UInt8.ofNat key.depth]⟩ ++ key.parentFingerprint ++
      encodeBE 4 key.childNumber ++ key.chainCode ++ material)

/-- Remove secret key material, preserving the BIP32 metadata and chain code. -/
def neuter (key : ExtendedKey) : Except String ExtendedKey := do
  let bytes ← publicKey key
  return { key with material := .publicKey bytes }

/-- Create a BIP32 master private key from a 128-to-512-bit seed. -/
def fromSeed (seed : ByteArray) (network : KeyEncoding.Network := .mainnet) :
    Except String ExtendedKey := do
  if seed.size < 16 || seed.size > 64 then throw "BIP32 seed must contain 16 to 64 bytes"
  let digest := SHA512.hmac "Bitcoin seed".toUTF8 seed
  let key : ExtendedKey := {
    network, depth := 0, parentFingerprint := ⟨#[0, 0, 0, 0]⟩,
    childNumber := 0, chainCode := digest.extract 32 64,
    material := .secret (digest.extract 0 32) }
  validate key
  return key

/-- Derive precisely the requested uint32 child. Hardened indices are at least
`0x80000000`; a public parent cannot derive them. A depth-255 parent and the
rare invalid-child cases return errors without advancing to another index. -/
def deriveChild (key : ExtendedKey) (index : Nat) : Except String ExtendedKey := do
  validate key
  if index ≥ 0x100000000 then throw "BIP32 child index exceeds uint32"
  if key.depth == 255 then throw "BIP32 child depth exceeds one byte"
  let hardened := index ≥ 0x80000000
  let pub ← rawPublicKey key
  let data ← if hardened then
      match key.material with
      | .secret bytes => pure (⟨#[0]⟩ ++ bytes)
      | .publicKey _ => throw "Cannot derive a hardened BIP32 child from a public key"
    else pure pub
  let digest := SHA512.hmac key.chainCode (data ++ encodeBE 4 index)
  let tweak := Secp256k1.decodeBE (digest.extract 0 32)
  if tweak ≥ Secp256k1.order then throw "Invalid BIP32 child: tweak exceeds the curve order"
  let material ← match key.material with
    | .secret bytes => do
        let scalar := (tweak + Secp256k1.decodeBE bytes) % Secp256k1.order
        if scalar == 0 then throw "Invalid BIP32 child: zero secret"
        pure (KeyMaterial.secret (encodeBE 32 scalar))
    | .publicKey bytes => do
        let some point := ECDSA.parsePublicKey bytes
          | throw "Invalid BIP32 public parent"
        let some (x, y) := Secp256k1.pointAdd
            (Secp256k1.pointMul Secp256k1.generator tweak) (some point)
          | throw "Invalid BIP32 child: point at infinity"
        pure (KeyMaterial.publicKey (⟨#[UInt8.ofNat (2 + y % 2)]⟩ ++ encodeBE 32 x))
  return {
    network := key.network, depth := key.depth + 1,
    parentFingerprint := (LeanHash160.hash160 pub).extract 0 4,
    childNumber := index, chainCode := digest.extract 32 64, material }

/-- Derive a sequence of exact child indices, validating even an empty path. -/
def derivePath (key : ExtendedKey) (indices : List Nat) : Except String ExtendedKey := do
  validate key
  indices.foldlM deriveChild key

end LeanMiniscript.Bitcoin.BIP32
