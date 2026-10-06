import LeanHash160
import LeanMiniscript.Bitcoin.Secp256k1

namespace LeanMiniscript.Bitcoin.KeyEncoding

/-! Strict Bitcoin key encodings for descriptor resolution. Base58 input uses
the exact alphabet without surrounding whitespace. Secret-key multiplication
uses the executable affine implementation and has no constant-time guarantee. -/

private def alphabet : List Char :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList

private def base58Digits (value : Nat) : List Char :=
  if value = 0 then []
  else alphabet[value % 58]! :: base58Digits (value / 58)
termination_by value
decreasing_by omega

private def base256Digits (value : Nat) : List UInt8 :=
  if value = 0 then []
  else UInt8.ofNat (value % 256) :: base256Digits (value / 256)
termination_by value
decreasing_by omega

/-- Base58 encoding preserves each leading zero byte as a leading `1`. -/
def encodeBase58 (bytes : ByteArray) : String :=
  let leading := (bytes.data.toList.takeWhile (· == 0)).length
  String.ofList (List.replicate leading '1' ++
    (base58Digits (Secp256k1.decodeBE bytes)).reverse)

/-- Decode the exact Base58 alphabet, including leading zero bytes. -/
def decodeBase58 (text : String) : Except String ByteArray := do
  let mut value := 0
  for character in text.toList do
    let some digit := alphabet.idxOf? character
      | throw "Invalid Base58 character"
    value := value * 58 + digit
  let leading := (text.toList.takeWhile (· == '1')).length
  return ⟨(List.replicate leading 0 ++ (base256Digits value).reverse).toArray⟩

private def checksum (payload : ByteArray) : ByteArray :=
  (LeanHash160.SHA256.hash (LeanHash160.SHA256.hash payload)).extract 0 4

/-- Append the first four bytes of double SHA256, then encode with Base58. -/
def encodeBase58Check (payload : ByteArray) : String :=
  encodeBase58 (payload ++ checksum payload)

/-- Verify the four-byte checksum and return the version-bearing payload. -/
def decodeBase58Check (text : String) : Except String ByteArray := do
  let bytes ← decodeBase58 text
  if bytes.size < 4 then throw "Base58Check input is shorter than its checksum"
  let payload := bytes.extract 0 (bytes.size - 4)
  if bytes.extract (bytes.size - 4) bytes.size != checksum payload then
    throw "Invalid Base58Check checksum"
  return payload

/-- Testnet, signet and regtest share the testnet key-version bytes. -/
inductive Network where
  | mainnet
  | testnet
  deriving Repr, DecidableEq, BEq

structure WIF where
  network : Network
  secret : ByteArray
  compressed : Bool

/-- A secp256k1 secret is exactly 32 bytes and an integer in `[1, order)`. -/
def validateSecret (secret : ByteArray) : Bool :=
  secret.size == 32 && Secp256k1.decodeBE secret > 0 &&
    Secp256k1.decodeBE secret < Secp256k1.order

/-- Decode mainnet/testnet WIF and enforce its scalar and compression marker. -/
def decodeWIF (text : String) : Except String WIF := do
  let payload ← decodeBase58Check text
  if payload.size != 33 && payload.size != 34 then
    throw "WIF payload must contain a version and a 32-byte secret"
  let network ← if payload[0]! == 0x80 then pure Network.mainnet
    else if payload[0]! == 0xef then pure Network.testnet
    else throw "Unsupported WIF network version"
  let compressed := payload.size == 34
  if compressed && payload[33]! != 1 then throw "Invalid WIF compression marker"
  let secret := payload.extract 1 33
  if !validateSecret secret then throw "WIF secret is outside the secp256k1 scalar range"
  return { network, secret, compressed }

private def encodeBE32 (value : Nat) : ByteArray :=
  ⟨((List.range 32).map (fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256))).toArray⟩

/-- Derive a SEC public key from a validated secret scalar. This executable
implementation does not provide constant-time secret handling. -/
def publicKeyFromSecret (secret : ByteArray) (compressed : Bool := true) :
    Except String ByteArray := do
  if !validateSecret secret then throw "Secret is outside the secp256k1 scalar range"
  let some (x, y) := Secp256k1.pointMul Secp256k1.generator (Secp256k1.decodeBE secret)
    | throw "Secret produced the point at infinity"
  if compressed then return ⟨#[UInt8.ofNat (2 + y % 2)]⟩ ++ encodeBE32 x
  else return ⟨#[4]⟩ ++ encodeBE32 x ++ encodeBE32 y

/-- Strict SEC validation checks canonical coordinates and curve membership.
Only compressed `02`/`03` and uncompressed `04` encodings are accepted. -/
def validatePublicKey (bytes : ByteArray) : Bool :=
  if bytes.size == 33 && (bytes[0]! == 2 || bytes[0]! == 3) then
    (Secp256k1.liftX (Secp256k1.decodeBE (bytes.extract 1 33))).isSome
  else if bytes.size == 65 && bytes[0]! == 4 then
    let x := Secp256k1.decodeBE (bytes.extract 1 33)
    let y := Secp256k1.decodeBE (bytes.extract 33 65)
    x < Secp256k1.field && y < Secp256k1.field &&
      y * y % Secp256k1.field == (x * x % Secp256k1.field * x + 7) % Secp256k1.field
  else false

end LeanMiniscript.Bitcoin.KeyEncoding
