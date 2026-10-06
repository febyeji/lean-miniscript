import Lean

namespace LeanMiniscript.Bitcoin.SHA512

/-! Executable SHA-512 and HMAC-SHA512 for BIP32. Compression and padding
follow FIPS 180-4; HMAC follows RFC 2104 with a 128-byte block. -/

private def initial : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

private def constants : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

private def rotateRight (word amount : UInt64) : UInt64 :=
  (word >>> amount) ||| (word <<< (64 - amount))

private def readWord (bytes : ByteArray) (offset : Nat) : UInt64 := Id.run do
  let mut word : UInt64 := 0
  for i in [:8] do
    word := (word <<< 8) ||| bytes[offset + i]!.toUInt64
  return word

private def compress (state : Array UInt64) (bytes : ByteArray) (offset : Nat) :
    Array UInt64 := Id.run do
  let mut words : Array UInt64 := Array.replicate 80 0
  for i in [:16] do
    words := words.set! i (readWord bytes (offset + 8 * i))
  for i in [16:80] do
    let a := words[i - 15]!
    let b := words[i - 2]!
    let σ₀ := rotateRight a 1 ^^^ rotateRight a 8 ^^^ (a >>> 7)
    let σ₁ := rotateRight b 19 ^^^ rotateRight b 61 ^^^ (b >>> 6)
    words := words.set! i (words[i - 16]! + σ₀ + words[i - 7]! + σ₁)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [:80] do
    let sigma1 := rotateRight e 14 ^^^ rotateRight e 18 ^^^ rotateRight e 41
    let choose := (e &&& f) ^^^ ((e ^^^ 0xffffffffffffffff) &&& g)
    let t₁ := h + sigma1 + choose + constants[i]! + words[i]!
    let sigma0 := rotateRight a 28 ^^^ rotateRight a 34 ^^^ rotateRight a 39
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t₂ := sigma0 + majority
    h := g
    g := f
    f := e
    e := d + t₁
    d := c
    c := b
    b := a
    a := t₁ + t₂
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- SHA-512 with the FIPS 180-4 128-bit big-endian bit length. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let mut padded := bytes.push 0x80
  let zeroCount := (112 + 128 - padded.size % 128) % 128
  for _ in [:zeroCount] do padded := padded.push 0
  let bitLength := bytes.size * 8
  for i in [:16] do
    padded := padded.push (UInt8.ofNat (bitLength / 256 ^ (15 - i)))
  let mut state := initial
  for block in [:padded.size / 128] do
    state := compress state padded (block * 128)
  let mut result := ByteArray.empty
  for word in state do
    for i in [:8] do
      result := result.push ((word >>> UInt64.ofNat (8 * (7 - i))).toUInt8)
  return result

/-- HMAC-SHA512, including hashing keys longer than the 128-byte block. -/
def hmac (key message : ByteArray) : ByteArray := Id.run do
  let key := if key.size > 128 then hash key else key
  let mut inner := ByteArray.empty
  let mut outer := ByteArray.empty
  for i in [:128] do
    let byte := if i < key.size then key[i]! else 0
    inner := inner.push (byte ^^^ 0x36)
    outer := outer.push (byte ^^^ 0x5c)
  return hash (outer ++ hash (inner ++ message))

end LeanMiniscript.Bitcoin.SHA512
