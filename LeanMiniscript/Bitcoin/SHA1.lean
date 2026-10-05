import LeanHash160.Internal

namespace LeanMiniscript.Bitcoin.SHA1

/-! Executable SHA-1 for Bitcoin's OP_SHA1. Compression and padding follow
FIPS 180-4 and the pinned Core `src/crypto/sha1.cpp` implementation. -/

private def initial : Array UInt32 :=
  #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

private def compress (state : Array UInt32) (bytes : ByteArray) (offset : Nat) :
    Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := Array.replicate 80 0
  for i in [0:16] do
    schedule := schedule.set! i (LeanHash160.Internal.readUInt32 .big bytes (offset + 4 * i))
  for i in [16:80] do
    schedule := schedule.set! i (LeanHash160.Internal.rotateLeft32
      (schedule[i - 3]! ^^^ schedule[i - 8]! ^^^ schedule[i - 14]! ^^^ schedule[i - 16]!) 1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  for i in [0:80] do
    let (f, k) := if i < 20 then
        ((b &&& c) ||| ((b ^^^ 0xffffffff) &&& d), (0x5a827999 : UInt32))
      else if i < 40 then (b ^^^ c ^^^ d, 0x6ed9eba1)
      else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8f1bbcdc)
      else (b ^^^ c ^^^ d, 0xca62c1d6)
    let next := LeanHash160.Internal.rotateLeft32 a 5 + f + e + k + schedule[i]!
    e := d
    d := c
    c := LeanHash160.Internal.rotateLeft32 b 30
    b := a
    a := next
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d, state[4]! + e]

/-- Compute a 20-byte SHA-1 digest using the message's exact byte encoding. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let padded := LeanHash160.Internal.padMessage .big bytes
  let mut state := initial
  for block in [0:padded.size / 64] do
    state := compress state padded (block * 64)
  return state.foldl (LeanHash160.Internal.appendUInt32 .big) ByteArray.empty

end LeanMiniscript.Bitcoin.SHA1
