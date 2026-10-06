import LeanMiniscript.Bitcoin.Secp256k1

namespace LeanMiniscript.Bitcoin.ECDSA

open Secp256k1

/-! Public-input ECDSA verification using the executable secp256k1 operations.
DER compatibility follows Bitcoin Core `src/pubkey.cpp` at
`9be056a8a72b624dae9623b2f7bded92c2a21c91`. Script's strict encoding and LOW_S
policy checks are separate. No curve-correctness or oracle-refinement theorem
is claimed by this executable implementation. -/

private def readLength (bytes : ByteArray) (offset : Nat) : Option (Nat × Nat) := Id.run do
  if offset ≥ bytes.size then return none
  let first := bytes[offset]!.toNat
  if first < 128 then return some (first, offset + 1)
  let mut count := first - 128
  let mut pos := offset + 1
  if count > bytes.size - pos then return none
  for _ in [:count] do
    if bytes[pos]! == 0 then
      pos := pos + 1
      count := count - 1
    else break
  -- Core fixes this bound at four bytes, independently of host size_t.
  if count ≥ 4 then return none
  let length := decodeBE (bytes.extract pos (pos + count))
  return some (length, pos + count)

/-- Core's permissive DER parser. Sequence lengths and trailing bytes do not
constrain R/S; leading zeros and high sign bits are accepted. Scalar overflow
produces the invalid pair (0,0), as Core's compact-parser fallback does. -/
def parseLaxDER (bytes : ByteArray) : Option (Nat × Nat) := do
  if bytes.size < 2 || bytes[0]! != 0x30 then none else do
    let sequenceLength := bytes[1]!.toNat
    let pos := 2 + if sequenceLength ≥ 128 then sequenceLength - 128 else 0
    if pos ≥ bytes.size || bytes[pos]! != 0x02 then none else do
      let (rLength, rPos) ← readLength bytes (pos + 1)
      if rLength > bytes.size - rPos then none else do
        let sTag := rPos + rLength
        if sTag ≥ bytes.size || bytes[sTag]! != 0x02 then none else do
          let (sLength, sPos) ← readLength bytes (sTag + 1)
          if sLength > bytes.size - sPos then none else do
            let rBytes := (bytes.extract rPos (rPos + rLength)).data.toList.dropWhile (· == 0)
            let sBytes := (bytes.extract sPos (sPos + sLength)).data.toList.dropWhile (· == 0)
            if rBytes.length > 32 || sBytes.length > 32 then return (0, 0)
            let r := decodeBE ⟨rBytes.toArray⟩
            let s := decodeBE ⟨sBytes.toArray⟩
            if r ≥ order || s ≥ order then return (0, 0)
            return (r, s)

/-- Parse compressed, uncompressed or parity-consistent hybrid public keys.
Strict Script policy can reject hybrid encodings before reaching this parser. -/
def parsePublicKey (bytes : ByteArray) : Point :=
  if bytes.size == 33 && (bytes[0]! == 2 || bytes[0]! == 3) then
    match liftX (decodeBE (bytes.extract 1 33)) with
    | none => none
    | some (x, y) => some (x, if bytes[0]! == 2 then y else field - y)
  else if bytes.size == 65 && (bytes[0]! == 4 || bytes[0]! == 6 || bytes[0]! == 7) then
    let x := decodeBE (bytes.extract 1 33)
    let y := decodeBE (bytes.extract 33 65)
    if x ≥ field || y ≥ field || y * y % field != (x * x % field * x + 7) % field then none
    else if bytes[0]! != 4 && y % 2 != bytes[0]!.toNat % 2 then none
    else some (x, y)
  else none

/-- Verify a DER signature without its Script hash-type byte against a 32-byte
digest. Both high and low S verify; LOW_S is enforced at the Script boundary. -/
def verify (signature publicKey digest : ByteArray) : Bool :=
  if digest.size != 32 then false
  else match parseLaxDER signature, parsePublicKey publicKey with
  | some (r, s), some point =>
      if r == 0 || s == 0 then false
      else
        let inverse := powMod s (order - 2) order
        let u₁ := decodeBE digest * inverse % order
        let u₂ := r * inverse % order
        match pointAdd (pointMul generator u₁) (pointMul (some point) u₂) with
        | none => false
        | some (x, _) => x % order == r
  | _, _ => false

end LeanMiniscript.Bitcoin.ECDSA
