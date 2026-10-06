import Lean

namespace LeanMiniscript.Bitcoin.DescriptorChecksum

/-! BIP380 descriptor checksums over the exact input text. Character expansion
and polynomial constants follow BIP380 and Bitcoin Core's DescriptorChecksum.
These functions validate the checksum envelope; descriptor grammar is checked
by the descriptor parser. -/

private def inputCharset : List Char :=
  "0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ".toList

private def checksumCharset : Array Char :=
  "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList.toArray

private def generators : Array UInt64 :=
  #[0xf5dee51989, 0xa9fdca3312, 0x1bab10e32d, 0x3706b1677a, 0x644d626ffd]

private def polymod (state value : UInt64) : UInt64 := Id.run do
  let top := state >>> 35
  let mut next := ((state &&& 0x7ffffffff) <<< 5) ^^^ value
  for i in [:5] do
    if (top >>> UInt64.ofNat i) &&& 1 != 0 then
      next := next ^^^ generators[i]!
  return next

/-- Calculate the eight checksum characters for a BIP380 payload. This does
not parse descriptor grammar or remove an existing checksum. -/
def checksum (body : String) : Except String String := do
  let mut state : UInt64 := 1
  let mut group : UInt64 := 0
  let mut groupSize : Nat := 0
  for character in body.toList do
    let some position := inputCharset.idxOf? character
      | throw "descriptor payload contains a character outside the BIP380 charset"
    state := polymod state (UInt64.ofNat (position % 32))
    group := 3 * group + UInt64.ofNat (position / 32)
    groupSize := groupSize + 1
    if groupSize == 3 then
      state := polymod state group
      group := 0
      groupSize := 0
  if groupSize != 0 then
    state := polymod state group
  for _ in [:8] do
    state := polymod state 0
  state := state ^^^ 1
  let mut result := ""
  for i in [:8] do
    let index := ((state >>> UInt64.ofNat (5 * (7 - i))) &&& 31).toNat
    result := result.push checksumCharset[index]!
  return result

/-- Append a checksum to a descriptor body without a checksum separator. -/
def addChecksum (body : String) : Except String String := do
  if body.contains '#' then
    throw "descriptor body already contains a checksum separator"
  return body ++ "#" ++ (← checksum body)

/-- Validate the original descriptor text and return its body. A present
checksum must be valid even when `requireChecksum` is false. The payload
charset is checked for descriptors that omit the optional checksum as well. -/
def validate (input : String) (requireChecksum : Bool := false) : Except String String := do
  match input.splitOn "#" with
  | [body] =>
      let _ ← checksum body
      if requireChecksum then
        throw "descriptor checksum is required"
      return body
  | [body, supplied] =>
      if supplied.length != 8 then
        throw "descriptor checksum must contain exactly eight characters"
      if !supplied.toList.all (fun character => checksumCharset.contains character) then
        throw "descriptor checksum contains an invalid character"
      let expected ← checksum body
      if supplied != expected then
        throw "descriptor checksum mismatch"
      return body
  | _ => throw "descriptor contains multiple checksum separators"

end LeanMiniscript.Bitcoin.DescriptorChecksum
