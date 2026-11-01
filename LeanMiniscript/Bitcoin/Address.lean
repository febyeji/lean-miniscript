import LeanMiniscript.Bitcoin.KeyEncoding
import LeanMiniscript.Bitcoin.ScriptBytes

namespace LeanMiniscript.Bitcoin.Address

/-! Address decoding for `addr()` descriptors. Base58Check addresses follow
Bitcoin Core's P2PKH and P2SH version bytes, and segwit addresses follow
BIP173 (Bech32, witness version 0) and BIP350 (Bech32m, versions 1 to 16).
Mainnet, testnet/signet, and regtest encodings are all accepted because the
descriptor parser has no selected chain. -/

private def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

private def generators : List Nat :=
  [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]

private def polymod (values : List Nat) : Nat :=
  values.foldl (fun check value =>
    let top := check / 2 ^ 25
    let check := (check % 2 ^ 25) * 32 ^^^ value
    (List.range 5).foldl (fun check bit =>
      if top / 2 ^ bit % 2 == 1 then check ^^^ generators[bit]! else check) check) 1

private def hrpExpand (hrp : List Char) : List Nat :=
  hrp.map (·.toNat / 32) ++ [0] ++ hrp.map (·.toNat % 32)

inductive Bech32Variant where
  | bech32
  | bech32m
  deriving Repr, DecidableEq

/-- Split a Bech32 or Bech32m string into its lowercase human-readable part
and 5-bit data values without the six checksum values. -/
def decodeBech32 (text : String) :
    Except String (String × List Nat × Bech32Variant) := do
  let chars := text.toList
  if chars.length > 90 then throw "Bech32 string exceeds 90 characters"
  if chars.any (fun c => c.toNat < 33 || c.toNat > 126) then
    throw "Bech32 string contains a character outside US-ASCII 33..126"
  if chars.any Char.isLower && chars.any Char.isUpper then
    throw "Bech32 string mixes upper and lower case"
  let chars := chars.map Char.toLower
  let some separator := (List.range chars.length).reverse.find? (chars[·]! == '1')
    | throw "Bech32 string has no separator"
  if separator == 0 then throw "Bech32 human-readable part is empty"
  if chars.length - separator - 1 < 6 then throw "Bech32 data part is shorter than its checksum"
  let hrp := chars.take separator
  let data ← (chars.drop (separator + 1)).mapM fun c =>
    match charset.idxOf? c with
    | some value => pure value
    | none => throw "Invalid Bech32 data character"
  let variant ← match polymod (hrpExpand hrp ++ data) with
    | 1 => pure Bech32Variant.bech32
    | 0x2bc830a3 => pure Bech32Variant.bech32m
    | _ => throw "Invalid Bech32 checksum"
  return (String.ofList hrp, data.take (data.length - 6), variant)

/-- Regroup 5-bit values into bytes, rejecting more than four padding bits or
nonzero padding. -/
def fiveToEight (values : List Nat) : Except String ByteArray := do
  let mut accumulator := 0
  let mut bits := 0
  let mut bytes : Array UInt8 := #[]
  for value in values do
    accumulator := (accumulator * 32 + value) % 2 ^ 12
    bits := bits + 5
    if bits ≥ 8 then
      bits := bits - 8
      bytes := bytes.push (UInt8.ofNat (accumulator / 2 ^ bits % 256))
  if bits ≥ 5 then throw "Witness program has more than four padding bits"
  if accumulator % 2 ^ bits != 0 then throw "Witness program has nonzero padding"
  return ⟨bytes⟩

private def segwitHrps : List String := ["bc", "tb", "bcrt"]

/-- Decode a segwit address into its witness version and program. -/
def decodeSegwit (text : String) : Except String (Nat × ByteArray) := do
  let (hrp, data, variant) ← decodeBech32 text
  if !segwitHrps.contains hrp then throw "Unknown segwit address prefix"
  let version :: programValues := data | throw "Segwit address has no witness version"
  if version > 16 then throw "Witness version exceeds 16"
  let program ← fiveToEight programValues
  if program.size < 2 || program.size > 40 then
    throw "Witness program length is outside 2..40 bytes"
  if version == 0 && program.size != 20 && program.size != 32 then
    throw "Witness v0 program must contain 20 or 32 bytes"
  if (version == 0) != (variant == .bech32) then
    throw "Witness v0 uses Bech32 and later versions use Bech32m"
  return (version, program)

/-- scriptPubKey for an address: P2PKH or P2SH for Base58Check, and a
witness program for Bech32 or Bech32m. -/
def scriptPubKey (text : String) : Except String ByteArray := do
  match decodeSegwit text with
  | .ok (version, program) =>
      let opcode := if version == 0 then 0 else 0x50 + version
      return ⟨#[UInt8.ofNat opcode, UInt8.ofNat program.size]⟩ ++ program
  | .error segwitError =>
      let some separator := (text.toList.reverse.idxOf? '1')
        | legacy text
      -- A string with a known segwit prefix reports its Bech32 error.
      let hrp := String.ofList (text.toList.take (text.length - separator - 1)) |>.toLower
      if segwitHrps.contains hrp then throw segwitError
      legacy text
where
  legacy (text : String) : Except String ByteArray := do
    let payload ← KeyEncoding.decodeBase58Check text
    if payload.size != 21 then throw "Base58 address payload must contain 21 bytes"
    let hash := payload.extract 1 21
    match payload[0]! with
    | 0x00 | 0x6f => return ScriptBytes.p2pkh hash
    | 0x05 | 0xc4 => return ⟨#[0xa9, 0x14]⟩ ++ hash ++ ⟨#[0x87]⟩
    | _ => throw "Unsupported Base58 address version"

end LeanMiniscript.Bitcoin.Address
