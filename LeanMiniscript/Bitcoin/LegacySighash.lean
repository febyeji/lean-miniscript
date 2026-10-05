import LeanHash160
import LeanMiniscript.Bitcoin.Transaction

namespace LeanMiniscript.Bitcoin

/-! Executable legacy and BIP143 signing hashes. Callers supply the script
suffix after the last executed CODESEPARATOR and, for BASE, remove all
relevant signatures with FindAndDelete before calling. -/

inductive LegacySighashError where
  | inputIndex
  | outpointHashSize
  deriving Repr, DecidableEq, BEq

def doubleSHA256 (bytes : ByteArray) : ByteArray :=
  LeanHash160.SHA256.hash (LeanHash160.SHA256.hash bytes)

private def littleEndian (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte value => byte.toNat + 256 * value) 0

/-- GetOp's success and cursor, including the cursor left by a malformed push. -/
private def scriptOpEnd (bytes : ByteArray) (offset : Nat) : Bool × Nat := Id.run do
  if offset ≥ bytes.size then return (false, offset)
  let opcode := bytes[offset]!.toNat
  let pos := offset + 1
  if opcode > 0x4e then return (true, pos)
  let width := if opcode < 0x4c then 0 else if opcode == 0x4c then 1
    else if opcode == 0x4d then 2 else 4
  if width > bytes.size - pos then return (false, pos)
  let length := if width == 0 then opcode else littleEndian (bytes.extract pos (pos + width))
  let payload := pos + width
  if length > bytes.size - payload then return (false, payload)
  return (true, payload + length)

private def stripCodeSeparators : Nat → ByteArray → Nat → Nat → ByteArray → Nat × ByteArray
  | 0, _, _, removed, output => (removed, output)
  | fuel + 1, bytes, offset, removed, output =>
      if offset ≥ bytes.size then (removed, output)
      else
        let (valid, next) := scriptOpEnd bytes offset
        if !valid then (removed, output ++ bytes.extract offset next)
        else if bytes[offset]! == 0xab then
          stripCodeSeparators fuel bytes next (removed + 1) output
        else stripCodeSeparators fuel bytes next removed (output ++ bytes.extract offset next)

/-- Core's BASE scriptCode serialization removes separator opcodes at opcode
boundaries. Its declared length retains a malformed suffix's original size,
while emitted bytes stop at the failed GetOp cursor, matching Core's serializer. -/
def serializeLegacyScriptCode (script : ByteArray) : ByteArray :=
  let (removed, bytes) := stripCodeSeparators (script.size + 1) script 0 0 ByteArray.empty
  ⟨(compactSize (script.size - removed)).toArray⟩ ++ bytes

private def validateLegacyTransaction (tx : Transaction) (inputIndex : Nat) :
    Except LegacySighashError Unit :=
  if inputIndex ≥ tx.inputs.size then .error .inputIndex
  else if tx.inputs.any (fun input => input.previousOutput.txid.size != 32) then
    .error .outpointHashSize
  else .ok ()

/-- Legacy signing digest, with all 32 hash-type bits serialized. Undefined
base types behave as ALL. SINGLE without a matching output returns uint256::ONE
in wire order, preserving the historical consensus behavior. -/
def legacySignatureHash (tx : Transaction) (inputIndex : Nat) (scriptCode : ByteArray)
    (hashType : UInt32) : Except LegacySighashError ByteArray := do
  validateLegacyTransaction tx inputIndex
  let kind := hashType.toNat % 32
  if kind == 3 && inputIndex ≥ tx.outputs.size then
    return ⟨(1 :: List.replicate 31 0).toArray⟩
  let anyone := hashType &&& 0x80 != 0
  let indices := if anyone then [inputIndex] else List.range tx.inputs.size
  let inputs := indices.foldl (fun bytes index =>
    let input := tx.inputs[index]!
    let script := if index == inputIndex then serializeLegacyScriptCode scriptCode else ⟨#[0]⟩
    let sequence := if index != inputIndex && (kind == 2 || kind == 3) then 0
      else input.sequence.toNat
    bytes ++ serializeOutPoint input.previousOutput ++ script ++
      ⟨(unsignedLE 4 sequence).toArray⟩) ByteArray.empty
  let outputCount := if kind == 2 then 0 else if kind == 3 then inputIndex + 1
    else tx.outputs.size
  let outputs := (List.range outputCount).foldl (fun bytes index =>
    let output := if kind == 3 && index != inputIndex then
      { amount := 0xffffffffffffffff, scriptPubKey := ByteArray.empty : TxOutput }
      else tx.outputs[index]!
    bytes ++ serializeTxOutput output) ByteArray.empty
  let message := ⟨(unsignedLE 4 tx.version.toNat ++ compactSize indices.length).toArray⟩ ++
    inputs ++ ⟨(compactSize outputCount).toArray⟩ ++ outputs ++
    ⟨(unsignedLE 4 tx.locktime.toNat ++ unsignedLE 4 hashType.toNat).toArray⟩
  return doubleSHA256 message

/-- BIP143 signing digest. The supplied amount is committed in every mode;
scriptCode retains all separator bytes after the last executed separator.
SINGLE with no matching output commits a zero hashOutputs. -/
def witnessV0SignatureHash (tx : Transaction) (inputIndex : Nat) (scriptCode : ByteArray)
    (amount : UInt64) (hashType : UInt32) : Except LegacySighashError ByteArray := do
  validateLegacyTransaction tx inputIndex
  let kind := hashType.toNat % 32
  let anyone := hashType &&& 0x80 != 0
  let zero : ByteArray := ⟨(List.replicate 32 0).toArray⟩
  let prevouts := if anyone then zero else doubleSHA256
    (tx.inputs.foldl (fun bytes input => bytes ++ serializeOutPoint input.previousOutput) ByteArray.empty)
  let sequences := if anyone || kind == 2 || kind == 3 then zero else doubleSHA256
    (tx.inputs.foldl (fun bytes input => bytes ++ ⟨(unsignedLE 4 input.sequence.toNat).toArray⟩) ByteArray.empty)
  let outputs := if kind != 2 && kind != 3 then doubleSHA256
    (tx.outputs.foldl (fun bytes output => bytes ++ serializeTxOutput output) ByteArray.empty)
    else if kind == 3 && inputIndex < tx.outputs.size then
      doubleSHA256 (serializeTxOutput tx.outputs[inputIndex]!) else zero
  let input := tx.inputs[inputIndex]!
  let message := ⟨(unsignedLE 4 tx.version.toNat).toArray⟩ ++ prevouts ++ sequences ++
    serializeOutPoint input.previousOutput ++ serializeByteVector scriptCode ++
    ⟨(unsignedLE 8 amount.toNat ++ unsignedLE 4 input.sequence.toNat).toArray⟩ ++
    outputs ++ ⟨(unsignedLE 4 tx.locktime.toNat ++ unsignedLE 4 hashType.toNat).toArray⟩
  return doubleSHA256 message

end LeanMiniscript.Bitcoin
