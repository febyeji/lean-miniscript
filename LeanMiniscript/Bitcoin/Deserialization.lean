import LeanMiniscript.Bitcoin.LegacySighash

namespace LeanMiniscript.Bitcoin

/-! Executable readers for Bitcoin wire encodings. Readers consume a byte list
and return the unread suffix. CompactSize reading rejects non-minimal forms,
matching Core's `ReadCompactSize`; Core's 32 MiB range check on vector lengths
is not modeled. Transaction parsing follows Core's `UnserializeTransaction`,
including its witness marker, flag and superfluous-witness checks. -/

inductive DecodeError where
  | truncated
  | nonCanonicalCompactSize
  | unknownTransactionFlags
  | superfluousWitness
  | trailingData
  deriving Repr, DecidableEq

abbrev Decoder (α : Type) := List UInt8 → Except DecodeError (α × List UInt8)

/-- Little-endian unsigned integer of all supplied bytes. -/
def decodeLE : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest

/-- Split exactly `count` bytes from the front. -/
def takeExact (count : Nat) : Decoder (List UInt8) := fun bytes =>
  if count ≤ bytes.length then .ok (bytes.take count, bytes.drop count)
  else .error .truncated

/-- Read a canonical CompactSize. Wider encodings of values that fit in a
shorter form are rejected. -/
def readCompactSize : Decoder Nat
  | [] => .error .truncated
  | tag :: rest =>
      if tag.toNat < 253 then .ok (tag.toNat, rest)
      else
        let width := if tag.toNat = 253 then 2 else if tag.toNat = 254 then 4 else 8
        let minimum := if tag.toNat = 253 then 253
          else if tag.toNat = 254 then 65536 else 4294967296
        match takeExact width rest with
        | .error error => .error error
        | .ok (bytes, rest) =>
            if decodeLE bytes < minimum then .error .nonCanonicalCompactSize
            else .ok (decodeLE bytes, rest)

/-- Encoding of a length-prefixed byte vector, as a byte list. -/
def encodeByteVector (bytes : ByteArray) : List UInt8 :=
  compactSize bytes.size ++ bytes.data.toList

/-- A CompactSize length followed by that many bytes. -/
def readByteVector : Decoder ByteArray := fun bytes =>
  match readCompactSize bytes with
  | .error error => .error error
  | .ok (count, rest) =>
      match takeExact count rest with
      | .error error => .error error
      | .ok (data, rest) => .ok (⟨data.toArray⟩, rest)

def readUInt32 : Decoder UInt32 := fun bytes => do
  let (data, rest) ← takeExact 4 bytes
  return (UInt32.ofNat (decodeLE data), rest)

def readUInt64 : Decoder UInt64 := fun bytes => do
  let (data, rest) ← takeExact 8 bytes
  return (UInt64.ofNat (decodeLE data), rest)

/-- Read `count` items with one decoder. -/
def readMany {α : Type} (decoder : Decoder α) : Nat → Decoder (List α)
  | 0, bytes => .ok ([], bytes)
  | count + 1, bytes => do
      let (item, rest) ← decoder bytes
      let (items, rest) ← readMany decoder count rest
      return (item :: items, rest)

/-- Require that a decoder consumes its entire input. -/
def decodeAll {α : Type} (decoder : Decoder α) (bytes : ByteArray) : Except DecodeError α := do
  let (value, rest) ← decoder bytes.data.toList
  if rest.isEmpty then return value else throw .trailingData

def readOutPoint : Decoder OutPoint := fun bytes => do
  let (txid, rest) ← takeExact 32 bytes
  let (index, rest) ← readUInt32 rest
  return ({ txid := ⟨txid.toArray⟩, index }, rest)

def readTxInput : Decoder TxInput := fun bytes => do
  let (previousOutput, rest) ← readOutPoint bytes
  let (scriptSig, rest) ← readByteVector rest
  let (sequence, rest) ← readUInt32 rest
  return ({ previousOutput, scriptSig, sequence }, rest)

def readTxOutput : Decoder TxOutput := fun bytes => do
  let (amount, rest) ← readUInt64 bytes
  let (scriptPubKey, rest) ← readByteVector rest
  return ({ amount, scriptPubKey }, rest)

/-- One input's witness stack: an item count and length-prefixed items. -/
def readWitnessStack : Decoder (List ByteArray) := fun bytes => do
  let (count, rest) ← readCompactSize bytes
  readMany readByteVector count rest

/-- A transaction together with its per-input witness stacks. Stacks are
empty for non-witness serialization. -/
structure WitnessTransaction where
  transaction : Transaction
  witnesses : List (List ByteArray)
  deriving Repr, Inhabited

/-- Core's transaction reader. With `allowWitness`, an empty input vector is
read as the BIP144 marker and a flag byte follows; flag bit 0 selects witness
stacks and any other bit is rejected. A zero flag ends both vectors, as in
Core. A witness flag with only empty stacks is rejected as superfluous.
Without `allowWitness`, an empty input vector is an ordinary zero-input
transaction. -/
def readTransaction (allowWitness : Bool) : Decoder WitnessTransaction := fun bytes => do
  let (version, rest) ← readUInt32 bytes
  let (inputCount, rest) ← readCompactSize rest
  let (flags, inputs, outputs, rest) ← do
    if inputCount = 0 ∧ allowWitness then
      let (flag, rest) ← takeExact 1 rest
      let flag := decodeLE flag
      if flag = 0 then
        -- Core reads a zero flag as an empty input and output vector.
        pure (0, [], [], rest)
      else
        let (inputCount, rest) ← readCompactSize rest
        let (inputs, rest) ← readMany readTxInput inputCount rest
        let (outputCount, rest) ← readCompactSize rest
        let (outputs, rest) ← readMany readTxOutput outputCount rest
        pure (flag, inputs, outputs, rest)
    else
      let (inputs, rest) ← readMany readTxInput inputCount rest
      let (outputCount, rest) ← readCompactSize rest
      let (outputs, rest) ← readMany readTxOutput outputCount rest
      pure (0, inputs, outputs, rest)
  let (witnesses, rest) ← do
    if flags % 2 = 1 then
      let (witnesses, rest) ← readMany readWitnessStack inputs.length rest
      if witnesses.all List.isEmpty then throw .superfluousWitness
      pure (witnesses, rest)
    else pure (inputs.map (fun _ => []), rest)
  if flags / 2 ≠ 0 then throw .unknownTransactionFlags
  let (locktime, rest) ← readUInt32 rest
  return ({ transaction := { version, inputs := inputs.toArray, outputs := outputs.toArray, locktime }
            witnesses }, rest)

/-- Parse a complete transaction byte string. -/
def parseTransaction (bytes : ByteArray) (allowWitness : Bool := true) :
    Except DecodeError WitnessTransaction :=
  decodeAll (readTransaction allowWitness) bytes

/-- Transaction identifier bytes in wire order. -/
def Transaction.txid (tx : Transaction) : ByteArray :=
  doubleSHA256 (serializeTransaction tx)

/-- BIP144 serialization. The marker and flag are emitted only when some
witness stack is nonempty, as in Core; otherwise this is the legacy form.
Missing stacks are treated as empty. -/
def serializeWitnessTransaction (tx : Transaction) (witnesses : List (List ByteArray)) : ByteArray :=
  if witnesses.all List.isEmpty then serializeTransaction tx
  else
    ⟨(unsignedLE 4 tx.version.toNat ++ [0, 1] ++ compactSize tx.inputs.size).toArray⟩ ++
      tx.inputs.foldl (fun bytes input => bytes ++ serializeTxInput input) ByteArray.empty ++
      ⟨(compactSize tx.outputs.size).toArray⟩ ++
      tx.outputs.foldl (fun bytes output => bytes ++ serializeTxOutput output) ByteArray.empty ++
      (List.range tx.inputs.size).foldl
        (fun bytes index => bytes ++ serializeWitness (witnesses.getD index [])) ByteArray.empty ++
      ⟨(unsignedLE 4 tx.locktime.toNat).toArray⟩

end LeanMiniscript.Bitcoin
