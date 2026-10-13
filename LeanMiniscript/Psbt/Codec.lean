import LeanMiniscript.Bitcoin.Deserialization

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-!
# BIP174 key-value framing

A PSBT is held as its key-value maps in wire order. Typed field views in
`Psbt.Fields` are decoded from these records, so unknown and proprietary
records survive every role unchanged. This layer checks the magic, CompactSize
canonicality, exact value lengths, duplicate keys within one map, the number
of input and output maps, and trailing data. Field-specific rules are separate.
-/

/-- Errors from framing, field validation and version rules. Field errors name
the map and key type; reasons are diagnostic text only. -/
inductive PsbtError where
  | decode (error : DecodeError)
  | base64
  | magic
  | duplicateKey (key : ByteArray)
  | trailingData
  | invalidKey (scope : String) (keyType : Nat) (reason : String)
  | invalidValue (scope : String) (keyType : Nat) (reason : String)
  | unsupportedVersion (version : Nat)
  | missingField (scope : String) (keyType : Nat)
  | excludedField (scope : String) (keyType : Nat)
  | mapCount
  | invalidUnsignedTransaction (reason : String)
  deriving Repr, DecidableEq

/-- One key-value pair. The key includes its CompactSize key type. -/
structure Record where
  key : ByteArray
  value : ByteArray
  deriving Repr, DecidableEq, Inhabited

/-- One map in wire order. -/
abbrev KeyValueMap := List Record

/-- A PSBT as its global, per-input and per-output maps. -/
structure Psbt where
  global : KeyValueMap
  inputs : List KeyValueMap
  outputs : List KeyValueMap
  deriving Repr, DecidableEq, Inhabited

def magicBytes : List UInt8 := [0x70, 0x73, 0x62, 0x74, 0xff]

def liftDecode {α : Type} : Except DecodeError α → Except PsbtError α :=
  Except.mapError .decode

/-- Value of the record with exactly this key. -/
def KeyValueMap.lookup (map : KeyValueMap) (key : ByteArray) : Option ByteArray :=
  (map.find? (fun record => decide (record.key = key))).map (·.value)

/-- Key uniqueness within one map. -/
def KeyValueMap.Unique (map : KeyValueMap) : Prop :=
  (map.map Record.key).Nodup

/-- Framing preconditions for exact re-reading: nonempty keys and uint64
lengths. -/
def Record.WellFormed (record : Record) : Prop :=
  0 < record.key.size ∧ record.key.size < 2 ^ 64 ∧ record.value.size < 2 ^ 64

def KeyValueMap.WellFormed (map : KeyValueMap) : Prop :=
  (∀ record ∈ map, record.WellFormed) ∧ map.Unique

def Psbt.WellFormed (psbt : Psbt) : Prop :=
  psbt.global.WellFormed ∧ (∀ map ∈ psbt.inputs, map.WellFormed) ∧
    ∀ map ∈ psbt.outputs, map.WellFormed

/-! ## Serialization -/

def Record.encode (record : Record) : List UInt8 :=
  encodeByteVector record.key ++ encodeByteVector record.value

/-- Records followed by the zero-length separator. -/
def KeyValueMap.encode (map : KeyValueMap) : List UInt8 :=
  map.flatMap Record.encode ++ [0]

def Psbt.encode (psbt : Psbt) : List UInt8 :=
  magicBytes ++ (psbt.global.encode ++
    (psbt.inputs.flatMap KeyValueMap.encode ++ psbt.outputs.flatMap KeyValueMap.encode))

def Psbt.serialize (psbt : Psbt) : ByteArray :=
  ⟨psbt.encode.toArray⟩

/-! ## Parsing -/

/-- Read one map. Fuel bounds the record count; every record and the
separator consume at least one byte. A repeated key is rejected. -/
def decodeMapFuel : Nat → List UInt8 → Except PsbtError (KeyValueMap × List UInt8)
  | 0, _ => .error (.decode .truncated)
  | fuel + 1, bytes => do
      let (keyLength, rest) ← liftDecode (readCompactSize bytes)
      if keyLength = 0 then return ([], rest)
      let (key, rest) ← liftDecode (takeExact keyLength rest)
      let (value, rest) ← liftDecode (readByteVector rest)
      let (records, rest) ← decodeMapFuel fuel rest
      let key : ByteArray := ⟨key.toArray⟩
      if records.any (fun record => decide (record.key = key)) then
        throw (.duplicateKey key)
      return ({ key, value } :: records, rest)

def decodeMap (bytes : List UInt8) : Except PsbtError (KeyValueMap × List UInt8) :=
  decodeMapFuel (bytes.length + 1) bytes

def decodeMaps : Nat → List UInt8 → Except PsbtError (List KeyValueMap × List UInt8)
  | 0, bytes => .ok ([], bytes)
  | count + 1, bytes => do
      let (map, rest) ← decodeMap bytes
      let (maps, rest) ← decodeMaps count rest
      return (map :: maps, rest)

/-- Read the magic, the global map, then as many input and output maps as
`counts` derives from the global map, and reject trailing bytes. -/
def decodePsbtWith (counts : KeyValueMap → Except PsbtError (Nat × Nat))
    (bytes : List UInt8) : Except PsbtError Psbt := do
  if bytes.take 5 ≠ magicBytes then throw .magic
  let (global, rest) ← decodeMap (bytes.drop 5)
  let (inputCount, outputCount) ← counts global
  let (inputs, rest) ← decodeMaps inputCount rest
  let (outputs, rest) ← decodeMaps outputCount rest
  if rest ≠ [] then throw .trailingData
  return { global, inputs, outputs }

/-! ## Map editing used by the roles -/

/-- Replace the value for a key, or append a new record. -/
def KeyValueMap.insert (map : KeyValueMap) (key value : ByteArray) : KeyValueMap :=
  if map.any (fun record => decide (record.key = key)) then
    map.map (fun record => if record.key = key then { record with value } else record)
  else map ++ [Record.mk key value]

/-- Add a record only when its key is absent. -/
def KeyValueMap.insertNew (map : KeyValueMap) (key value : ByteArray) : KeyValueMap :=
  if map.any (fun record => decide (record.key = key)) then map else map ++ [Record.mk key value]

/-- Key bytes for a type with optional key data. -/
def recordKey (keyType : Nat) (keyData : ByteArray := ByteArray.empty) : ByteArray :=
  ⟨(compactSize keyType).toArray⟩ ++ keyData

/-- Key type and key data of a key, when the type is canonically encoded. -/
def splitKey (key : ByteArray) : Except PsbtError (Nat × ByteArray) := do
  let (keyType, rest) ← liftDecode (readCompactSize key.data.toList)
  return (keyType, ⟨rest.toArray⟩)

/-- Key type of a record, or `none` for a non-canonical type encoding. -/
def Record.keyType? (record : Record) : Option Nat :=
  match splitKey record.key with
  | .ok (keyType, _) => some keyType
  | .error _ => none

end LeanMiniscript.Psbt
