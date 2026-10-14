import LeanMiniscript.Psbt.Codec
import LeanMiniscript.Bitcoin.ECDSA
import LeanMiniscript.Bitcoin.Base64

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-!
# Typed BIP174, BIP370 and BIP371 fields

Typed views are decoded from the stored key-value maps. Every known key type
has its key-data and value shape checked; unknown and proprietary records are
returned unchanged in `unknown`, in wire order. Version rules follow BIP370:
version 0 requires the unsigned transaction and excludes version-2 fields;
version 2 excludes the unsigned transaction and requires the version-2
transaction fields. Versions other than 0 and 2 are rejected.

Beyond Core's framing checks, hash preimage records must hash to their key,
as BIP174 requires. Public keys in `PARTIAL_SIG` and `BIP32_DERIVATION` keys
must parse as secp256k1 points. X-only keys are checked only for length.

The typed value encoders are covered by executable round-trip examples for
key origins, Taproot key origins, and complete Taproot trees.
-/

namespace KeyType
def globalUnsignedTx : Nat := 0x00
def globalXpub : Nat := 0x01
def globalTxVersion : Nat := 0x02
def globalFallbackLocktime : Nat := 0x03
def globalInputCount : Nat := 0x04
def globalOutputCount : Nat := 0x05
def globalTxModifiable : Nat := 0x06
def globalVersion : Nat := 0xfb
def proprietary : Nat := 0xfc

def inNonWitnessUtxo : Nat := 0x00
def inWitnessUtxo : Nat := 0x01
def inPartialSig : Nat := 0x02
def inSighashType : Nat := 0x03
def inRedeemScript : Nat := 0x04
def inWitnessScript : Nat := 0x05
def inBip32Derivation : Nat := 0x06
def inFinalScriptSig : Nat := 0x07
def inFinalScriptWitness : Nat := 0x08
def inRipemd160 : Nat := 0x0a
def inSha256 : Nat := 0x0b
def inHash160 : Nat := 0x0c
def inHash256 : Nat := 0x0d
def inPreviousTxid : Nat := 0x0e
def inOutputIndex : Nat := 0x0f
def inSequence : Nat := 0x10
def inRequiredTimeLocktime : Nat := 0x11
def inRequiredHeightLocktime : Nat := 0x12
def inTapKeySig : Nat := 0x13
def inTapScriptSig : Nat := 0x14
def inTapLeafScript : Nat := 0x15
def inTapBip32Derivation : Nat := 0x16
def inTapInternalKey : Nat := 0x17
def inTapMerkleRoot : Nat := 0x18

def outRedeemScript : Nat := 0x00
def outWitnessScript : Nat := 0x01
def outBip32Derivation : Nat := 0x02
def outAmount : Nat := 0x03
def outScript : Nat := 0x04
def outTapInternalKey : Nat := 0x05
def outTapTree : Nat := 0x06
def outTapBip32Derivation : Nat := 0x07
end KeyType

/-- Master fingerprint and derivation path of a key. -/
structure KeySource where
  fingerprint : ByteArray
  path : List UInt32 := []
  deriving Repr, DecidableEq, Inhabited

/-- BIP371 key origin, with the leaf hashes in which the key appears. -/
structure TapKeySource where
  leafHashes : List ByteArray := []
  source : KeySource
  deriving Repr, DecidableEq, Inhabited

/-- One `PSBT_OUT_TAP_TREE` tuple, in depth-first order. -/
structure TapTreeLeaf where
  depth : Nat
  leafVersion : UInt8
  script : ByteArray
  deriving Repr, DecidableEq, Inhabited

/-- One `PSBT_IN_TAP_LEAF_SCRIPT` record. -/
structure TapLeafScript where
  controlBlock : ByteArray
  script : ByteArray
  leafVersion : UInt8
  deriving Repr, DecidableEq, Inhabited

structure GlobalFields where
  unsignedTx : Option Transaction := none
  xpubs : List (ByteArray × KeySource) := []
  txVersion : Option UInt32 := none
  fallbackLocktime : Option UInt32 := none
  inputCount : Option Nat := none
  outputCount : Option Nat := none
  txModifiable : Option UInt8 := none
  version : Option UInt32 := none
  unknown : KeyValueMap := []
  deriving Repr, Inhabited

structure InputFields where
  nonWitnessUtxo : Option Transaction := none
  witnessUtxo : Option TxOutput := none
  partialSigs : List (ByteArray × ByteArray) := []
  sighashType : Option UInt32 := none
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  bip32Derivation : List (ByteArray × KeySource) := []
  finalScriptSig : Option ByteArray := none
  finalScriptWitness : Option (List ByteArray) := none
  ripemd160Preimages : List (ByteArray × ByteArray) := []
  sha256Preimages : List (ByteArray × ByteArray) := []
  hash160Preimages : List (ByteArray × ByteArray) := []
  hash256Preimages : List (ByteArray × ByteArray) := []
  previousTxid : Option ByteArray := none
  outputIndex : Option UInt32 := none
  sequence : Option UInt32 := none
  requiredTimeLocktime : Option UInt32 := none
  requiredHeightLocktime : Option UInt32 := none
  tapKeySig : Option ByteArray := none
  /-- `((x-only key, leaf hash), signature)` -/
  tapScriptSigs : List ((ByteArray × ByteArray) × ByteArray) := []
  tapLeafScripts : List TapLeafScript := []
  tapBip32Derivation : List (ByteArray × TapKeySource) := []
  tapInternalKey : Option ByteArray := none
  tapMerkleRoot : Option ByteArray := none
  unknown : KeyValueMap := []
  deriving Repr, Inhabited

structure OutputFields where
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  bip32Derivation : List (ByteArray × KeySource) := []
  amount : Option UInt64 := none
  script : Option ByteArray := none
  tapInternalKey : Option ByteArray := none
  tapTree : Option (List TapTreeLeaf) := none
  tapBip32Derivation : List (ByteArray × TapKeySource) := []
  unknown : KeyValueMap := []
  deriving Repr, Inhabited

/-! ## Field decoders -/

def checkKeyData (scope : String) (keyType : Nat) (valid : Bool) (reason : String) :
    Except PsbtError Unit :=
  if valid then .ok () else .error (.invalidKey scope keyType reason)

def noKeyData (scope : String) (keyType : Nat) (keyData : ByteArray) :
    Except PsbtError Unit :=
  checkKeyData scope keyType (keyData.size == 0) "key data must be empty"

/-- Decode a value that must be consumed exactly. -/
def exactValue {α : Type} (scope : String) (keyType : Nat) (decoder : Decoder α)
    (value : ByteArray) : Except PsbtError α :=
  match decodeAll decoder value with
  | .ok result => .ok result
  | .error _ => .error (.invalidValue scope keyType "malformed value")

private def checkValue (scope : String) (keyType : Nat) (valid : Bool) (reason : String) :
    Except PsbtError Unit :=
  if valid then .ok () else .error (.invalidValue scope keyType reason)

private def readUInt32List : Nat → Decoder (List UInt32)
  | 0, bytes => .ok ([], bytes)
  | count + 1, bytes => do
      let (value, rest) ← readUInt32 bytes
      let (values, rest) ← readUInt32List count rest
      return (value :: values, rest)

/-- `<4-byte fingerprint> <uint32 path element>*` filling the whole value. -/
def decodeKeySource (scope : String) (keyType : Nat) (value : ByteArray) :
    Except PsbtError KeySource := do
  checkValue scope keyType (value.size ≥ 4 && value.size % 4 == 0) "invalid key origin length"
  let path ← exactValue scope keyType (readUInt32List ((value.size - 4) / 4))
    (value.extract 4 value.size)
  return { fingerprint := value.extract 0 4, path }

def encodeKeySource (source : KeySource) : ByteArray :=
  source.fingerprint ++ ⟨(source.path.flatMap (fun element => unsignedLE 4 element.toNat)).toArray⟩

def decodeTapKeySource (scope : String) (keyType : Nat) (value : ByteArray) :
    Except PsbtError TapKeySource := do
  let (count, rest) ← match readCompactSize value.data.toList with
    | .ok result => pure result
    | .error _ => throw (.invalidValue scope keyType "malformed leaf hash count")
  checkValue scope keyType (count * 32 ≤ rest.length) "truncated leaf hashes"
  let leafHashes := (List.range count).map (fun index =>
    (⟨(rest.drop (32 * index) |>.take 32).toArray⟩ : ByteArray))
  let source ← decodeKeySource scope keyType ⟨(rest.drop (32 * count)).toArray⟩
  return { leafHashes, source }

def encodeTapKeySource (source : TapKeySource) : ByteArray :=
  ⟨(compactSize source.leafHashes.length).toArray⟩ ++
    source.leafHashes.foldl (· ++ ·) ByteArray.empty ++ encodeKeySource source.source

private def validPublicKey (key : ByteArray) : Bool :=
  (key.size == 33 || key.size == 65) && (ECDSA.parsePublicKey key).isSome

private def validSchnorrSignature (signature : ByteArray) : Bool :=
  signature.size == 64 || signature.size == 65

/-- Control-block shape from BIP341: 33 + 32m bytes with m ≤ 128. -/
def validControlBlockSize (size : Nat) : Bool :=
  size ≥ 33 && (size - 33) % 32 == 0 && (size - 33) / 32 ≤ 128

/-- Depth-first leaf depths describe a complete binary tree of depth at most
128. `pending` holds the depths of unfinished left subtrees, deepest first. -/
def tapTreeComplete (depths : List Nat) : Bool :=
  let rec merge : Nat → List Nat → Nat → Option (List Nat)
    | 0, _, _ => none
    | fuel + 1, pending, depth =>
        match pending with
        | top :: rest =>
            if top == depth then
              if depth == 0 then none else merge fuel rest (depth - 1)
            else if depth < top then none
            else some (depth :: pending)
        | [] => some [depth]
  let step (pending : Option (List Nat)) (depth : Nat) : Option (List Nat) := do
    let pending ← pending
    if pending == [0] || depth > 128 then none
    merge 130 pending depth
  (depths.foldl step (some [])) == some [0]

private def readTapTreeLeaf : Decoder TapTreeLeaf := fun bytes => do
  let (header, rest) ← takeExact 2 bytes
  let (script, rest) ← readByteVector rest
  return ({ depth := header[0]!.toNat, leafVersion := header[1]!, script }, rest)

private def readTapTreeLeaves : Nat → Decoder (List TapTreeLeaf)
  | 0, bytes => if bytes.isEmpty then .ok ([], bytes) else .error .trailingData
  | fuel + 1, bytes =>
      if bytes.isEmpty then .ok ([], bytes)
      else do
        let (leaf, rest) ← readTapTreeLeaf bytes
        let (leaves, rest) ← readTapTreeLeaves fuel rest
        return (leaf :: leaves, rest)

def decodeTapTree (value : ByteArray) : Except PsbtError (List TapTreeLeaf) := do
  let scope := "output"
  let keyType := KeyType.outTapTree
  let leaves ← exactValue scope keyType (readTapTreeLeaves value.size) value
  checkValue scope keyType (!leaves.isEmpty) "empty Taproot tree"
  checkValue scope keyType (leaves.all (fun leaf => leaf.leafVersion.toNat % 2 == 0))
    "invalid leaf version"
  checkValue scope keyType (tapTreeComplete (leaves.map (·.depth))) "malformed Taproot tree"
  return leaves

def encodeTapTree (leaves : List TapTreeLeaf) : ByteArray :=
  leaves.foldl (fun bytes leaf =>
    bytes ++ ⟨#[UInt8.ofNat leaf.depth, leaf.leafVersion]⟩ ++ serializeByteVector leaf.script)
    ByteArray.empty

/-- A proprietary key: identifier, CompactSize subtype and optional key data. -/
private def validProprietaryKey (keyData : ByteArray) : Bool :=
  match readByteVector keyData.data.toList with
  | .error _ => false
  | .ok (_, rest) => match readCompactSize rest with
    | .error _ => false
    | .ok _ => true

private def preimageHash (keyType : Nat) (preimage : ByteArray) : ByteArray :=
  if keyType == KeyType.inRipemd160 then LeanHash160.RIPEMD160.hash preimage
  else if keyType == KeyType.inSha256 then LeanHash160.SHA256.hash preimage
  else if keyType == KeyType.inHash160 then LeanHash160.hash160 preimage
  else doubleSHA256 preimage

private def keepUnknown (scope : String) (keyType : Nat) (record : Record) (unknown : KeyValueMap) :
    Except PsbtError KeyValueMap := do
  if keyType == KeyType.proprietary then
    let (_, keyData) ← splitKey record.key
    checkKeyData scope keyType (validProprietaryKey keyData) "malformed proprietary key"
  return unknown ++ [record]

/-! ## Map decoders -/

private def globalStep (fields : GlobalFields) (record : Record) : Except PsbtError GlobalFields := do
  let scope := "global"
  let (keyType, keyData) ← splitKey record.key
  let value := record.value
  if keyType == KeyType.globalUnsignedTx then
    noKeyData scope keyType keyData
    let tx ← match parseTransaction value (allowWitness := false) with
      | .ok tx => pure tx.transaction
      | .error _ => throw (.invalidValue scope keyType "malformed unsigned transaction")
    return { fields with unsignedTx := some tx }
  else if keyType == KeyType.globalXpub then
    checkKeyData scope keyType (keyData.size == 78) "extended key must be 78 bytes"
    let source ← decodeKeySource scope keyType value
    checkValue scope keyType (source.path.length == keyData[4]!.toNat)
      "path length must match the extended key depth"
    return { fields with xpubs := fields.xpubs ++ [(keyData, source)] }
  else if keyType == KeyType.globalTxVersion then
    noKeyData scope keyType keyData
    return { fields with txVersion := some (← exactValue scope keyType readUInt32 value) }
  else if keyType == KeyType.globalFallbackLocktime then
    noKeyData scope keyType keyData
    return { fields with fallbackLocktime := some (← exactValue scope keyType readUInt32 value) }
  else if keyType == KeyType.globalInputCount then
    noKeyData scope keyType keyData
    return { fields with inputCount := some (← exactValue scope keyType readCompactSize value) }
  else if keyType == KeyType.globalOutputCount then
    noKeyData scope keyType keyData
    return { fields with outputCount := some (← exactValue scope keyType readCompactSize value) }
  else if keyType == KeyType.globalTxModifiable then
    noKeyData scope keyType keyData
    checkValue scope keyType (value.size == 1) "flags must be one byte"
    return { fields with txModifiable := some value[0]! }
  else if keyType == KeyType.globalVersion then
    noKeyData scope keyType keyData
    return { fields with version := some (← exactValue scope keyType readUInt32 value) }
  else return { fields with unknown := ← keepUnknown scope keyType record fields.unknown }

def GlobalFields.psbtVersion (fields : GlobalFields) : Nat :=
  (fields.version.map UInt32.toNat).getD 0

/-- Decode the global map and apply the version rules. -/
def decodeGlobal (map : KeyValueMap) : Except PsbtError GlobalFields := do
  let fields ← map.foldlM globalStep {}
  let scope := "global"
  match fields.psbtVersion with
  | 0 =>
      let some tx := fields.unsignedTx | throw (.missingField scope KeyType.globalUnsignedTx)
      if tx.inputs.any (fun input => input.scriptSig.size != 0) then
        throw (.invalidUnsignedTransaction "scriptSig must be empty")
      if fields.txVersion.isSome then throw (.excludedField scope KeyType.globalTxVersion)
      if fields.fallbackLocktime.isSome then
        throw (.excludedField scope KeyType.globalFallbackLocktime)
      if fields.inputCount.isSome then throw (.excludedField scope KeyType.globalInputCount)
      if fields.outputCount.isSome then throw (.excludedField scope KeyType.globalOutputCount)
      if fields.txModifiable.isSome then throw (.excludedField scope KeyType.globalTxModifiable)
      return fields
  | 2 =>
      if fields.unsignedTx.isSome then throw (.excludedField scope KeyType.globalUnsignedTx)
      if fields.txVersion.isNone then throw (.missingField scope KeyType.globalTxVersion)
      if fields.inputCount.isNone then throw (.missingField scope KeyType.globalInputCount)
      if fields.outputCount.isNone then throw (.missingField scope KeyType.globalOutputCount)
      return fields
  | version => throw (.unsupportedVersion version)

/-- Input and output map counts determined by the decoded global map. -/
def GlobalFields.counts (fields : GlobalFields) : Nat × Nat :=
  match fields.unsignedTx with
  | some tx => (tx.inputs.size, tx.outputs.size)
  | none => (fields.inputCount.getD 0, fields.outputCount.getD 0)

def globalCounts (map : KeyValueMap) : Except PsbtError (Nat × Nat) := do
  return (← decodeGlobal map).counts

private def v2Only (scope : String) (version keyType : Nat) : Except PsbtError Unit :=
  if version == 2 then .ok () else .error (.excludedField scope keyType)

/-- Decode one input record, updating its typed field. -/
def inputStep (version : Nat) (fields : InputFields) (record : Record) :
    Except PsbtError InputFields := do
  let scope := "input"
  let (keyType, keyData) ← splitKey record.key
  let value := record.value
  if keyType == KeyType.inNonWitnessUtxo then
    noKeyData scope keyType keyData
    let tx ← match parseTransaction value with
      | .ok tx => pure tx.transaction
      | .error _ => throw (.invalidValue scope keyType "malformed transaction")
    return { fields with nonWitnessUtxo := some tx }
  else if keyType == KeyType.inWitnessUtxo then
    noKeyData scope keyType keyData
    return { fields with witnessUtxo := some (← exactValue scope keyType readTxOutput value) }
  else if keyType == KeyType.inPartialSig then
    checkKeyData scope keyType (validPublicKey keyData) "invalid public key"
    return { fields with partialSigs := fields.partialSigs ++ [(keyData, value)] }
  else if keyType == KeyType.inSighashType then
    noKeyData scope keyType keyData
    return { fields with sighashType := some (← exactValue scope keyType readUInt32 value) }
  else if keyType == KeyType.inRedeemScript then
    noKeyData scope keyType keyData
    return { fields with redeemScript := some value }
  else if keyType == KeyType.inWitnessScript then
    noKeyData scope keyType keyData
    return { fields with witnessScript := some value }
  else if keyType == KeyType.inBip32Derivation then
    checkKeyData scope keyType (validPublicKey keyData) "invalid public key"
    let source ← decodeKeySource scope keyType value
    return { fields with bip32Derivation := fields.bip32Derivation ++ [(keyData, source)] }
  else if keyType == KeyType.inFinalScriptSig then
    noKeyData scope keyType keyData
    return { fields with finalScriptSig := some value }
  else if keyType == KeyType.inFinalScriptWitness then
    noKeyData scope keyType keyData
    return { fields with finalScriptWitness := some (← exactValue scope keyType readWitnessStack value) }
  else if keyType == KeyType.inRipemd160 || keyType == KeyType.inSha256 ||
      keyType == KeyType.inHash160 || keyType == KeyType.inHash256 then
    let size := if keyType == KeyType.inRipemd160 || keyType == KeyType.inHash160 then 20 else 32
    checkKeyData scope keyType (keyData.size == size) "invalid hash length"
    checkValue scope keyType (preimageHash keyType value == keyData) "preimage does not match hash"
    let entry := [(keyData, value)]
    if keyType == KeyType.inRipemd160 then
      return { fields with ripemd160Preimages := fields.ripemd160Preimages ++ entry }
    else if keyType == KeyType.inSha256 then
      return { fields with sha256Preimages := fields.sha256Preimages ++ entry }
    else if keyType == KeyType.inHash160 then
      return { fields with hash160Preimages := fields.hash160Preimages ++ entry }
    else return { fields with hash256Preimages := fields.hash256Preimages ++ entry }
  else if keyType == KeyType.inPreviousTxid then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    checkValue scope keyType (value.size == 32) "txid must be 32 bytes"
    return { fields with previousTxid := some value }
  else if keyType == KeyType.inOutputIndex then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    return { fields with outputIndex := some (← exactValue scope keyType readUInt32 value) }
  else if keyType == KeyType.inSequence then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    return { fields with sequence := some (← exactValue scope keyType readUInt32 value) }
  else if keyType == KeyType.inRequiredTimeLocktime then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    let locktime ← exactValue scope keyType readUInt32 value
    checkValue scope keyType (locktime.toNat ≥ 500000000) "time locktime below 500000000"
    return { fields with requiredTimeLocktime := some locktime }
  else if keyType == KeyType.inRequiredHeightLocktime then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    let locktime ← exactValue scope keyType readUInt32 value
    checkValue scope keyType (0 < locktime.toNat && locktime.toNat < 500000000)
      "height locktime outside 1..499999999"
    return { fields with requiredHeightLocktime := some locktime }
  else if keyType == KeyType.inTapKeySig then
    noKeyData scope keyType keyData
    checkValue scope keyType (validSchnorrSignature value) "signature must be 64 or 65 bytes"
    return { fields with tapKeySig := some value }
  else if keyType == KeyType.inTapScriptSig then
    checkKeyData scope keyType (keyData.size == 64) "key must be x-only key and leaf hash"
    checkValue scope keyType (validSchnorrSignature value) "signature must be 64 or 65 bytes"
    return { fields with tapScriptSigs := fields.tapScriptSigs ++
      [((keyData.extract 0 32, keyData.extract 32 64), value)] }
  else if keyType == KeyType.inTapLeafScript then
    checkKeyData scope keyType (validControlBlockSize keyData.size) "invalid control block size"
    checkValue scope keyType (value.size ≥ 1) "missing leaf version"
    return { fields with tapLeafScripts := fields.tapLeafScripts ++
      [{ controlBlock := keyData, script := value.extract 0 (value.size - 1),
         leafVersion := value[value.size - 1]! }] }
  else if keyType == KeyType.inTapBip32Derivation then
    checkKeyData scope keyType (keyData.size == 32) "key must be x-only"
    let source ← decodeTapKeySource scope keyType value
    return { fields with tapBip32Derivation := fields.tapBip32Derivation ++ [(keyData, source)] }
  else if keyType == KeyType.inTapInternalKey then
    noKeyData scope keyType keyData
    checkValue scope keyType (value.size == 32) "internal key must be x-only"
    return { fields with tapInternalKey := some value }
  else if keyType == KeyType.inTapMerkleRoot then
    noKeyData scope keyType keyData
    checkValue scope keyType (value.size == 32) "Merkle root must be 32 bytes"
    return { fields with tapMerkleRoot := some value }
  else return { fields with unknown := ← keepUnknown scope keyType record fields.unknown }

def decodeInput (version : Nat) (map : KeyValueMap) : Except PsbtError InputFields := do
  let fields ← map.foldlM (inputStep version) {}
  if version == 2 then
    if fields.previousTxid.isNone then throw (.missingField "input" KeyType.inPreviousTxid)
    if fields.outputIndex.isNone then throw (.missingField "input" KeyType.inOutputIndex)
  return fields

private def outputStep (version : Nat) (fields : OutputFields) (record : Record) :
    Except PsbtError OutputFields := do
  let scope := "output"
  let (keyType, keyData) ← splitKey record.key
  let value := record.value
  if keyType == KeyType.outRedeemScript then
    noKeyData scope keyType keyData
    return { fields with redeemScript := some value }
  else if keyType == KeyType.outWitnessScript then
    noKeyData scope keyType keyData
    return { fields with witnessScript := some value }
  else if keyType == KeyType.outBip32Derivation then
    checkKeyData scope keyType (validPublicKey keyData) "invalid public key"
    let source ← decodeKeySource scope keyType value
    return { fields with bip32Derivation := fields.bip32Derivation ++ [(keyData, source)] }
  else if keyType == KeyType.outAmount then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    return { fields with amount := some (← exactValue scope keyType readUInt64 value) }
  else if keyType == KeyType.outScript then
    v2Only scope version keyType
    noKeyData scope keyType keyData
    return { fields with script := some value }
  else if keyType == KeyType.outTapInternalKey then
    noKeyData scope keyType keyData
    checkValue scope keyType (value.size == 32) "internal key must be x-only"
    return { fields with tapInternalKey := some value }
  else if keyType == KeyType.outTapTree then
    noKeyData scope keyType keyData
    return { fields with tapTree := some (← decodeTapTree value) }
  else if keyType == KeyType.outTapBip32Derivation then
    checkKeyData scope keyType (keyData.size == 32) "key must be x-only"
    let source ← decodeTapKeySource scope keyType value
    return { fields with tapBip32Derivation := fields.tapBip32Derivation ++ [(keyData, source)] }
  else return { fields with unknown := ← keepUnknown scope keyType record fields.unknown }

def decodeOutput (version : Nat) (map : KeyValueMap) : Except PsbtError OutputFields := do
  let fields ← map.foldlM (outputStep version) {}
  if version == 2 then
    if fields.amount.isNone then throw (.missingField "output" KeyType.outAmount)
    if fields.script.isNone then throw (.missingField "output" KeyType.outScript)
  return fields

/-! ## Whole-PSBT decoding -/

structure DecodedPsbt where
  global : GlobalFields
  inputs : List InputFields
  outputs : List OutputFields
  deriving Repr, Inhabited

/-- Decode every map and check that the stored map counts match the global
fields. -/
def Psbt.decode (psbt : Psbt) : Except PsbtError DecodedPsbt := do
  let global ← decodeGlobal psbt.global
  if global.counts ≠ (psbt.inputs.length, psbt.outputs.length) then throw .mapCount
  let inputs ← psbt.inputs.mapM (decodeInput global.psbtVersion)
  let outputs ← psbt.outputs.mapM (decodeOutput global.psbtVersion)
  return { global, inputs, outputs }

/-- Parse and fully validate binary PSBT bytes. -/
def Psbt.parse (bytes : ByteArray) : Except PsbtError Psbt := do
  let psbt ← decodePsbtWith globalCounts bytes.data.toList
  let _ ← psbt.decode
  return psbt

/-- Parse the BIP174 Base64 text form. -/
def Psbt.parseBase64 (text : String) : Except PsbtError Psbt :=
  match Base64.decode text with
  | none => .error .base64
  | some bytes => Psbt.parse bytes

def Psbt.toBase64 (psbt : Psbt) : String := Base64.encode psbt.serialize

/-- BIP370 lock time determination. Inputs without locktime fields accept
either type; height is preferred when both types remain possible. `none`
means the required types are incompatible. -/
def determineLocktime (fallback : Option UInt32) (inputs : List InputFields) : Option UInt32 :=
  let constrained := inputs.filter (fun input =>
    input.requiredTimeLocktime.isSome || input.requiredHeightLocktime.isSome)
  if constrained.isEmpty then some (fallback.getD 0)
  else if constrained.all (fun input => input.requiredHeightLocktime.isSome) then
    some (constrained.foldl (fun best input => max best (input.requiredHeightLocktime.getD 0)) 0)
  else if constrained.all (fun input => input.requiredTimeLocktime.isSome) then
    some (constrained.foldl (fun best input => max best (input.requiredTimeLocktime.getD 0)) 0)
  else none

/-- The transaction being signed: the stored unsigned transaction for
version 0, or the one built from version-2 fields with the determined lock
time. Input scriptSigs are empty. -/
def DecodedPsbt.unsignedTransaction (decoded : DecodedPsbt) : Except PsbtError Transaction :=
  match decoded.global.unsignedTx with
  | some tx => .ok tx
  | none =>
      match determineLocktime decoded.global.fallbackLocktime decoded.inputs with
      | none => .error (.invalidUnsignedTransaction "incompatible input locktimes")
      | some locktime => .ok {
          version := decoded.global.txVersion.getD 2
          inputs := (decoded.inputs.map fun input => {
            previousOutput := { txid := input.previousTxid.getD ByteArray.empty,
                                index := input.outputIndex.getD 0 }
            sequence := input.sequence.getD 0xffffffff : TxInput }).toArray
          outputs := (decoded.outputs.map fun output => {
            amount := output.amount.getD 0
            scriptPubKey := output.script.getD ByteArray.empty : TxOutput }).toArray
          locktime }

end LeanMiniscript.Psbt
