import LeanMiniscript.Psbt.Fields
import LeanMiniscript.Miniscript.DescriptorKey
import LeanMiniscript.Miniscript.OutputDescriptor

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-!
# Creator, updater, combiner, signer support and extractor

Roles edit the stored key-value maps, so records a role does not understand
are carried through unchanged. Successful roles re-decode their result, so
they return only PSBTs accepted by `Psbt.decode`.

The combiner is a left-biased union of each map, by key. It requires both
PSBTs to describe the same transaction: the same unsigned transaction for
version 0, or the same BIP370 unique identifier for version 2.

The signer entry points take caller-supplied signing callbacks. They compute
the exact BIP143, legacy, or BIP341 digest, append the requested hash type,
verify the resulting signature, and insert it. This keeps deterministic
nonce generation and private-key handling at the application boundary.
-/

inductive RoleError where
  | psbt (error : PsbtError)
  | inputIndex
  | outputIndex
  | differentTransactions
  | missingUtxo
  | utxoMismatch (reason : String)
  | scriptMismatch (reason : String)
  | descriptor (message : String)
  | sighash (reason : String)
  | invalidSignature
  | notFinalized (index : Nat)
  deriving Repr, DecidableEq

def liftPsbt {α : Type} : Except PsbtError α → Except RoleError α := Except.mapError .psbt

/-! ## Byte helpers -/

def uint32Bytes (value : UInt32) : ByteArray := ⟨(unsignedLE 4 value.toNat).toArray⟩
def uint64Bytes (value : UInt64) : ByteArray := ⟨(unsignedLE 8 value.toNat).toArray⟩
def compactSizeBytes (value : Nat) : ByteArray := ⟨(compactSize value).toArray⟩

def p2shScript (script : ByteArray) : ByteArray :=
  ⟨#[0xa9, 0x14]⟩ ++ LeanHash160.hash160 script ++ ⟨#[0x87]⟩

def p2wshScript (script : ByteArray) : ByteArray :=
  ⟨#[0x00, 0x20]⟩ ++ LeanHash160.SHA256.hash script

def p2pkhScript (keyHash : ByteArray) : ByteArray :=
  ⟨#[0x76, 0xa9, 0x14]⟩ ++ keyHash ++ ⟨#[0x88, 0xac]⟩

def isP2sh (script : ByteArray) : Bool :=
  script.size == 23 && script[0]! == 0xa9 && script[1]! == 0x14 && script[22]! == 0x87

/-- BIP141 witness program: a version opcode and one 2-to-40-byte push. -/
def isWitnessProgram (script : ByteArray) : Bool :=
  4 ≤ script.size && script.size ≤ 42 &&
    (script[0]! == 0 || ((0x51 : UInt8) ≤ script[0]! && script[0]! ≤ (0x60 : UInt8))) &&
    script[1]!.toNat + 2 == script.size

def isP2wpkh (script : ByteArray) : Bool := script.size == 22 && script[0]! == 0 && script[1]! == 20
def isP2wsh (script : ByteArray) : Bool := script.size == 34 && script[0]! == 0 && script[1]! == 32
def isP2tr (script : ByteArray) : Bool := script.size == 34 && script[0]! == 0x51 && script[1]! == 32

/-- Minimal direct push used for a single-element P2SH scriptSig. -/
def pushData (data : ByteArray) : ByteArray :=
  if data.size < 76 then ⟨#[UInt8.ofNat data.size]⟩ ++ data
  else if data.size < 256 then ⟨#[0x4c, UInt8.ofNat data.size]⟩ ++ data
  else ⟨#[0x4d] ++ (unsignedLE 2 data.size).toArray⟩ ++ data

/-- Data pushes of a script, stopping at the first malformed push. -/
def scriptPushes (script : ByteArray) : List ByteArray := Id.run do
  let mut offset := 0
  let mut pushes : Array ByteArray := #[]
  for _ in [0:script.size] do
    if offset ≥ script.size then break
    let opcode := script[offset]!.toNat
    let (width, length?) :=
      if 1 ≤ opcode && opcode ≤ 75 then (0, some opcode)
      else if opcode == 0x4c then (1, none)
      else if opcode == 0x4d then (2, none)
      else if opcode == 0x4e then (4, none)
      else (0, some 0)
    if width > script.size - (offset + 1) then break
    let length := length?.getD (decodeLE (script.extract (offset + 1) (offset + 1 + width)).data.toList)
    let start := offset + 1 + width
    if length > script.size - start then break
    if length > 0 then pushes := pushes.push (script.extract start (start + length))
    offset := start + length
  return pushes.toList

/-- Lexicographic order on key bytes. -/
def lexLE : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLE as bs

/-- Records sorted by key bytes, the order used by deterministic writers. -/
def KeyValueMap.sorted (map : KeyValueMap) : KeyValueMap :=
  map.mergeSort (fun a b => lexLE a.key.data.toList b.key.data.toList)

/-- Same records regardless of order. -/
def KeyValueMap.sameRecords (left right : KeyValueMap) : Bool :=
  left.sorted == right.sorted

def Psbt.sameRecords (left right : Psbt) : Bool :=
  left.global.sameRecords right.global &&
    left.inputs.length == right.inputs.length && left.outputs.length == right.outputs.length &&
    (left.inputs.zip right.inputs).all (fun (a, b) => a.sameRecords b) &&
    (left.outputs.zip right.outputs).all (fun (a, b) => a.sameRecords b)

/-- Re-decode a role result. -/
def Psbt.checked (psbt : Psbt) : Except RoleError Psbt := do
  let _ ← liftPsbt psbt.decode
  return psbt

def Psbt.modifyInput (psbt : Psbt) (index : Nat) (edit : KeyValueMap → KeyValueMap) :
    Except RoleError Psbt :=
  if index < psbt.inputs.length then .ok { psbt with inputs := psbt.inputs.modify index edit }
  else .error .inputIndex

def Psbt.modifyOutput (psbt : Psbt) (index : Nat) (edit : KeyValueMap → KeyValueMap) :
    Except RoleError Psbt :=
  if index < psbt.outputs.length then .ok { psbt with outputs := psbt.outputs.modify index edit }
  else .error .outputIndex

/-! ## Creator -/

/-- BIP174 creator: the unsigned transaction and empty maps. -/
def Psbt.createV0 (tx : Transaction) : Except RoleError Psbt :=
  if tx.inputs.any (fun input => input.scriptSig.size != 0) then
    .error (.psbt (.invalidUnsignedTransaction "scriptSig must be empty"))
  else Psbt.checked {
    global := [⟨recordKey KeyType.globalUnsignedTx, serializeTransaction tx⟩]
    inputs := List.replicate tx.inputs.size []
    outputs := List.replicate tx.outputs.size [] }

/-- BIP370 creator and constructor from a complete transaction description.
Each input records its sequence; the fallback lock time is the transaction's. -/
def Psbt.createV2 (tx : Transaction) (txModifiable : Option UInt8 := none) :
    Except RoleError Psbt :=
  Psbt.checked {
    global := [⟨recordKey KeyType.globalTxVersion, uint32Bytes tx.version⟩,
      ⟨recordKey KeyType.globalFallbackLocktime, uint32Bytes tx.locktime⟩,
      ⟨recordKey KeyType.globalInputCount, compactSizeBytes tx.inputs.size⟩,
      ⟨recordKey KeyType.globalOutputCount, compactSizeBytes tx.outputs.size⟩] ++
      (txModifiable.toList.map fun flags => ⟨recordKey KeyType.globalTxModifiable, ⟨#[flags]⟩⟩) ++
      [⟨recordKey KeyType.globalVersion, uint32Bytes 2⟩]
    inputs := tx.inputs.toList.map fun input =>
      [⟨recordKey KeyType.inPreviousTxid, input.previousOutput.txid⟩,
       ⟨recordKey KeyType.inOutputIndex, uint32Bytes input.previousOutput.index⟩,
       ⟨recordKey KeyType.inSequence, uint32Bytes input.sequence⟩]
    outputs := tx.outputs.toList.map fun output =>
      [⟨recordKey KeyType.outAmount, uint64Bytes output.amount⟩,
       ⟨recordKey KeyType.outScript, output.scriptPubKey⟩] }

/-! ## Decoded views used by several roles -/

def DecodedPsbt.input (decoded : DecodedPsbt) (index : Nat) : Except RoleError InputFields :=
  match decoded.inputs[index]? with
  | some input => .ok input
  | none => .error .inputIndex

/-- The output spent by an input. A non-witness UTXO must hash to the
outpoint's txid and contain its index; when both UTXO forms are present they
must agree. -/
def DecodedPsbt.spentOutput (decoded : DecodedPsbt) (index : Nat) : Except RoleError TxOutput := do
  let input ← decoded.input index
  let tx ← liftPsbt decoded.unsignedTransaction
  let some txin := tx.inputs[index]? | throw .inputIndex
  let fromFull ← match input.nonWitnessUtxo with
    | none => pure none
    | some previous =>
        if previous.txid != txin.previousOutput.txid then
          throw (.utxoMismatch "non-witness UTXO does not match the outpoint txid")
        match previous.outputs[txin.previousOutput.index.toNat]? with
        | none => throw (.utxoMismatch "outpoint index is outside the non-witness UTXO")
        | some output => pure (some output)
  match input.witnessUtxo, fromFull with
  | some output, some full =>
      if output.amount == full.amount && output.scriptPubKey == full.scriptPubKey then pure output
      else throw (.utxoMismatch "witness and non-witness UTXOs disagree")
  | some output, none => pure output
  | none, some full => pure full
  | none, none => throw .missingUtxo

def DecodedPsbt.spentOutputs (decoded : DecodedPsbt) : Except RoleError (Array TxOutput) :=
  ((List.range decoded.inputs.length).mapM decoded.spentOutput).map List.toArray

/-! ## Updater -/

/-- Scripts, previous transactions and key origins known to an updater. -/
structure UpdaterData where
  redeemScripts : List ByteArray := []
  witnessScripts : List ByteArray := []
  /-- Serialized previous transactions; witness serialization is accepted. -/
  previousTransactions : List ByteArray := []
  /-- Public keys with their BIP32 origins. -/
  keyOrigins : List (ByteArray × KeySource) := []

/-- Origins for keys pushed by the scripts, or whose HASH160 they push. -/
def UpdaterData.originsFor (data : UpdaterData) (scripts : List ByteArray) :
    List (ByteArray × KeySource) :=
  let pushes := scripts.flatMap scriptPushes
  data.keyOrigins.filter fun (key, _) =>
    pushes.any (fun push => push == key || push == LeanHash160.hash160 key)

private def scriptsFor (data : UpdaterData) (scriptPubKey : ByteArray) :
    Option ByteArray × Option ByteArray :=
  let redeem := data.redeemScripts.find? (fun script => p2shScript script == scriptPubKey)
  let effective := redeem.getD scriptPubKey
  let witness := data.witnessScripts.find? (fun script => p2wshScript script == effective)
  (redeem, witness)

private def bip32Records (keyType : Nat) (origins : List (ByteArray × KeySource)) : KeyValueMap :=
  origins.map fun (key, source) => ⟨recordKey keyType key, encodeKeySource source⟩

private def insertAll (map : KeyValueMap) (records : KeyValueMap) : KeyValueMap :=
  records.foldl (fun map record => map.insert record.key record.value) map

/-- BIP174 updater. For each input whose previous transaction is known, add
its witness UTXO when the spent script (or P2SH redeem script) is a witness
program and its non-witness UTXO otherwise, matching redeem and witness
scripts, and origins for keys used by those scripts. Outputs receive matching
scripts and key origins. -/
def Psbt.update (psbt : Psbt) (data : UpdaterData) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let tx ← liftPsbt decoded.unsignedTransaction
  let previous := data.previousTransactions.filterMap fun bytes =>
    match parseTransaction bytes with
    | .ok parsed => some (bytes, parsed.transaction)
    | .error _ => none
  let inputs := (psbt.inputs.zip tx.inputs.toList).map fun (map, txin) =>
    match previous.find? (fun (_, prev) => prev.txid == txin.previousOutput.txid) with
    | none => map
    | some (bytes, prev) =>
        match prev.outputs[txin.previousOutput.index.toNat]? with
        | none => map
        | some spent =>
            let (redeem, witness) := scriptsFor data spent.scriptPubKey
            let effective := redeem.getD spent.scriptPubKey
            let utxo : Record := if isWitnessProgram effective then
                ⟨recordKey KeyType.inWitnessUtxo, serializeTxOutput spent⟩
              else ⟨recordKey KeyType.inNonWitnessUtxo, bytes⟩
            let scripts := [spent.scriptPubKey] ++ redeem.toList ++ witness.toList
            insertAll map ([utxo] ++
              (redeem.toList.map fun script => ⟨recordKey KeyType.inRedeemScript, script⟩) ++
              (witness.toList.map fun script => ⟨recordKey KeyType.inWitnessScript, script⟩) ++
              bip32Records KeyType.inBip32Derivation (data.originsFor scripts))
  let outputs := (psbt.outputs.zip tx.outputs.toList).map fun (map, output) =>
    let (redeem, witness) := scriptsFor data output.scriptPubKey
    let scripts := [output.scriptPubKey] ++ redeem.toList ++ witness.toList
    insertAll map (
      (redeem.toList.map fun script => ⟨recordKey KeyType.outRedeemScript, script⟩) ++
      (witness.toList.map fun script => ⟨recordKey KeyType.outWitnessScript, script⟩) ++
      bip32Records KeyType.outBip32Derivation (data.originsFor scripts))
  Psbt.checked { psbt with inputs, outputs }

/-- Set `PSBT_IN_SIGHASH_TYPE`. -/
def Psbt.setSighashType (psbt : Psbt) (index : Nat) (hashType : UInt32) : Except RoleError Psbt := do
  let updated ← psbt.modifyInput index (·.insert (recordKey KeyType.inSighashType) (uint32Bytes hashType))
  updated.checked

/-! ## Descriptor updater -/

/-- The x-only form of a 32-byte or compressed key. -/
def xOnly (key : ByteArray) : ByteArray :=
  if key.size == 33 then key.extract 1 33 else key

/-- BIP32 origin of a descriptor key at a wildcard index: the declared origin
followed by the derivation suffix. Without an origin, an extended key
contributes its own fingerprint and a plain key the fingerprint of itself. -/
def descriptorKeySource (key : DescriptorKey) (wildcardIndex : Option Nat := none) :
    Except String (ByteArray × KeySource) := do
  let publicKey ← key.resolve wildcardIndex
  let index : DerivationStep → Nat
    | .normal value => value
    | .hardened value => value + 0x80000000
  let suffix := key.derivation.map index ++ match key.wildcard, wildcardIndex with
    | .normal, some child => [child]
    | .hardened, some child => [child + 0x80000000]
    | _, _ => []
  let (fingerprint, originPath) ← match key.origin, key.material with
    | some origin, _ => pure (origin.fingerprint, origin.path.map index)
    | none, .extendedKey extended =>
        pure ((LeanHash160.hash160 (← BIP32.publicKey extended)).extract 0 4, [])
    | none, _ => pure ((LeanHash160.hash160 publicKey.bytes).extract 0 4, [])
  return (publicKey.bytes,
    { fingerprint, path := (originPath ++ suffix).map UInt32.ofNat })

/-- Parse a key expression and compute its origin. -/
def keySourceOf (token : String) (wildcardIndex : Option Nat := none) :
    Except String (ByteArray × KeySource) := do
  descriptorKeySource (← parseDescriptorKey token) wildcardIndex

private def descriptorInternalKey : OutputDescriptor → Option ByteArray
  | .tr key _ => some (xOnly key.bytes)
  | _ => none

private def descriptorKeys : OutputDescriptor → List ByteArray
  | .wsh fragment | .shWsh fragment => (desugar fragment).keys.map (·.bytes)
  | .tr _ none => []
  | .tr _ (some tree) => tree.fragments.flatMap fun fragment => (desugar fragment).keys.map (·.bytes)

/-- Taproot key origins with the hashes of the leaves that use each key. -/
private def tapOrigins (descriptor : OutputDescriptor) (compiled : CompiledDescriptor)
    (origins : List (ByteArray × KeySource)) : List (ByteArray × TapKeySource) :=
  origins.filterMap fun (key, source) =>
    let key := xOnly key
    let leafHashes := compiled.taprootLeaves.filterMap fun leaf =>
      if (desugar leaf.fragment).keys.any (fun leafKey => xOnly leafKey.bytes == key) then
        some (tapleafHash leaf.script 0xc0) else none
    if descriptorInternalKey descriptor == some key || !leafHashes.isEmpty then
      some (key, { leafHashes := leafHashes.eraseDups, source })
    else none

def compileDescriptor (descriptor : OutputDescriptor) : Except RoleError CompiledDescriptor :=
  (compileOutputDescriptor descriptor).mapError .descriptor

/-- Fill an input from the descriptor that produced its spent output. When a
UTXO is present its script must be the descriptor's output script. -/
def Psbt.updateInputFromDescriptor (psbt : Psbt) (index : Nat) (descriptor : OutputDescriptor)
    (origins : List (ByteArray × KeySource) := []) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let _ ← decoded.input index
  let compiled ← compileDescriptor descriptor
  match decoded.spentOutput index with
  | .ok spent =>
      if spent.scriptPubKey != compiled.scriptPubKey then
        throw (.scriptMismatch "UTXO script is not the descriptor output")
  | .error .missingUtxo => pure ()
  | .error error => throw error
  let keys := descriptorKeys descriptor
  let records : KeyValueMap := match descriptor with
    | .wsh _ | .shWsh _ =>
        (compiled.redeemScript.toList.map fun script => ⟨recordKey KeyType.inRedeemScript, script⟩) ++
        (compiled.witnessScript.toList.map fun script => ⟨recordKey KeyType.inWitnessScript, script⟩) ++
        bip32Records KeyType.inBip32Derivation (origins.filter fun (key, _) => keys.contains key)
    | .tr _ _ =>
        (descriptorInternalKey descriptor).toList.map (fun key => ⟨recordKey KeyType.inTapInternalKey, key⟩) ++
        (compiled.taprootMerkleRoot.toList.map fun root => ⟨recordKey KeyType.inTapMerkleRoot, root⟩) ++
        (compiled.taprootLeaves.map fun leaf =>
          ⟨recordKey KeyType.inTapLeafScript leaf.controlBlock, leaf.script ++ ⟨#[0xc0]⟩⟩) ++
        ((tapOrigins descriptor compiled origins).map fun (key, source) =>
          ⟨recordKey KeyType.inTapBip32Derivation key, encodeTapKeySource source⟩)
  let updated ← psbt.modifyInput index (insertAll · records)
  updated.checked

/-- Fill an output from the descriptor producing its script. -/
def Psbt.updateOutputFromDescriptor (psbt : Psbt) (index : Nat) (descriptor : OutputDescriptor)
    (origins : List (ByteArray × KeySource) := []) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let tx ← liftPsbt decoded.unsignedTransaction
  let some output := tx.outputs[index]? | throw .outputIndex
  let compiled ← compileDescriptor descriptor
  if output.scriptPubKey != compiled.scriptPubKey then
    throw (.scriptMismatch "output script is not the descriptor output")
  let keys := descriptorKeys descriptor
  let records : KeyValueMap := match descriptor with
    | .wsh _ | .shWsh _ =>
        (compiled.redeemScript.toList.map fun script => ⟨recordKey KeyType.outRedeemScript, script⟩) ++
        (compiled.witnessScript.toList.map fun script => ⟨recordKey KeyType.outWitnessScript, script⟩) ++
        bip32Records KeyType.outBip32Derivation (origins.filter fun (key, _) => keys.contains key)
    | .tr _ _ =>
        (descriptorInternalKey descriptor).toList.map (fun key => ⟨recordKey KeyType.outTapInternalKey, key⟩) ++
        (if compiled.taprootLeaves.isEmpty then [] else
          [⟨recordKey KeyType.outTapTree, encodeTapTree (compiled.taprootLeaves.map fun leaf =>
            { depth := leaf.merklePath.length, leafVersion := 0xc0, script := leaf.script })⟩]) ++
        ((tapOrigins descriptor compiled origins).map fun (key, source) =>
          ⟨recordKey KeyType.outTapBip32Derivation key, encodeTapKeySource source⟩)
  let updated ← psbt.modifyOutput index (insertAll · records)
  updated.checked

/-! ## Combiner -/

/-- Left-biased union by key: every left record, then right records whose key
the left map lacks. -/
def mergeMap (left right : KeyValueMap) : KeyValueMap :=
  left ++ right.filter (fun record => !left.any (fun r => decide (r.key = record.key)))

/-- Map-wise union of two PSBTs with the same map counts. -/
def Psbt.combineMaps (left right : Psbt) : Psbt :=
  { global := mergeMap left.global right.global
    inputs := List.zipWith mergeMap left.inputs right.inputs
    outputs := List.zipWith mergeMap left.outputs right.outputs }

/-- Transaction identity used by the combiner: the unsigned transaction for
version 0, and the BIP370 unique identifier (txid with zero sequences) for
version 2. -/
def DecodedPsbt.uniqueId (decoded : DecodedPsbt) : Except RoleError (Nat × ByteArray) := do
  let tx ← liftPsbt decoded.unsignedTransaction
  if decoded.global.psbtVersion == 0 then return (0, serializeTransaction tx)
  let zeroed : Transaction :=
    { tx with inputs := tx.inputs.map fun (input : TxInput) => { input with sequence := 0 } }
  return (2, zeroed.txid)

/-- BIP174 combiner for two PSBTs of the same transaction. -/
def Psbt.combine (left right : Psbt) : Except RoleError Psbt := do
  let leftDecoded ← liftPsbt left.decode
  let rightDecoded ← liftPsbt right.decode
  let leftId ← leftDecoded.uniqueId
  let rightId ← rightDecoded.uniqueId
  if leftId ≠ rightId ∨ left.inputs.length ≠ right.inputs.length ∨
      left.outputs.length ≠ right.outputs.length then
    throw .differentTransactions
  (left.combineMaps right).checked

/-- Combine a nonempty list from left to right. -/
def Psbt.combineAll : List Psbt → Except RoleError Psbt
  | [] => .error .differentTransactions
  | first :: rest => rest.foldlM Psbt.combine first

/-! ## Signer support -/

/-- How an input is spent, derived from its UTXO and scripts. -/
inductive SpendKind where
  | legacy (scriptCode : ByteArray)
  | witnessV0 (scriptCode : ByteArray) (amount : UInt64)
  | taproot
  deriving Repr

/-- BIP174 signer checks: UTXO and outpoint agreement, no witness UTXO for a
non-witness spend, and redeem and witness scripts matching their hashes. The
spend kind determines the signature hash. -/
def DecodedPsbt.spendKind (decoded : DecodedPsbt) (index : Nat) : Except RoleError SpendKind := do
  let input ← decoded.input index
  let spent ← decoded.spentOutput index
  let script := spent.scriptPubKey
  let effective ← if isP2sh script then
      match input.redeemScript with
      | none => throw (.scriptMismatch "P2SH input lacks a redeem script")
      | some redeem =>
          if p2shScript redeem != script then
            throw (.scriptMismatch "redeem script does not match the P2SH output")
          pure redeem
    else
      if input.redeemScript.isSome then
        throw (.scriptMismatch "redeem script supplied for a non-P2SH output")
      pure script
  if isP2tr effective && !isP2sh script then return .taproot
  if isP2wpkh effective then
    return .witnessV0 (p2pkhScript (effective.extract 2 22)) spent.amount
  if isP2wsh effective then
    match input.witnessScript with
    | none => throw (.scriptMismatch "P2WSH input lacks a witness script")
    | some witness =>
        if p2wshScript witness != effective then
          throw (.scriptMismatch "witness script does not match the witness program")
        return .witnessV0 witness spent.amount
  if isWitnessProgram effective then throw (.scriptMismatch "unsupported witness program")
  if input.witnessUtxo.isSome then
    throw (.utxoMismatch "witness UTXO supplied for a non-witness spend")
  if input.witnessScript.isSome then
    throw (.scriptMismatch "witness script supplied for a non-witness spend")
  return .legacy effective

/-- Digest an ECDSA signer signs for an input and hash type. -/
def DecodedPsbt.ecdsaSignatureHash (decoded : DecodedPsbt) (index : Nat) (hashType : UInt32) :
    Except RoleError ByteArray := do
  let tx ← liftPsbt decoded.unsignedTransaction
  match ← decoded.spendKind index with
  | .legacy scriptCode =>
      (legacySignatureHash tx index scriptCode hashType).mapError fun _ => .sighash "legacy"
  | .witnessV0 scriptCode amount =>
      (witnessV0SignatureHash tx index scriptCode amount hashType).mapError fun _ => .sighash "BIP143"
  | .taproot => throw (.sighash "Taproot inputs use Schnorr signatures")

/-- BIP341/342 digest for a key-path or version-0xc0 script-path signature. -/
def DecodedPsbt.taprootSignatureHash (decoded : DecodedPsbt) (index : Nat)
    (leafScript : Option ByteArray) (hashType : UInt8) : Except RoleError ByteArray := do
  let tx ← liftPsbt decoded.unsignedTransaction
  let spentOutputs ← decoded.spentOutputs
  let spendPath := match leafScript with
    | none => TaprootSpendPath.keyPath
    | some script => .scriptPath script 0xc0 0xffffffff
  (Bitcoin.taprootSignatureHash { transaction := tx, spentOutputs, inputIndex := index, spendPath }
    hashType).mapError fun _ => .sighash "BIP341"

/-- Verify an ECDSA partial signature, whose last byte is its hash type, with
the supplied verifier (for example `ECDSA.verify`). -/
def DecodedPsbt.verifyPartialSig (decoded : DecodedPsbt) (index : Nat)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (publicKey signature : ByteArray) : Bool :=
  signature.size != 0 &&
    match decoded.ecdsaSignatureHash index (UInt32.ofNat signature[signature.size - 1]!.toNat) with
    | .ok digest => verify (signature.extract 0 (signature.size - 1)) publicKey digest
    | .error _ => false

/-- Insert a verified ECDSA partial signature. -/
def Psbt.addPartialSig (psbt : Psbt) (index : Nat)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (publicKey signature : ByteArray) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  if !decoded.verifyPartialSig index verify publicKey signature then throw .invalidSignature
  let updated ← psbt.modifyInput index
    (·.insert (recordKey KeyType.inPartialSig publicKey) signature)
  updated.checked

/-- Sign and insert an ECDSA partial signature. The callback receives the
32-byte digest and returns DER bytes without the final hash-type byte. -/
def Psbt.signPartialSig (psbt : Psbt) (index : Nat)
    (sign : ByteArray → Option ByteArray)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (publicKey : ByteArray) (hashType : UInt32) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let digest ← decoded.ecdsaSignatureHash index hashType
  let raw ← match sign digest with
    | some signature => pure signature
    | none => throw .invalidSignature
  let signature := raw ++ ⟨#[UInt8.ofNat (hashType.toNat % 256)]⟩
  psbt.addPartialSig index verify publicKey signature

/-- Insert a Taproot key-path signature after BIP340 verification against
the output key. -/
def Psbt.addTapKeySig (psbt : Psbt) (index : Nat)
    (verify : ByteArray → ByteArray → ByteArray → Bool) (signature : ByteArray) :
    Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let spent ← decoded.spentOutput index
  let hashType := if signature.size == 65 then signature[64]! else 0
  let digest ← decoded.taprootSignatureHash index none hashType
  if !(signature.size == 64 || signature.size == 65) ||
      !verify (signature.extract 0 64) (spent.scriptPubKey.extract 2 34) digest then
    throw .invalidSignature
  let updated ← psbt.modifyInput index (·.insert (recordKey KeyType.inTapKeySig) signature)
  updated.checked

/-- Sign and insert a Taproot key-path signature. The callback receives the
32-byte BIP341 digest and returns the 64-byte BIP340 signature; a non-default
hash type is appended by this wrapper. -/
def Psbt.signTapKeySig (psbt : Psbt) (index : Nat)
    (sign : ByteArray → Option ByteArray)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (hashType : UInt8) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let digest ← decoded.taprootSignatureHash index none hashType
  let raw ← match sign digest with
    | some signature => pure signature
    | none => throw .invalidSignature
  if raw.size != 64 then throw .invalidSignature
  let signature := if hashType == 0 then raw else raw ++ ⟨#[hashType]⟩
  psbt.addTapKeySig index verify signature

/-- Insert a Taproot script-path signature for an x-only key and a version
0xc0 leaf script, after BIP340 verification. -/
def Psbt.addTapScriptSig (psbt : Psbt) (index : Nat)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (publicKey leafScript signature : ByteArray) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let hashType := if signature.size == 65 then signature[64]! else 0
  let digest ← decoded.taprootSignatureHash index (some leafScript) hashType
  if !(signature.size == 64 || signature.size == 65) ||
      !verify (signature.extract 0 64) publicKey digest then
    throw .invalidSignature
  let updated ← psbt.modifyInput index
    (·.insert (recordKey KeyType.inTapScriptSig (publicKey ++ tapleafHash leafScript 0xc0)) signature)
  updated.checked

/-- Sign and insert a Taproot script-path signature for a version-0xc0 leaf. -/
def Psbt.signTapScriptSig (psbt : Psbt) (index : Nat)
    (sign : ByteArray → Option ByteArray)
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (publicKey leafScript : ByteArray) (hashType : UInt8) : Except RoleError Psbt := do
  let decoded ← liftPsbt psbt.decode
  let digest ← decoded.taprootSignatureHash index (some leafScript) hashType
  let raw ← match sign digest with
    | some signature => pure signature
    | none => throw .invalidSignature
  if raw.size != 64 then throw .invalidSignature
  let signature := if hashType == 0 then raw else raw ++ ⟨#[hashType]⟩
  psbt.addTapScriptSig index verify publicKey leafScript signature

/-! ## Extractor -/

/-- The final transaction and witness stacks. Every input needs a final
scriptSig or a final witness. -/
def DecodedPsbt.finalTransaction (decoded : DecodedPsbt) :
    Except RoleError WitnessTransaction := do
  let tx ← liftPsbt decoded.unsignedTransaction
  let finals ← (List.range decoded.inputs.length).mapM fun index => do
    let input ← decoded.input index
    if input.finalScriptSig.isNone && input.finalScriptWitness.isNone then
      throw (.notFinalized index)
    pure (input.finalScriptSig.getD ByteArray.empty, input.finalScriptWitness.getD [])
  let inputs := (tx.inputs.toList.zip finals).map
    fun (pair : TxInput × ByteArray × List ByteArray) => { pair.1 with scriptSig := pair.2.1 }
  return { transaction := { tx with inputs := inputs.toArray }, witnesses := finals.map (·.2) }

/-- BIP174 transaction extractor: network serialization of the final
transaction, with BIP144 witness data when any input has a witness. -/
def Psbt.extract (psbt : Psbt) : Except RoleError ByteArray := do
  let decoded ← liftPsbt psbt.decode
  let final ← decoded.finalTransaction
  return serializeWitnessTransaction final.transaction final.witnesses

end LeanMiniscript.Psbt
