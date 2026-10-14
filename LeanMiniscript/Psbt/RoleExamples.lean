import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Psbt.Fixtures

namespace LeanMiniscript.Psbt.RoleExamples

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Psbt
open LeanMiniscript.Psbt.Fixtures

/-! Role vectors from BIP174 and BIP371. Record order inside a map is not
significant in BIP174 and Core orders some fields by key hash, so map
contents are compared as record sets (`sameRecords`) except where the
official bytes are reproduced exactly. -/

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩

private def psbtOf (bytes : String) : Psbt :=
  match Psbt.parse (hex bytes) with
  | .ok psbt => psbt
  | .error _ => default

private def decodedOf (psbt : Psbt) : DecodedPsbt :=
  match psbt.decode with
  | .ok decoded => decoded
  | .error _ => default

private def role (index : Nat) : Psbt := psbtOf bip174Roles[index]!.2.1
private def roleBytes (index : Nat) : ByteArray := hex bip174Roles[index]!.2.1

/-! ## BIP174 creator, updater and signer -/

private def displayTxid (text : String) : ByteArray := ⟨(hex text).data.reverse⟩

-- The BIP fixes inputs and outputs; version 2, final sequences and lock time
-- zero are the values serialized in its creator vector.
private def creatorTransaction : Transaction :=
  { version := 2, locktime := 0
    inputs := (bip174CreatorInputs.map fun (txid, index) =>
      { previousOutput := { txid := displayTxid txid, index := UInt32.ofNat index },
        sequence := 0xffffffff : TxInput }).toArray
    outputs := (bip174CreatorOutputs.map fun (script, amount) =>
      { amount := UInt64.ofNat amount, scriptPubKey := hex script : TxOutput }).toArray }

example : (match Psbt.createV0 creatorTransaction with
    | .ok psbt => psbt.serialize == roleBytes 0
    | .error _ => false) = true := by native_decide

-- The updater's previous transactions are the creator's inputs, by TXID.
private def previousTxids : List ByteArray :=
  bip174UpdaterPreviousTransactions.filterMap fun bytes =>
    match parseTransaction (hex bytes) with
    | .ok parsed => some parsed.transaction.txid
    | .error _ => none

example : bip174CreatorInputs.all (fun (txid, _) =>
    previousTxids.contains (displayTxid txid)) = true := by native_decide
example : previousTxids.length = 2 := by native_decide

private def masterFingerprint : ByteArray :=
  match BIP32.parse bip174MasterKey >>= BIP32.publicKey with
  | .ok key => (LeanHash160.hash160 key).extract 0 4
  | .error _ => ByteArray.empty

example : masterFingerprint = hex "d90c6a4f" := by native_decide

private def parsePath (text : String) : List UInt32 :=
  ((text.splitOn "/").drop 1).map fun part =>
    if part.endsWith "'" then UInt32.ofNat ((part.dropEnd 1).toString.toNat! + 0x80000000)
    else UInt32.ofNat part.toNat!

private def updaterData : UpdaterData :=
  { redeemScripts := bip174UpdaterRedeemScripts.map hex
    witnessScripts := bip174UpdaterWitnessScripts.map hex
    previousTransactions := bip174UpdaterPreviousTransactions.map hex
    keyOrigins := bip174UpdaterKeys.map fun (key, path) =>
      (hex key, { fingerprint := masterFingerprint, path := parsePath path }) }

example : (match (role 0).update updaterData with
    | .ok psbt => psbt.sameRecords (role 1)
    | .error _ => false) = true := by native_decide

example : (match (role 1).setSighashType 0 1 >>= (·.setSighashType 1 1) with
    | .ok psbt => psbt.sameRecords (role 2)
    | .error _ => false) = true := by native_decide

-- Both inputs pass the BIP174 signer checks: a legacy P2SH multisig and a
-- P2SH-P2WSH multisig.
example : (match (decodedOf (role 2)).spendKind 0, (decodedOf (role 2)).spendKind 1 with
    | .ok (.legacy _), .ok (.witnessV0 _ _) => true
    | _, _ => false) = true := by native_decide

-- Each fixture violates one signer check on some input.
example : bip174SignerFailures.all (fun (_, bytes, _) =>
    let decoded := decodedOf (psbtOf bytes)
    (List.range decoded.inputs.length).any fun index =>
      (decoded.spendKind index).toBool == false) = true := by native_decide

private def partialSigs (psbt : Psbt) : List (Nat × ByteArray × ByteArray) :=
  (decodedOf psbt).inputs.zipIdx.flatMap fun (input, index) =>
    input.partialSigs.map fun (key, signature) => (index, key, signature)

-- Every official ECDSA signature verifies against the digest computed here:
-- legacy for input 0 and BIP143 for input 1, with SIGHASH_ALL and with
-- SIGHASH_ALL|ANYONECANPAY.
example : (partialSigs (role 3) ++ partialSigs (role 4)).all (fun (index, key, signature) =>
    (decodedOf (role 2)).verifyPartialSig index ECDSA.verify key signature) = true := by
  native_decide
example : (partialSigs (role 3) ++ partialSigs (role 4)).length = 4 := by native_decide
example : (partialSigs (role 12)).all (fun (index, key, signature) =>
    (decodedOf (role 11)).verifyPartialSig index ECDSA.verify key signature) = true := by
  native_decide

-- A modified signature is rejected by the signer integration point.
private def flipLast (bytes : ByteArray) : ByteArray :=
  ⟨bytes.data.set! (bytes.size - 2) (bytes[bytes.size - 2]! ^^^ 1)⟩
example : (partialSigs (role 3)).all (fun (index, key, signature) =>
    ((role 2).addPartialSig index ECDSA.verify key (flipLast signature)).toBool == false) = true := by
  native_decide

example : (match (partialSigs (role 3)).foldlM (fun psbt (index, key, signature) =>
      psbt.addPartialSig index ECDSA.verify key signature) (role 2) with
    | .ok psbt => psbt.sameRecords (role 3)
    | .error _ => false) = true := by native_decide

/-! ## BIP174 combiner -/

example : (match (role 3).combine (role 4), (role 4).combine (role 3) with
    | .ok first, .ok second => first.sameRecords (role 5) && second.sameRecords (role 5)
    | _, _ => false) = true := by native_decide

-- Unknown records are kept; this combination reproduces the official bytes.
example : (match (role 8).combine (role 9) with
    | .ok psbt => psbt.serialize == roleBytes 10
    | .error _ => false) = true := by native_decide

example : (match (role 11).combine (role 12), (role 12).combine (role 11) with
    | .ok first, .ok second => first.sameRecords (role 13) && second.sameRecords (role 13)
    | _, _ => false) = true := by native_decide

example : (match Psbt.combineAll [role 2, role 3, role 4] with
    | .ok psbt => psbt.sameRecords (role 5)
    | .error _ => false) = true := by native_decide

-- PSBTs for different transactions are not combined.
example : (match (role 5).combine (role 8) with
    | .error .differentTransactions => true
    | _ => false) = true := by native_decide

/-! ## BIP174 finalizer and extractor -/

private def multisigKeys : List PubKey :=
  [PubKey.ofBytes (hex "03089dc10c7ac6db54f91329af617333db388cead0c231f723379d1b99030b02dc"),
   PubKey.ofBytes (hex "023add904f3d6dcf59ddb906b0dee23529b7ffb9ed50e5e86151926860221f0e73")]
private def shWshMultisig : OutputDescriptor := .shWsh (.core (.multi 2 multisigKeys))

private def legacyMultisigKeys : List PubKey :=
  [PubKey.ofBytes (hex "029583bf39ae0a609747ad199addd634fa6108559d6c5cd39b4c2183f1ab96e07f"),
   PubKey.ofBytes (hex "02dab61ff49a14db6a7d02b0cd1fbb78fc4b18312b5b4e54dae4dba2fbfef536d7")]
private def shLegacyMultisig : OutputDescriptor :=
  .sh (.core (.multi 2 legacyMultisigKeys))

-- Input 1 is P2SH-P2WSH: the descriptor finalizer reproduces its official
-- final scriptSig and witness byte for byte. Input 0 is legacy P2SH and is
-- finalized through the legacy script context below.
example : (match (role 5).finalizeInput {} 1 shWshMultisig with
    | .ok psbt => psbt.inputs[1]! == (role 6).inputs[1]! && psbt.inputs[0]! == (role 5).inputs[0]!
    | .error _ => false) = true := by native_decide

-- Input 0 is the legacy P2SH half of the same official role vector. Its
-- scriptSig is built from the legacy ECDSA signatures and redeem script.
example : (match (role 5).finalizeInput {} 0 shLegacyMultisig with
    | .ok psbt => psbt.inputs[0]! == (role 6).inputs[0]! && psbt.inputs[1]! == (role 5).inputs[1]!
    | .error _ => false) = true := by native_decide

-- The wrapped witness must reach both P2SH and witness verification even
-- when the caller supplies fewer flags than the default configuration.
example : ((role 5).finalizeInput
    { flags := { witness := false, cleanStack := false, p2sh := true } }
    1 shWshMultisig).toBool = false := by native_decide

example : ((role 5).finalizeInput
    { flags := { witness := true, cleanStack := false, p2sh := false } }
    1 shWshMultisig).toBool = false := by native_decide

-- The complete verifier checks signature encoding even if a supplied
-- material-verification callback accepts malformed signatures.
example : (let decoded := decodedOf (role 5)
    let input := { decoded.inputs[1]! with
      partialSigs := multisigKeys.map (fun key => (key.bytes, hex "01")) }
    finalizeWitnessV0 { verifyECDSA := fun _ _ _ => true }
      decoded 1 input shWshMultisig (.core (.multi 2 multisigKeys))).toBool = false := by
  native_decide

example : (match (role 6).extract with
    | .ok bytes => bytes == roleBytes 7
    | .error _ => false) = true := by native_decide

-- The extracted transaction parses with its witnesses, re-serializes to the
-- same bytes and spends the unsigned transaction's outpoints.
example : (match parseTransaction (roleBytes 7), (decodedOf (role 6)).unsignedTransaction with
    | .ok parsed, .ok unsigned =>
        serializeWitnessTransaction parsed.transaction parsed.witnesses == roleBytes 7 &&
          parsed.witnesses.map List.length == [0, 4] &&
          (parsed.transaction.inputs.map (serializeOutPoint ·.previousOutput)) ==
            unsigned.inputs.map (serializeOutPoint ·.previousOutput)
    | _, _ => false) = true := by native_decide

-- Already finalized inputs are left unchanged.
example : (match (role 6).finalizeInput {} 1 shWshMultisig with
    | .ok psbt => psbt == role 6
    | .error _ => false) = true := by native_decide

-- Unfinalized inputs block extraction.
example : (match (role 5).extract with
    | .error (.notFinalized 0) => true
    | _ => false) = true := by native_decide

-- A sighash type disagreeing with the signatures blocks finalization.
example : (match (role 5).setSighashType 1 2 >>= fun psbt => .ok (psbt.finalizeInput {} 1 shWshMultisig) with
    | .ok (.error .sighashMismatch) => true
    | _ => false) = true := by native_decide

-- With one signature the 2-of-2 multisig is unavailable.
example : (match (role 3).finalizeInput {} 1 shWshMultisig with
    | .error .unavailable => true
    | _ => false) = true := by native_decide

-- A descriptor for another output is rejected.
example : (match (role 5).finalizeInput {} 1 (.wsh (.core (.multi 2 multisigKeys))) with
    | .error (.role (.scriptMismatch _)) => true
    | _ => false) = true := by native_decide

-- SIGHASH_ALL|ANYONECANPAY signatures agree with their sighash field.
example : (decodedOf (role 13)).inputs.all (·.sighashTypesMatch) = true := by native_decide

/-! ## BIP371 Taproot finalizer and updater -/

private def taproot (index : Nat) : Psbt := psbtOf bip371Valid[index]!.2.1

private def xonly (text : String) : PubKey := PubKey.ofBytes (hex text)
private def keyOnly : OutputDescriptor :=
  .tr (xonly "fe349064c98d6e2a853fa3c9b12bd8b304a19c195c60efa7ee2393046d3fa232") none
private def pkLeaf (key : String) : DescriptorTree := .leaf (.pk (xonly key))
private def nums : PubKey := xonly "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"
private def scriptTree : OutputDescriptor := .tr nums (some (.branch
  (.branch (pkLeaf "2cb13ac68248de806aa6a3659cf3c03eb6821d09c8114a4e868febde865bb6d2")
    (pkLeaf "fa0f7a3cef3b1d0c0a6ce7d26e17ada0b2e5c92d19efad48b41859cb8a451ca9"))
  (pkLeaf "4320b0bf16f011b53ea7be615924aa7f27e5d29ad20ea1155d848676c3bad1b2")))

-- The official key-path signature verifies against the BIP341 digest and the
-- tweaked output key, so it becomes the whole witness.
example : (match (taproot 1).finalizeInput {} 0 keyOnly with
    | .ok psbt => match (decodedOf psbt).inputs[0]?, (decodedOf (taproot 1)).inputs[0]? with
      | some final, some original =>
          final.finalScriptWitness == original.tapKeySig.map ([·]) &&
            final.tapKeySig.isNone && final.tapInternalKey.isNone && final.witnessUtxo.isSome
      | _, _ => false
    | .error _ => false) = true := by native_decide

-- Each official script-path signature passes Core verification; the leaf
-- with the shortest control block is selected.
private def leafWitness : List ByteArray :=
  [hex "e1f1ab6fabfa26b236f21833719dc1d428ab768d80f91f9988d8abef47bfb863bb1f2a529f768c15f00ce34ec283cdc07e88f8428be28f6ef64043c32911811a",
   hex "204320b0bf16f011b53ea7be615924aa7f27e5d29ad20ea1155d848676c3bad1b2ac",
   hex "c150929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac097c6e6fea5ff714ff5724499990810e406e98aa10f5bf7e5f6784bc1d0a9a6ce"]

example : (match (decodedOf (taproot 5)).finalInput {} 0 scriptTree with
    | .ok final => final.witness == leafWitness && final.scriptSig.size == 0
    | .error _ => false) = true := by native_decide

private def candidateCount : Nat :=
  match compileOutputDescriptor scriptTree, (decodedOf (taproot 5)).unsignedTransaction,
      (decodedOf (taproot 5)).spentOutputs, (decodedOf (taproot 5)).inputs[0]? with
  | .ok compiled, .ok tx, .ok spent, some input =>
      (scriptPathCandidates {} compiled input tx spent 0).length
  | _, _, _, _ => 0

example : candidateCount = 3 := by native_decide

-- The extracted transaction carries the selected witness.
example : (match (taproot 5).finalizeInput {} 0 scriptTree >>= fun psbt =>
      (psbt.extract.mapError .role) with
    | .ok bytes => match parseTransaction bytes with
      | .ok parsed => parsed.witnesses == [leafWitness]
      | .error _ => false
    | .error _ => false) = true := by native_decide

-- Without signatures nothing is available.
example : (match (taproot 3).finalizeInput {} 0 scriptTree, (taproot 0).finalizeInput {} 0 keyOnly with
    | .error .unavailable, .error .unavailable => true
    | _, _ => false) = true := by native_decide

-- A key-path signature for another message is not used.
example : (match (taproot 1).modifyInput 0 (·.insert (recordKey KeyType.inTapKeySig)
      leafWitness[0]!) with
    | .ok psbt => match psbt.finalizeInput {} 0 keyOnly with
      | .error .unavailable => true
      | _ => false
    | .error _ => false) = true := by native_decide

private def tapOrigins (psbt : Psbt) : List (ByteArray × KeySource) :=
  ((decodedOf psbt).inputs.flatMap (·.tapBip32Derivation) ++
    (decodedOf psbt).outputs.flatMap (·.tapBip32Derivation)).map fun (key, source) =>
      (key, source.source)

private def onlyUtxo (map : KeyValueMap) : KeyValueMap :=
  map.filter fun record => record.key == recordKey KeyType.inWitnessUtxo

-- The descriptor updater recreates the official Taproot input fields: leaf
-- scripts, internal key, Merkle root and key origins with leaf hashes.
example : (match ({ taproot 3 with inputs := (taproot 3).inputs.map onlyUtxo }).updateInputFromDescriptor
      0 scriptTree (tapOrigins (taproot 3)) with
    | .ok psbt => psbt.sameRecords (taproot 3)
    | .error _ => false) = true := by native_decide

example : (match ({ taproot 0 with inputs := (taproot 0).inputs.map onlyUtxo }).updateInputFromDescriptor
      0 keyOnly (tapOrigins (taproot 0)) with
    | .ok psbt => psbt.sameRecords (taproot 0)
    | .error _ => false) = true := by native_decide

private def outputTree : OutputDescriptor := .tr nums (some (.branch
  (.branch (pkLeaf "736e572900fe1252589a2143c8f3c79f71a0412d2353af755e9701c782694a02")
    (pkLeaf "631c5f3b5832b8fbdebfb19704ceeb323c21f40f7a24f43d68ef0cc26b125969"))
  (pkLeaf "44faa49a0338de488c8dfffecdfb6f329f380bd566ef20c8df6d813eab1c4273")))

-- The output updater recreates the official TAP_TREE and key origins.
example : (match ({ taproot 4 with outputs := [[]] }).updateOutputFromDescriptor
      0 outputTree (tapOrigins (taproot 4)) with
    | .ok psbt => psbt.sameRecords (taproot 4)
    | .error _ => false) = true := by native_decide

example : (match ({ taproot 2 with outputs := [[]] }).updateOutputFromDescriptor 0
      (.tr (xonly "1124da7aec92ccd06c954562647f437b138b95721a84be2bf2276bbddab3e671") none)
      (tapOrigins (taproot 2)) with
    | .ok psbt => psbt.outputs == (taproot 2).outputs
    | .error _ => false) = true := by native_decide

-- Descriptor key expressions supply the same origins as the BIP174 updater.
example : bip174UpdaterKeys.all (fun (key, path) =>
    match keySourceOf s!"[d90c6a4f{(path.drop 1).toString.replace "'" "h"}]{key}" with
    | .ok (bytes, source) => bytes == hex key && source.fingerprint == masterFingerprint &&
        source.path == parsePath path
    | .error _ => false) = true := by native_decide

-- The witness-v0 descriptor updater adds the scripts and origins of the
-- BIP174 updater for the P2SH-P2WSH input.
example : (match (role 0).updateInputFromDescriptor 1 shWshMultisig updaterData.keyOrigins with
    | .ok psbt => psbt.inputs[1]!.sameRecords ((role 1).inputs[1]!.filter fun record =>
        record.key != recordKey KeyType.inWitnessUtxo)
    | .error _ => false) = true := by native_decide

/-! ## BIP370 creator and conversion -/

-- A version-2 PSBT built from the creator transaction reconstructs it, and
-- is a different PSBT version from the version-0 one.
example : (match Psbt.createV2 creatorTransaction with
    | .ok psbt => match psbt.decode with
      | .ok decoded => match decoded.unsignedTransaction with
        | .ok tx => serializeTransaction tx == serializeTransaction creatorTransaction &&
            decoded.global.psbtVersion == 2
        | .error _ => false
      | .error _ => false
    | .error _ => false) = true := by native_decide

-- BIP370 valid PSBTs combine with themselves, as the combiner theorems state.
example : bip370Valid.all (fun (_, bytes, _) =>
    match (psbtOf bytes).combine (psbtOf bytes) with
    | .ok psbt => psbt == psbtOf bytes
    | .error _ => false) = true := by native_decide

end LeanMiniscript.Psbt.RoleExamples
