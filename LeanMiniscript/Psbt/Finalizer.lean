import LeanMiniscript.Psbt.Roles
import LeanMiniscript.Extraction.DescriptorSatisfaction
import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Bitcoin.ECDSA

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Script
open LeanMiniscript.Extraction

/-!
# Descriptor-based input finalizer

The finalizer turns an input's PSBT records into satisfaction material and
asks the existing Miniscript satisfier for the final witness:

* `pk`, `pkh`, `sh`, `wpkh`, `sh(wpkh)`, `wsh`, and `sh(wsh)`: partial
  signatures that verify against their legacy or BIP143
  digest and 32-byte hash preimages form a `DescriptorSatisfactionMaterial`;
  `satisfyFinal` on the sane witness-script fragment supplies the witness
  arguments, followed by the witness script. The complete Core script-pair
  verifier checks the resulting scriptSig and witness before returning them.
* `tr`: a key-path signature that verifies against the output key is used
  when present. Otherwise every leaf is tried with
  `satisfyDescriptorTransaction`, using that leaf's `TAP_SCRIPT_SIG` records
  and the PSBT preimages; it filters material and runs the complete Core
  verifier model. The smallest verified witness is chosen, earliest leaf
  first on ties.

Nonpreimage dissatisfaction material is 32 zero bytes. Raw descriptors retain
their exact script bytes; satisfaction generation remains available for the
typed and single-key forms. Already finalized inputs are left unchanged.
-/

inductive FinalizeError where
  | role (error : RoleError)
  | sighashMismatch
  | notSane (error : SaneError)
  | unavailable
  | witnessTooLarge
  deriving Repr, DecidableEq

/-- Verification callbacks and flags used during finalization. -/
structure FinalizerConfig where
  oracle : CryptoOracle := CryptoOracle.pureLeanSchnorr
  flags : CoreVerificationFlags :=
    { witness := true, taproot := true, cleanStack := true
      checkLockTimeVerify := true, checkSequenceVerify := true }
  /-- ECDSA verification of a signature without its hash-type byte. -/
  verifyECDSA : ByteArray → ByteArray → ByteArray → Bool := ECDSA.verify

/-- Final scriptSig and witness stack for one input. -/
structure FinalInput where
  scriptSig : ByteArray := ByteArray.empty
  witness : List ByteArray := []
  deriving Repr, DecidableEq, Inhabited

/-- CompactSize encodes the witness item count and each item length as uint64. -/
def FinalInput.WitnessFits (final : FinalInput) : Prop :=
  final.witness.length < 2 ^ 64 ∧ ∀ item ∈ final.witness, item.size < 2 ^ 64

/-- Validate witness lengths before writing final fields to a PSBT. -/
def FinalInput.checkWitness (final : FinalInput) : Except FinalizeError FinalInput :=
  if final.witness.length < 2 ^ 64 && final.witness.all (fun item => item.size < 2 ^ 64) then
    .ok final
  else .error .witnessTooLarge

/-! ## Satisfaction material from PSBT records -/

private def lookupBytes (entries : List (ByteArray × ByteArray)) (key : ByteArray) :
    Option ByteArray :=
  (entries.find? (fun entry => entry.1 == key)).map (·.2)

/-- The PSBT preimage for a typed hashlock, keyed by its digest. -/
def InputFields.preimageFor (input : InputFields) : HashLock → Option StackElement
  | .sha256 hash => lookupBytes input.sha256Preimages hash.bytes
  | .hash256 hash => lookupBytes input.hash256Preimages hash.bytes
  | .ripemd160 hash => lookupBytes input.ripemd160Preimages hash.bytes
  | .hash160 hash => lookupBytes input.hash160Preimages hash.bytes

def zeroNonPreimage : StackElement := ⟨Array.replicate 32 0⟩

/-- Tapscript material for one leaf: `TAP_SCRIPT_SIG` records for this leaf
hash and all preimages. `satisfyDescriptorTransaction` filters both. -/
def InputFields.tapscriptMaterial (input : InputFields) (leafHash : ByteArray) :
    DescriptorSatisfactionMaterial where
  signatureFor key := (input.tapScriptSigs.find? (fun entry =>
    entry.1.1 == key.bytes && entry.1.2 == leafHash)).map (·.2)
  preimageFor := input.preimageFor
  nonPreimageFor _ := zeroNonPreimage

/-- Witness-v0 material: partial signatures accepted by `accept`, and
preimages of the 32 bytes required by BIP379 hashlocks. -/
def InputFields.witnessV0Material (input : InputFields)
    (accept : ByteArray → ByteArray → Bool) : DescriptorSatisfactionMaterial where
  signatureFor key := (lookupBytes input.partialSigs key.bytes).filter (accept key.bytes)
  preimageFor lock := (input.preimageFor lock).filter (·.size == 32)
  nonPreimageFor _ := zeroNonPreimage

/-- Legacy material uses the same PSBT records as witness-v0 material, with a
legacy signature-hash callback supplied by the finalizer. -/
def InputFields.legacyMaterial (input : InputFields)
    (accept : ByteArray → ByteArray → Bool) : DescriptorSatisfactionMaterial where
  signatureFor key := (lookupBytes input.partialSigs key.bytes).filter (accept key.bytes)
  preimageFor lock := (input.preimageFor lock).filter (·.size == 32)
  nonPreimageFor _ := zeroNonPreimage

/-- Script execution context for a witness-v0 input. Signature digests are
checked per signature by the material filter, so the abstract hash is empty. -/
def witnessV0Context (tx : Transaction) (index : Nat) : TxContext :=
  { version := tx.signedVersion
    locktime := tx.locktime.toNat
    sequence := (tx.inputs[index]!).sequence.toNat
    sigHash := ByteArray.empty
    sigVersion := .witnessV0 }

/-- Script execution context for a legacy input. -/
def legacyContext (tx : Transaction) (index : Nat) : TxContext :=
  { version := tx.signedVersion
    locktime := tx.locktime.toNat
    sequence := (tx.inputs[index]!).sequence.toNat
    sigHash := ByteArray.empty
    sigVersion := .base }

/-- Accept an ECDSA partial signature when it verifies against the BIP143
digest selected by its own hash-type byte. -/
def witnessV0Accept (config : FinalizerConfig) (tx : Transaction) (index : Nat)
    (witnessScript : ByteArray) (amount : UInt64) (key signature : ByteArray) : Bool :=
  signature.size != 0 &&
    match witnessV0SignatureHash tx index witnessScript amount
        (UInt32.ofNat signature[signature.size - 1]!.toNat) with
    | .ok digest => config.verifyECDSA (signature.extract 0 (signature.size - 1)) key digest
    | .error _ => false

/-- Accept an ECDSA partial signature using legacy SIGHASH serialization. -/
def legacyAccept (config : FinalizerConfig) (tx : Transaction) (index : Nat)
    (scriptCode key signature : ByteArray) : Bool :=
  signature.size != 0 &&
    match legacySignatureHash tx index scriptCode
        (UInt32.ofNat signature[signature.size - 1]!.toNat) with
    | .ok digest => config.verifyECDSA (signature.extract 0 (signature.size - 1)) key digest
    | .error _ => false

/-- The satisfaction environment used for a witness-v0 input. -/
def witnessV0Env (config : FinalizerConfig) (tx : Transaction) (index : Nat)
    (input : InputFields) (witnessScript : ByteArray) (amount : UInt64) : SatEnv :=
  (input.witnessV0Material (witnessV0Accept config tx index witnessScript amount)).toEnv
    (witnessV0Context tx index)

/-- The satisfaction environment used for a legacy script-hash input. -/
def legacyEnv (config : FinalizerConfig) (tx : Transaction) (index : Nat)
    (input : InputFields) (scriptCode : ByteArray) : SatEnv :=
  (input.legacyMaterial (legacyAccept config tx index scriptCode)).toEnv
    (legacyContext tx index)

/-- Transaction-backed Core execution for a finalized witness-v0 input. The
signature callback derives the BIP143 or legacy digest from the signature's
hash-type byte, matching the PSBT preflight used to select material. -/
def witnessV0CoreExecutor (config : FinalizerConfig) (tx : Transaction)
    (index : Nat) (amount : UInt64) : CoreScriptExecutor :=
  let oracleForScript := fun version scriptCode =>
    CryptoOracle.pureLeanHashes (fun signature publicKey _ =>
      if signature.size == 0 then false
      else
        let hashType := UInt32.ofNat signature[signature.size - 1]!.toNat
        let digest := if version == .witnessV0 then
          witnessV0SignatureHash tx index scriptCode amount hashType
        else legacySignatureHash tx index scriptCode hashType
        match digest with
        | .error _ => false
        | .ok digest => config.verifyECDSA (signature.extract 0 (signature.size - 1))
            publicKey digest) config.oracle.checkSchnorrSig
  fun request => executeCoreScript config.flags (witnessV0Context tx index)
    oracleForScript request

/-- Transaction-backed Core execution for a legacy input. -/
def legacyCoreExecutor (config : FinalizerConfig) (tx : Transaction)
    (index : Nat) : CoreScriptExecutor :=
  let oracleForScript := fun _ scriptCode =>
    CryptoOracle.pureLeanHashes (fun signature publicKey _ =>
      if signature.size == 0 then false
      else
        let hashType := UInt32.ofNat signature[signature.size - 1]!.toNat
        match legacySignatureHash tx index scriptCode hashType with
        | .error _ => false
        | .ok digest => config.verifyECDSA (signature.extract 0 (signature.size - 1))
            publicKey digest) config.oracle.checkSchnorrSig
  fun request => executeCoreScript config.flags (legacyContext tx index)
    oracleForScript request

/-- Verify a finalized P2WSH or P2SH-P2WSH witness through the same Core
script-pair and witness-program boundary used by Taproot finalization. -/
def verifyWitnessV0Final (config : FinalizerConfig) (tx : Transaction)
    (index : Nat) (compiled : CompiledDescriptor) (final : FinalInput)
    (amount : UInt64) : Except CoreVerificationError Unit := do
  if !(config.flags.witness || config.flags.cleanStack) then
    throw (.unsupported "witness verification disabled")
  if compiled.redeemScript.isSome && !(config.flags.p2sh || config.flags.cleanStack) then
    throw (.unsupported "P2SH verification disabled")
  let execute := witnessV0CoreExecutor config tx index amount
  verifyCoreScripts execute
    (fun witness version program isP2SH =>
      verifyCoreWitnessProgram execute config.flags witness version program isP2SH)
    config.flags final.scriptSig compiled.scriptPubKey final.witness

/-- Verify a legacy script pair through Core's scriptSig, scriptPubKey, and
P2SH boundary. A legacy descriptor must not carry witness data. -/
def verifyLegacyFinal (config : FinalizerConfig) (tx : Transaction)
    (index : Nat) (compiled : CompiledDescriptor) (final : FinalInput) :
    Except CoreVerificationError Unit := do
  if !final.witness.isEmpty then throw (.unsupported "legacy witness data")
  let execute := legacyCoreExecutor config tx index
  verifyCoreScripts execute
    (fun _ _ _ _ => throw (.unsupported "legacy witness program"))
    config.flags final.scriptSig compiled.scriptPubKey final.witness

/-! ## Signature hash-type agreement -/

/-- With `PSBT_IN_SIGHASH_TYPE`, every signature must carry that type. A
64-byte Schnorr signature carries SIGHASH_DEFAULT (0). -/
def InputFields.sighashTypesMatch (input : InputFields) : Bool :=
  match input.sighashType with
  | none => true
  | some expected =>
      let schnorrType := fun (signature : ByteArray) =>
        if signature.size == 65 then signature[64]!.toNat else 0
      input.partialSigs.all (fun (_, signature) =>
        signature.size != 0 && signature[signature.size - 1]!.toNat == expected.toNat) &&
      input.tapKeySig.all (fun signature => schnorrType signature == expected.toNat) &&
      input.tapScriptSigs.all (fun (_, signature) => schnorrType signature == expected.toNat)

private def serializeArguments (arguments : Witness) : ByteArray :=
  arguments.foldl (fun script argument => script ++ pushData argument) ByteArray.empty

/-- Descriptor and transaction data shared by legacy and witness-v0 finalizers. -/
structure FinalizationContext where
  compiled : CompiledDescriptor
  spent : TxOutput
  transaction : Transaction

/-- Compile the descriptor and load the selected UTXO and unsigned transaction,
in the order used by legacy and witness-v0 finalization. -/
def prepareFinalization (decoded : DecodedPsbt) (index : Nat)
    (descriptor : OutputDescriptor) : Except FinalizeError FinalizationContext := do
  let compiled ← (compileDescriptor descriptor).mapError .role
  let spent ← (decoded.spentOutput index).mapError .role
  let transaction ← (liftPsbt decoded.unsignedTransaction).mapError .role
  return { compiled, spent, transaction }

/-- Require the selected UTXO to commit to the compiled descriptor output. -/
def checkFinalizerOutput (compiled : CompiledDescriptor) (spent : TxOutput) :
    Except FinalizeError Unit := do
  if spent.scriptPubKey ≠ compiled.scriptPubKey then
    throw (.role (.scriptMismatch "UTXO script is not the descriptor output"))

/-! ## Legacy and single-key finalization -/

def finalizeLegacyFragment (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) (fragment : SurfaceFragment) :
    Except FinalizeError FinalInput := do
  let ⟨compiled, spent, tx⟩ ← prepareFinalization decoded index descriptor
  let some redeemScript := compiled.redeemScript
    | throw (.role (.descriptor "legacy descriptor has no redeem script"))
  checkFinalizerOutput compiled spent
  if input.redeemScript.any (· != redeemScript) || input.witnessScript.isSome then
    throw (.role (.scriptMismatch "PSBT scripts differ from the descriptor"))
  let env := legacyEnv config tx index input redeemScript
  let arguments := match fragment with
    | .pk _ | .pkh _ | .core (.multi _ _) => satisfyFinal (desugar fragment) env
    | _ =>
        match checkSaneSurface .p2wsh fragment with
        | .error _ => none
        | .ok sane => satisfyFinal sane.checked.fragment env
  match arguments with
  | none => throw .unavailable
  | some arguments =>
      let final := { scriptSig := serializeArguments arguments ++ pushData redeemScript }
      match verifyLegacyFinal config tx index compiled final with
      | .ok () => return final
      | .error _ => throw .unavailable

def finalizeLegacyMulti (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) (threshold : Nat) (keys : List PubKey) :
    Except FinalizeError FinalInput := do
  let ⟨compiled, spent, tx⟩ ← prepareFinalization decoded index descriptor
  checkFinalizerOutput compiled spent
  if input.redeemScript.isSome || input.witnessScript.isSome then
    throw (.role (.scriptMismatch "PSBT scripts differ from the descriptor"))
  let fragment := SurfaceFragment.core (.multi threshold keys)
  match satisfyFinal (desugar fragment)
      (legacyEnv config tx index input compiled.scriptPubKey) with
  | none => throw .unavailable
  | some arguments =>
      let final := { scriptSig := serializeArguments arguments }
      match verifyLegacyFinal config tx index compiled final with
      | .ok () => return final
      | .error _ => throw .unavailable

def finalizeLegacySingle (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) (key : PubKey) (pkh : Bool) :
    Except FinalizeError FinalInput := do
  let ⟨compiled, spent, tx⟩ ← prepareFinalization decoded index descriptor
  checkFinalizerOutput compiled spent
  if input.redeemScript.isSome || input.witnessScript.isSome then
    throw (.role (.scriptMismatch "PSBT scripts differ from the descriptor"))
  let some signature := lookupBytes input.partialSigs key.bytes | throw .unavailable
  if !legacyAccept config tx index compiled.scriptPubKey key.bytes signature then
    throw .unavailable
  let arguments := if pkh then [signature, key.bytes] else [signature]
  let final := { scriptSig := serializeArguments arguments }
  match verifyLegacyFinal config tx index compiled final with
  | .ok () => return final
  | .error _ => throw .unavailable

def finalizeWpkh (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) (key : PubKey) :
    Except FinalizeError FinalInput := do
  let ⟨compiled, spent, tx⟩ ← prepareFinalization decoded index descriptor
  checkFinalizerOutput compiled spent
  let expectedProgram := ScriptBytes.p2wpkh (LeanHash160.hash160 key.bytes)
  if compiled.redeemScript.any (· != expectedProgram) || input.witnessScript.isSome ||
      input.redeemScript.any (· != expectedProgram) then
    throw (.role (.scriptMismatch "PSBT scripts differ from the descriptor"))
  let scriptCode := p2pkhScript (LeanHash160.hash160 key.bytes)
  let some signature := lookupBytes input.partialSigs key.bytes | throw .unavailable
  if !witnessV0Accept config tx index scriptCode spent.amount key.bytes signature then
    throw .unavailable
  let final := { scriptSig := (compiled.redeemScript.map pushData).getD ByteArray.empty
                 witness := [signature, key.bytes] }
  match verifyWitnessV0Final config tx index compiled final spent.amount with
  | .ok () => return final
  | .error _ => throw .unavailable

/-! ## Witness-v0 finalization -/

def finalizeWitnessV0 (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) (fragment : SurfaceFragment) :
    Except FinalizeError FinalInput := do
  let ⟨compiled, spent, tx⟩ ← prepareFinalization decoded index descriptor
  let some witnessScript := compiled.witnessScript
    | throw (.role (.descriptor "descriptor has no witness script"))
  checkFinalizerOutput compiled spent
  if input.witnessScript.any (· != witnessScript) ||
      input.redeemScript.any (fun script => compiled.redeemScript != some script) then
    throw (.role (.scriptMismatch "PSBT scripts differ from the descriptor"))
  let sane ← (checkSaneSurface .p2wsh fragment).mapError .notSane
  match satisfyFinal sane.checked.fragment
      (witnessV0Env config tx index input witnessScript spent.amount) with
  | none => throw .unavailable
  | some arguments =>
      let final := { scriptSig := (compiled.redeemScript.map pushData).getD ByteArray.empty
                     witness := arguments ++ [witnessScript] }
      match verifyWitnessV0Final config tx index compiled final spent.amount with
      | .ok () => return final
      | .error _ => throw .unavailable

/-! ## Taproot finalization -/

/-- A key-path signature with valid encoding that verifies against the
output key and the BIP341 key-path digest. -/
def keyPathValid (config : FinalizerConfig) (tx : Transaction) (spentOutputs : Array TxOutput)
    (index : Nat) (outputKey signature : ByteArray) : Bool :=
  match checkSchnorrSignatureEncoding signature with
  | .error _ => false
  | .ok () =>
      match Bitcoin.taprootSignatureHash
          { transaction := tx, spentOutputs, inputIndex := index }
          (if signature.size == 65 then signature[64]! else 0) with
      | .error _ => false
      | .ok digest => config.oracle.checkSchnorrSig (signature.extract 0 64) outputKey digest

/-- Every leaf whose generated witness passes `satisfyDescriptorTransaction`. -/
def scriptPathCandidates (config : FinalizerConfig) (compiled : CompiledDescriptor)
    (input : InputFields) (tx : Transaction) (spentOutputs : Array TxOutput) (index : Nat) :
    List (Nat × PreparedDescriptorSatisfaction) :=
  (List.range compiled.taprootLeaves.length).filterMap fun leafIndex =>
    match compiled.taprootLeaves[leafIndex]? with
    | none => none
    | some leaf =>
        match satisfyDescriptorTransaction config.oracle config.flags compiled leafIndex
            (input.tapscriptMaterial (tapleafHash leaf.script 0xc0)) tx spentOutputs index with
        | .ok prepared => some (leafIndex, prepared)
        | .error _ => none

/-- Serialized size of a witness stack. -/
def witnessSize (witness : List ByteArray) : Nat := (serializeWitness witness).size

/-- The candidate with the smallest witness; the earliest wins ties. -/
def bestCandidate {α : Type} (size : α → Nat) : List α → Option α
  | [] => none
  | first :: rest => some (rest.foldl (fun best next =>
      if size next < size best then next else best) first)

def finalizeTaproot (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (input : InputFields) (descriptor : OutputDescriptor) : Except FinalizeError FinalInput := do
  let compiled ← (compileDescriptor descriptor).mapError .role
  let tx ← (liftPsbt decoded.unsignedTransaction).mapError .role
  let spentOutputs ← decoded.spentOutputs.mapError .role
  let some spent := spentOutputs[index]? | throw (.role .inputIndex)
  checkFinalizerOutput compiled spent
  let outputKey := compiled.scriptPubKey.extract 2 34
  match input.tapKeySig with
  | some signature =>
      if keyPathValid config tx spentOutputs index outputKey signature then
        return { witness := [signature] }
  | none => pure ()
  match bestCandidate (fun candidate => witnessSize candidate.2.witness)
      (scriptPathCandidates config compiled input tx spentOutputs index) with
  | none => throw .unavailable
  | some (_, prepared) => return { witness := prepared.witness }

/-! ## Input and PSBT finalizers -/

/-- Final scriptSig and witness for an input spending `descriptor`. -/
def DecodedPsbt.finalInput (config : FinalizerConfig) (decoded : DecodedPsbt) (index : Nat)
    (descriptor : OutputDescriptor) : Except FinalizeError FinalInput := do
  let input ← (decoded.input index).mapError .role
  if !input.sighashTypesMatch then throw .sighashMismatch
  let final ← match descriptor with
    | .raw _ | .shRaw _ => throw .unavailable
    | .pk key => finalizeLegacySingle config decoded index input descriptor key false
    | .pkh key => finalizeLegacySingle config decoded index input descriptor key true
    | .multi threshold keys =>
        finalizeLegacyMulti config decoded index input descriptor threshold keys
    | .sh fragment => finalizeLegacyFragment config decoded index input descriptor fragment
    | .wpkh key | .shWpkh key => finalizeWpkh config decoded index input descriptor key
    | .wsh fragment | .shWsh fragment => finalizeWitnessV0 config decoded index input descriptor fragment
    | .tr _ _ => finalizeTaproot config decoded index input descriptor
  final.checkWitness

/-- Input key types defined by BIP174, BIP370 and BIP371. -/
def knownInputKeyTypes : List Nat :=
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x0a, 0x0b, 0x0c, 0x0d,
   0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]

/-- Records a finalizer keeps: UTXOs, the BIP370 transaction fields and
records of types it does not define, including proprietary records. -/
def keepAfterFinalize (record : Record) : Bool :=
  match record.keyType? with
  | none => true
  | some keyType =>
      [0x00, 0x01, 0x0e, 0x0f, 0x10, 0x11, 0x12].contains keyType ||
        !knownInputKeyTypes.contains keyType

/-- Clear the input map and add the final fields; empty fields stay unset. -/
def finalizedInputMap (map : KeyValueMap) (final : FinalInput) : KeyValueMap :=
  map.filter keepAfterFinalize ++
    (if final.scriptSig.size == 0 then []
     else [⟨recordKey KeyType.inFinalScriptSig, final.scriptSig⟩]) ++
    (if final.witness.isEmpty then []
     else [⟨recordKey KeyType.inFinalScriptWitness, serializeWitness final.witness⟩])

def InputFields.isFinalized (input : InputFields) : Bool :=
  input.finalScriptSig.isSome || input.finalScriptWitness.isSome

/-- BIP174 input finalizer for one input. -/
def Psbt.finalizeInput (config : FinalizerConfig) (psbt : Psbt) (index : Nat)
    (descriptor : OutputDescriptor) : Except FinalizeError Psbt := do
  let decoded ← (liftPsbt psbt.decode).mapError .role
  let input ← (decoded.input index).mapError .role
  if input.isFinalized then return psbt
  let final ← decoded.finalInput config index descriptor
  let updated ← (psbt.modifyInput index (finalizedInputMap · final)).mapError .role
  updated.checked.mapError .role

/-- Finalize each input with a supplied descriptor; `none` skips an input. -/
def Psbt.finalize (config : FinalizerConfig) (psbt : Psbt)
    (descriptors : List (Option OutputDescriptor)) : Except FinalizeError Psbt :=
  (descriptors.zipIdx).foldlM (fun psbt (descriptor?, index) =>
    match descriptor? with
    | none => pure psbt
    | some descriptor => psbt.finalizeInput config index descriptor) psbt

/-- Finalize every input and extract the network transaction. -/
def Psbt.finalizeAndExtract (config : FinalizerConfig) (psbt : Psbt)
    (descriptors : List (Option OutputDescriptor)) : Except FinalizeError ByteArray := do
  let finalized ← psbt.finalize config descriptors
  finalized.extract.mapError .role

end LeanMiniscript.Psbt
