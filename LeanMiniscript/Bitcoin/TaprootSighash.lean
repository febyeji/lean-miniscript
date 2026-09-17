import LeanMiniscript.Bitcoin.TaggedHash
import LeanMiniscript.Bitcoin.Transaction

namespace LeanMiniscript.Bitcoin

/-!
Executable BIP341/342 signature messages and tagged SHA256. Transaction
validity, Taproot commitments and Schnorr/secp256k1 verification are separate
obligations. The Script AST has no CODESEPARATOR; standalone hash callers may
provide its position explicitly, while Script execution uses 0xffffffff.
-/

inductive SighashError where
  | invalidHashType
  | inputIndex
  | spentOutputCount
  | outpointHashSize
  | missingSingleOutput
  | invalidAnnex
  | invalidLeafVersion
  deriving Repr, DecidableEq, BEq

inductive TaprootSpendPath where
  | keyPath
  | scriptPath (scriptBytes : ByteArray) (leafVersion : UInt8) (codeSeparatorPos : UInt32)
  deriving Repr, Inhabited

/-- Spent outputs are aligned with transaction inputs. This API requires all
    prevouts even for ANYONECANPAY, although only the current one is committed
    in that mode. Prevout correctness is a caller obligation. -/
structure TaprootSigHashContext where
  transaction : Transaction
  spentOutputs : Array TxOutput
  inputIndex : Nat
  annex : Option ByteArray := none
  spendPath : TaprootSpendPath := .keyPath
  deriving Repr

def validTaprootHashType (hashType : UInt8) : Bool :=
  hashType == 0 || hashType == 1 || hashType == 2 || hashType == 3 ||
    hashType == 0x81 || hashType == 0x82 || hashType == 0x83

def taprootOutputType (hashType : UInt8) : Nat :=
  if hashType == 0 then 1 else hashType.toNat % 4

def taprootAnyoneCanPay (hashType : UInt8) : Bool :=
  hashType.toNat / 128 == 1

def tapleafHash (scriptBytes : ByteArray) (leafVersion : UInt8 := 0xc0) : ByteArray :=
  taggedHash "TapLeaf" (⟨#[leafVersion]⟩ ++ serializeByteVector scriptBytes)

def hashPrevouts (tx : Transaction) : ByteArray :=
  LeanHash160.SHA256.hash
    (tx.inputs.foldl (fun bytes input => bytes ++ serializeOutPoint input.previousOutput) ByteArray.empty)

def hashAmounts (spentOutputs : Array TxOutput) : ByteArray :=
  LeanHash160.SHA256.hash
    (spentOutputs.foldl (fun bytes output => bytes ++ ⟨(unsignedLE 8 output.amount.toNat).toArray⟩) ByteArray.empty)

def hashScriptPubKeys (spentOutputs : Array TxOutput) : ByteArray :=
  LeanHash160.SHA256.hash
    (spentOutputs.foldl (fun bytes output => bytes ++ serializeByteVector output.scriptPubKey) ByteArray.empty)

def hashSequences (tx : Transaction) : ByteArray :=
  LeanHash160.SHA256.hash
    (tx.inputs.foldl (fun bytes input => bytes ++ ⟨(unsignedLE 4 input.sequence.toNat).toArray⟩) ByteArray.empty)

def hashOutputs (tx : Transaction) : ByteArray :=
  LeanHash160.SHA256.hash
    (tx.outputs.foldl (fun bytes output => bytes ++ serializeTxOutput output) ByteArray.empty)

/-- Validate data-shape requirements before indexing or serializing fields.
    This is not full transaction consensus validation. -/
def validateTaprootContext (ctx : TaprootSigHashContext) : Except SighashError Unit :=
  if ctx.inputIndex ≥ ctx.transaction.inputs.size || ctx.inputIndex > 4294967295 then
    .error .inputIndex
  else if ctx.spentOutputs.size != ctx.transaction.inputs.size then .error .spentOutputCount
  else if ctx.transaction.inputs.any (fun input => input.previousOutput.txid.size != 32) then
    .error .outpointHashSize
  else if ctx.annex.any (fun annex => annex.size == 0 || annex[0]! != 0x50) then
    .error .invalidAnnex
  else match ctx.spendPath with
    | .scriptPath _ leafVersion _ =>
        if leafVersion.toNat % 2 != 0 then .error .invalidLeafVersion else .ok ()
    | .keyPath => .ok ()

def TaprootSpendPath.extensionFlag : TaprootSpendPath → Nat
  | .keyPath => 0
  | .scriptPath _ _ _ => 1

def TaprootSpendPath.extension : TaprootSpendPath → ByteArray
  | .keyPath => ByteArray.empty
  | .scriptPath script leafVersion codeSeparatorPos =>
      tapleafHash script leafVersion ++ ⟨#[0]⟩ ++
        ⟨(unsignedLE 4 codeSeparatorPos.toNat).toArray⟩

/-- Complete signing preimage: epoch 0, BIP341 SigMsg and the BIP342 extension
    when requested. DEFAULT commits as ALL but retains hash_type byte 0.
    SIGHASH_SINGLE without a corresponding output fails; no zero-hash fallback. -/
def taprootSignatureMessage (ctx : TaprootSigHashContext) (hashType : UInt8) :
    Except SighashError ByteArray := do
  if !validTaprootHashType hashType then throw .invalidHashType
  validateTaprootContext ctx
  let outputType := taprootOutputType hashType
  if outputType == 3 && ctx.inputIndex ≥ ctx.transaction.outputs.size then
    throw .missingSingleOutput
  let tx := ctx.transaction
  let input := tx.inputs[ctx.inputIndex]!
  let spent := ctx.spentOutputs[ctx.inputIndex]!
  let header : ByteArray := ⟨#[0, hashType]⟩ ++
    ⟨(unsignedLE 4 tx.version.toNat ++ unsignedLE 4 tx.locktime.toNat).toArray⟩
  let inputHashes := if taprootAnyoneCanPay hashType then ByteArray.empty else
    hashPrevouts tx ++ hashAmounts ctx.spentOutputs ++ hashScriptPubKeys ctx.spentOutputs ++ hashSequences tx
  let outputHash := if outputType == 1 then hashOutputs tx else ByteArray.empty
  let spendType := UInt8.ofNat (2 * ctx.spendPath.extensionFlag + if ctx.annex.isSome then 1 else 0)
  let currentInput := if taprootAnyoneCanPay hashType then
    serializeOutPoint input.previousOutput ++ ⟨(unsignedLE 8 spent.amount.toNat).toArray⟩ ++
      serializeByteVector spent.scriptPubKey ++ ⟨(unsignedLE 4 input.sequence.toNat).toArray⟩
    else ⟨(unsignedLE 4 ctx.inputIndex).toArray⟩
  let annexHash := match ctx.annex with
    | none => ByteArray.empty
    | some annex => LeanHash160.SHA256.hash (serializeByteVector annex)
  let singleHash := if outputType == 3 then
    LeanHash160.SHA256.hash (serializeTxOutput tx.outputs[ctx.inputIndex]!) else ByteArray.empty
  return header ++ inputHashes ++ outputHash ++ ⟨#[spendType]⟩ ++ currentInput ++
    annexHash ++ singleHash ++ ctx.spendPath.extension

def taprootSignatureHash (ctx : TaprootSigHashContext) (hashType : UInt8) :
    Except SighashError ByteArray :=
  (taprootSignatureMessage ctx hashType).map (taggedHash "TapSighash")

/-- This connects the hash API to the complete signing-message API. Hash and
    transaction consensus correctness are checked by external vectors, not
    claimed as cryptographic security theorems. -/
theorem taprootSignatureHash_of_message
    {ctx : TaprootSigHashContext} {hashType : UInt8} {message : ByteArray}
    (computed : taprootSignatureMessage ctx hashType = .ok message) :
    taprootSignatureHash ctx hashType = .ok (taggedHash "TapSighash" message) := by
  simp [taprootSignatureHash, computed, Except.map]

end LeanMiniscript.Bitcoin
