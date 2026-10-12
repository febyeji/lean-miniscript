import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Extraction.DescriptorSatisfactionMaterial
import LeanMiniscript.Miniscript.OutputDescriptor
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

inductive DescriptorSatisfactionError where
  | leafIndex
  | context (error : SighashError)
  | spentOutputMismatch
  | nonemptyScriptSig
  | notSane (error : SaneError)
  /-- No usable final satisfaction remains after filtering supplied material. -/
  | unavailable
  | witnessDisabled
  | taprootDisabled
  | verification (error : CoreVerificationError)
  deriving Repr, DecidableEq

/-- A generated no-annex script-path satisfaction. Successful preparation
establishes its source and context relationships and filters supplied signatures
and preimages. Core verification checks the complete witness. A raw record
carries no preparation invariant. -/
structure PreparedDescriptorSatisfaction where
  leaf : TaprootLeafSpendInfo
  sane : SaneFragment .tapscript
  context : TxContext
  arguments : Witness

/-- Complete witness in wire order, including the selected occurrence's
script and control block. -/
def PreparedDescriptorSatisfaction.witness (prepared : PreparedDescriptorSatisfaction) : Witness :=
  prepared.arguments ++ [prepared.leaf.script, prepared.leaf.controlBlock]

/-- Select a leaf by its occurrence in the compiled descriptor, validate the
transaction shape and spent-output binding, then generate its satisfaction from
material checked with the supplied execution oracle and flags.
The script-path context fixes leaf version 0xc0, no annex and no CODESEPARATOR.
Prevout provenance and whole-transaction validity remain caller obligations. -/
def prepareDescriptorSatisfaction (oracle : CryptoOracle) (flags : ScriptFlags)
    (descriptor : CompiledDescriptor) (leafIndex : Nat)
    (material : DescriptorSatisfactionMaterial) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except DescriptorSatisfactionError PreparedDescriptorSatisfaction := do
  let leaf ← match descriptor.taprootLeaves[leafIndex]? with
    | none => throw .leafIndex
    | some leaf => pure leaf
  let context ← (TxContext.fromTaproot
    { transaction, spentOutputs, inputIndex
      spendPath := .scriptPath leaf.script 0xc0 0xffffffff }).mapError .context
  if (spentOutputs[inputIndex]!).scriptPubKey.data ≠ descriptor.scriptPubKey.data then
    throw .spentOutputMismatch
  if (transaction.inputs[inputIndex]!).scriptSig.size != 0 then
    throw .nonemptyScriptSig
  let sane ← (checkSaneSurface .tapscript leaf.fragment).mapError .notSane
  let arguments ← match satisfyFinal sane.checked.fragment
      ((material.validated oracle flags context).toEnv context) with
    | none => throw .unavailable
    | some arguments => pure arguments
  return { leaf, sane, context, arguments }

/-- Verify a prepared witness through the complete Core script-pair entry
point, using its transaction context and the descriptor's output script. -/
def PreparedDescriptorSatisfaction.verify (prepared : PreparedDescriptorSatisfaction)
    (oracle : CryptoOracle) (flags : CoreVerificationFlags)
    (descriptor : CompiledDescriptor) : Except CoreVerificationError Unit :=
  let execute := executeCoreScript flags prepared.context (fun _ _ => oracle)
  verifyCoreScripts execute (fun witness version program isP2SH =>
    verifyCoreWitnessProgram execute flags witness version program isP2SH)
    flags ByteArray.empty descriptor.scriptPubKey prepared.witness

/-- Generate and verify a descriptor script-path witness. Witness and Taproot
verification must be enabled. Invalid supplied signatures and preimages are
excluded before selection. Setup, unavailable material and Core verification
failures retain distinct errors; successful results contain the full witness. -/
def satisfyDescriptorTransaction (oracle : CryptoOracle) (flags : CoreVerificationFlags)
    (descriptor : CompiledDescriptor) (leafIndex : Nat)
    (material : DescriptorSatisfactionMaterial) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except DescriptorSatisfactionError PreparedDescriptorSatisfaction := do
  if !flags.witness then throw .witnessDisabled
  if !flags.taproot then throw .taprootDisabled
  let prepared ← prepareDescriptorSatisfaction oracle flags.script descriptor leafIndex material
    transaction spentOutputs inputIndex
  prepared.verify oracle flags descriptor |>.mapError .verification
  return prepared

end LeanMiniscript.Extraction
