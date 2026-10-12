import LeanMiniscript.Extraction.DescriptorSatisfaction
import LeanMiniscript.Extraction.BitcoinCoreSatisfactionProofs

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

private theorem checkSane_source {ctx : ScriptContext} {fragment : CoreFragment}
    {sane : SaneFragment ctx} (checked : checkSane ctx fragment = .ok sane) :
    sane.checked.fragment = fragment := by
  unfold checkSane at checked
  repeat' (split at checked <;> try simp_all)
  subst sane
  rfl

/-- Successful preparation retains the selected occurrence and derives both
the source match and the generated-satisfaction equation. It also binds the
context to the supplied transaction and selected script. -/
theorem prepareDescriptorSatisfaction_spec
    {descriptor : CompiledDescriptor} {leafIndex : Nat}
    {material : DescriptorSatisfactionMaterial} {transaction : Transaction}
    {spentOutputs : Array TxOutput} {inputIndex : Nat}
    {prepared : PreparedDescriptorSatisfaction}
    (preparation : prepareDescriptorSatisfaction descriptor leafIndex material
      transaction spentOutputs inputIndex = .ok prepared) :
    descriptor.taprootLeaves[leafIndex]? = some prepared.leaf ∧
    prepared.sane.checked.fragment = desugar prepared.leaf.fragment ∧
    satisfyFinal prepared.sane.checked.fragment (material.toEnv prepared.context) =
      some prepared.arguments ∧
    TxContext.fromTaproot
      { transaction, spentOutputs, inputIndex
        spendPath := .scriptPath prepared.leaf.script 0xc0 0xffffffff } = .ok prepared.context ∧
    (spentOutputs[inputIndex]!).scriptPubKey = descriptor.scriptPubKey ∧
    (transaction.inputs[inputIndex]!).scriptSig.size = 0 := by
  unfold prepareDescriptorSatisfaction at preparation
  cases selected : descriptor.taprootLeaves[leafIndex]? with
  | none => simp [selected, throw, bind, Except.bind] at preparation
  | some leaf =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at preparation
    cases context : TxContext.fromTaproot
        { transaction, spentOutputs, inputIndex
          spendPath := .scriptPath leaf.script 0xc0 0xffffffff } with
    | error error => simp [context, Except.mapError] at preparation
    | ok ctx =>
      simp only [context, Except.mapError] at preparation
      split at preparation
      · simp at preparation
      · rename_i output
        split at preparation
        · simp at preparation
        · rename_i scriptSig
          cases sane : checkSaneSurface .tapscript leaf.fragment with
          | error error => simp [sane] at preparation
          | ok saneFragment =>
            simp only [sane] at preparation
            cases generated : satisfyFinal saneFragment.checked.fragment (material.toEnv ctx) with
            | none => simp [generated] at preparation
            | some arguments =>
              simp only [generated, Except.ok.injEq] at preparation
              subst prepared
              exact ⟨rfl, checkSane_source sane, generated, context,
                by exact ByteArray.ext (by simpa using output), by simpa using scriptSig⟩

/-- A context created for this leaf is unchanged by the Core executor's
script-path binding, independently of the generated arguments and budget. -/
theorem descriptorSatisfaction_context
    {transaction : Transaction} {spentOutputs : Array TxOutput} {inputIndex : Nat}
    {leaf : TaprootLeafSpendInfo} {context : TxContext}
    (created : TxContext.fromTaproot
      { transaction, spentOutputs, inputIndex
        spendPath := .scriptPath leaf.script 0xc0 0xffffffff } = .ok context)
    (arguments : Witness) :
    context = coreTapscriptContext context
      (coreTaprootRequest arguments leaf.script leaf.controlBlock) := by
  unfold TxContext.fromTaproot at created
  cases valid : validateTaprootContext
      { transaction, spentOutputs, inputIndex
        spendPath := .scriptPath leaf.script 0xc0 0xffffffff } with
  | error error => simp [valid, bind, Except.bind] at created
  | ok result =>
    cases result
    simp only [valid, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at created
    subst context
    rfl

/-- Generated descriptor witnesses satisfy Core verification under the
existing material, encoding and oracle contracts. Successful preparation
supplies leaf membership, source agreement, generation and context agreement.
The inherited satisfaction proofs retain their native_decide dependencies. -/
theorem verify_of_prepareDescriptorSatisfaction
    (flags : CoreVerificationFlags)
    (verifyECDSA verifySchnorr : StackElement → StackElement → ByteArray → Bool)
    {key : PubKey} {tree : DescriptorTree} {descriptor : CompiledDescriptor}
    {leafIndex : Nat} {material : DescriptorSatisfactionMaterial}
    {transaction : Transaction} {spentOutputs : Array TxOutput} {inputIndex : Nat}
    {prepared : PreparedDescriptorSatisfaction} {output : ByteArray}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok descriptor)
    (preparation : prepareDescriptorSatisfaction descriptor leafIndex material
      transaction spentOutputs inputIndex = .ok prepared)
    (selected : descriptor.taprootOutputKey = some output)
    (outputTruth : castToBool output = true)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (sound : (material.toEnv prepared.context).Sound)
    (encodings : (material.toEnv prepared.context).EncodingSound flags.script)
    (modeled : ModeledContextFlags .tapscript flags.script)
    (agreement : (CryptoOracle.pureLeanHashes verifyECDSA verifySchnorr).RefinesModel) :
    prepared.verify (CryptoOracle.pureLeanHashes verifyECDSA verifySchnorr)
      flags descriptor = .ok () := by
  obtain ⟨leaf, source, generated, context, _, _⟩ := prepareDescriptorSatisfaction_spec preparation
  exact verifyCoreScripts_of_compiled_descriptor_satisfaction flags prepared.context
    verifyECDSA verifySchnorr _ prepared.sane compiled
    (List.mem_of_getElem? leaf) source selected outputTruth enabled taproot locktime sequence
    sound encodings modeled generated (descriptorSatisfaction_context context _) agreement

/-- The combined entry returns a witness exactly when preparation and Core
verification succeed with witness and Taproot verification enabled. This
statement uses the supplied executable oracle directly. -/
theorem satisfyDescriptorTransaction_ok_iff
    (oracle : CryptoOracle) (flags : CoreVerificationFlags)
    (descriptor : CompiledDescriptor) (leafIndex : Nat)
    (material : DescriptorSatisfactionMaterial) (transaction : Transaction)
    (spentOutputs : Array TxOutput) (inputIndex : Nat)
    (prepared : PreparedDescriptorSatisfaction) :
    satisfyDescriptorTransaction oracle flags descriptor leafIndex material
      transaction spentOutputs inputIndex = .ok prepared ↔
    flags.witness = true ∧ flags.taproot = true ∧
    prepareDescriptorSatisfaction descriptor leafIndex material transaction spentOutputs inputIndex =
      .ok prepared ∧ prepared.verify oracle flags descriptor = .ok () := by
  unfold satisfyDescriptorTransaction
  cases witness : flags.witness <;> cases taproot : flags.taproot <;>
    simp [throw, bind, Except.bind]
  cases preparation : prepareDescriptorSatisfaction descriptor leafIndex material
      transaction spentOutputs inputIndex with
  | error error => simp
  | ok result =>
    cases verified : result.verify oracle flags descriptor with
    | error error =>
      simp [verified, Except.mapError]
      intro same
      subst prepared
      simp [verified]
    | ok value =>
      cases value
      simp [verified, Except.mapError, pure, Except.pure]
      intro same
      subst prepared
      exact verified

/-- Material soundness and the existing verification contracts suffice for
the combined transaction entry to return the prepared witness. Context and
source agreement are derived from preparation. -/
theorem satisfyDescriptorTransaction_of_preparation
    (flags : CoreVerificationFlags)
    (verifyECDSA verifySchnorr : StackElement → StackElement → ByteArray → Bool)
    {key : PubKey} {tree : DescriptorTree} {descriptor : CompiledDescriptor}
    {leafIndex : Nat} {material : DescriptorSatisfactionMaterial}
    {transaction : Transaction} {spentOutputs : Array TxOutput} {inputIndex : Nat}
    {prepared : PreparedDescriptorSatisfaction} {output : ByteArray}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok descriptor)
    (preparation : prepareDescriptorSatisfaction descriptor leafIndex material
      transaction spentOutputs inputIndex = .ok prepared)
    (selected : descriptor.taprootOutputKey = some output)
    (outputTruth : castToBool output = true)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (sound : (material.toEnv prepared.context).Sound)
    (encodings : (material.toEnv prepared.context).EncodingSound flags.script)
    (modeled : ModeledContextFlags .tapscript flags.script)
    (agreement : (CryptoOracle.pureLeanHashes verifyECDSA verifySchnorr).RefinesModel) :
    satisfyDescriptorTransaction (CryptoOracle.pureLeanHashes verifyECDSA verifySchnorr)
      flags descriptor leafIndex material transaction spentOutputs inputIndex = .ok prepared := by
  apply (satisfyDescriptorTransaction_ok_iff _ _ _ _ _ _ _ _ _).mpr
  exact ⟨enabled, taproot, preparation,
    verify_of_prepareDescriptorSatisfaction flags verifyECDSA verifySchnorr compiled
      preparation selected outputTruth enabled taproot locktime sequence sound encodings
      modeled agreement⟩

end LeanMiniscript.Extraction
