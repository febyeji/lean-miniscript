import LeanMiniscript.Extraction.BitcoinCoreTaprootProofs
import LeanMiniscript.Miniscript.OutputDescriptorProofs
import LeanMiniscript.Miniscript.SatisfactionCorrectnessProofs
import LeanMiniscript.Properties.SaneExecutionResourceProofs

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-!
Generated no-annex satisfactions for compiled Taproot descriptors reach Core's
complete script-pair verifier. The sane-fragment theorem derives runtime
completion from the stack summary, source push bounds and a static signature
budget. Byte/context agreement, oracle refinement, a truthy output key and
initial argument sizes remain explicit. Satisfaction correctness supplies the
final singleton and truth value; descriptor correctness supplies the commitment.
The generated-satisfaction step inherits the existing satisfaction proofs'
`native_decide` dependencies.
-/

/-- Generated satisfaction correctness determines the final main stack of any
completed resource-limited run under an oracle that refines the model. -/
theorem satisfyFinal_runtime_cleanStack
    {fragment : CoreFragment} {env : SatEnv} {arguments : Witness}
    {flags : ScriptFlags} {oracle : CryptoOracle}
    {initialWeight finalWeight : Nat} {stack alt : Stack}
    (valid : ValidMiniscript .tapscript fragment)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (generated : satisfyFinal fragment env = some arguments)
    (agreement : oracle.RefinesModel)
    (executed : evaluateWithRuntimeLimits oracle (compile fragment)
      arguments.toInitialStack [] flags env.txCtx initialWeight =
        .success stack alt finalWeight) :
    ∃ top, stack = [top] ∧ castToBool top = true := by
  obtain ⟨_, _, top, finalAlt, satisfied, truth⟩ :=
    satisfyFinalCorrectnessCore valid sound encodings version modeled generated
  have observed := evaluateWithRuntimeLimits_eval_success agreement executed
  have same := (evaluate_model_iff.mp observed).symm.trans
    (evaluate_model_iff.mp satisfied)
  exact ⟨top, (ExecResult.success.inj same).1, truth⟩

/-- A selected descriptor leaf with a generated satisfaction passes native
Taproot VerifyScript, conditional on byte/context agreement, oracle refinement,
a truthy output key, initial witness limits, and resource-limited execution
completing. Descriptor correctness supplies the control commitment and
satisfaction correctness supplies the final true singleton. The witness has
no annex. -/
theorem verifyCoreScripts_of_descriptor_satisfaction
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker)
    {key : PubKey} {tree : DescriptorTree} {descriptor : CompiledDescriptor}
    {leaf : TaprootLeafSpendInfo} {output : ByteArray}
    {fragment : CoreFragment} {env : SatEnv} {arguments : Witness}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok descriptor)
    (member : leaf ∈ descriptor.taprootLeaves)
    (selected : descriptor.taprootOutputKey = some output)
    (outputTruth : castToBool output = true)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (valid : ValidMiniscript .tapscript fragment)
    (sound : env.Sound) (encodings : env.EncodingSound flags.script)
    (modeled : ModeledContextFlags .tapscript flags.script)
    (generated : satisfyFinal fragment env = some arguments)
    (encoded : CoreTapscriptEncoding leaf.script 0 (compile fragment))
    (context : env.txCtx = coreTapscriptContext ctx
      (coreTaprootRequest arguments leaf.script leaf.controlBlock))
    (agreement : (oracles .tapscript leaf.script).RefinesModel)
    (count : arguments.length ≤ maxStackSize)
    (sizes : arguments.ItemsBounded)
    {stack alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits (oracles .tapscript leaf.script)
      (compile fragment) arguments.toInitialStack [] flags.script env.txCtx
      (coreTaprootRequest arguments leaf.script leaf.controlBlock).validationWeight =
        .success stack alt weight) :
    verifyCoreScripts (executeCoreScript flags ctx oracles)
      (fun witness version program isP2SH => verifyCoreWitnessProgram
        (executeCoreScript flags ctx oracles) flags witness version program isP2SH keyPath)
      flags ByteArray.empty descriptor.scriptPubKey
      (arguments ++ [leaf.script, leaf.controlBlock]) = .ok () := by
  have version : ModeledContextVersion .tapscript env.txCtx := by
    simp [ModeledContextVersion, context, coreTapscriptContext]
  obtain ⟨top, stackEq, truth⟩ := satisfyFinal_runtime_cleanStack valid sound encodings
    version modeled generated agreement executed
  obtain ⟨compiledOutput, root, outputEq, _, commitments⟩ :=
    compileOutputDescriptor_taprootCommitments compiled
  have outputSame : compiledOutput = output := Option.some.inj (outputEq.symm.trans selected)
  subst compiledOutput
  rw [(compileOutputDescriptor_taprootScriptPubKey compiled selected).1]
  apply verifyCoreScripts_of_taproot_runtime flags ctx oracles keyPath arguments
    leaf.script leaf.controlBlock output root (compile fragment) enabled taproot
    locktime sequence (commitments leaf member) outputTruth encoded count sizes
    (top := top) (alt := alt) (weight := weight)
  · simpa only [← context, stackEq, Witness.toInitialStack] using executed
  · exact truth

/-- A sane descriptor satisfaction passes the complete Core verifier under
static resource conditions. Runtime completion and initial witness count are
derived. The budget counts all source signature opcodes, including skipped
branches, so it is sufficient but may exceed the actual debit. -/
theorem verifyCoreScripts_of_sane_descriptor_satisfaction
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (sane : SaneFragment .tapscript)
    {key : PubKey} {tree : DescriptorTree} {descriptor : CompiledDescriptor}
    {leaf : TaprootLeafSpendInfo} {output : ByteArray}
    {env : SatEnv} {arguments : Witness}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok descriptor)
    (member : leaf ∈ descriptor.taprootLeaves)
    (selected : descriptor.taprootOutputKey = some output)
    (outputTruth : castToBool output = true)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (sound : env.Sound) (encodings : env.EncodingSound flags.script)
    (modeled : ModeledContextFlags .tapscript flags.script)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (encoded : CoreTapscriptEncoding leaf.script 0 sane.compile)
    (context : env.txCtx = coreTapscriptContext ctx
      (coreTaprootRequest arguments leaf.script leaf.controlBlock))
    (agreement : (oracles .tapscript leaf.script).RefinesModel)
    (sizes : arguments.ItemsBounded)
    (pushes : ∀ element ∈ sane.compile, element.pushSize ≤ maxScriptElementSize)
    (budget : staticValidationWeight sane.compile ≤
      (coreTaprootRequest arguments leaf.script leaf.controlBlock).validationWeight) :
    verifyCoreScripts (executeCoreScript flags ctx oracles)
      (fun witness version program isP2SH => verifyCoreWitnessProgram
        (executeCoreScript flags ctx oracles) flags witness version program isP2SH keyPath)
      flags ByteArray.empty descriptor.scriptPubKey
      (arguments ++ [leaf.script, leaf.controlBlock]) = .ok () := by
  have version : ModeledContextVersion .tapscript env.txCtx := by
    simp [ModeledContextVersion, context, coreTapscriptContext]
  obtain ⟨top, remaining, completed, _, count, _⟩ :=
    sane.tapscript_satisfyFinal_runtime_complete sound encodings version modeled generated
      agreement pushes _ budget
  exact verifyCoreScripts_of_descriptor_satisfaction flags ctx oracles keyPath compiled
    member selected outputTruth enabled taproot locktime sequence sane.validMiniscript
    sound encodings modeled generated encoded context agreement count sizes completed

end LeanMiniscript.Extraction
