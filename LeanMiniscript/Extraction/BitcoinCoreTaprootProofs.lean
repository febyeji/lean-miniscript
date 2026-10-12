import LeanMiniscript.Extraction.BitcoinCoreWitnessProofs
import LeanMiniscript.Extraction.BitcoinCoreVerification

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin CoreScriptExecution

private def nativeOutput (output : ByteArray) : ByteArray := ⟨#[0x51, 0x20]⟩ ++ output

private theorem nativeOutput_size (output : ByteArray) :
    (nativeOutput output).size = 2 + output.size := by
  change (ByteArray.mk #[0x51, 0x20] ++ output).size = _
  rw [ByteArray.size_append]
  rfl

private theorem nativeOutput_first (output : ByteArray) :
    (nativeOutput output)[0]! = 0x51 ∧ (nativeOutput output)[1]! = 0x20 := by
  have zero : 0 < (nativeOutput output).size := by rw [nativeOutput_size]; omega
  have one : 1 < (nativeOutput output).size := by rw [nativeOutput_size]; omega
  constructor
  · rw [getElem!_pos (nativeOutput output) 0 zero]
    change (ByteArray.mk #[0x51, 0x20] ++ output)[0] = _
    rw [ByteArray.getElem_append_left (by decide)]
    rfl
  · rw [getElem!_pos (nativeOutput output) 1 one]
    change (ByteArray.mk #[0x51, 0x20] ++ output)[1] = _
    rw [ByteArray.getElem_append_left (by decide)]
    rfl

private theorem nativeOutput_payload (output : ByteArray) :
    (nativeOutput output).extract 2 (2 + output.size) = output := by
  exact ByteArray.extract_append_eq_right rfl rfl

/-- Core recognizes the native P2TR output produced by the descriptor compiler. -/
theorem decodeCoreWitnessProgram_taproot (output : ByteArray) (size : output.size = 32) :
    decodeCoreWitnessProgram? (⟨#[0x51, 0x20]⟩ ++ output) = some (1, output) := by
  change decodeCoreWitnessProgram? (nativeOutput output) = _
  have payload : (nativeOutput output).extract 2 34 = output := by
    simpa [size] using nativeOutput_payload output
  simp only [decodeCoreWitnessProgram?, (nativeOutput_first output).1,
    (nativeOutput_first output).2, nativeOutput_size, size]
  simp [payload]

/-- The native Taproot output executes as two BASE pushes before witness dispatch. -/
theorem executeCoreScript_taprootOutput (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (output : ByteArray) (size : output.size = 32) :
    executeCoreScript flags ctx oracles { scriptBytes := ⟨#[0x51, 0x20]⟩ ++ output } =
      .ok [output, trueElement] := by
  have payload : (nativeOutput output).extract 2 34 = output := by
    simpa [size] using nativeOutput_payload output
  have first : readCoreRawInstruction (nativeOutput output) 0 =
      .ok ⟨0x51, ByteArray.empty, 1⟩ := by
    simp only [readCoreRawInstruction, (nativeOutput_first output).1, nativeOutput_size, size]
    rfl
  have second : readCoreRawInstruction (nativeOutput output) 1 =
      .ok ⟨0x20, output, 34⟩ := by
    simp only [readCoreRawInstruction, (nativeOutput_first output).2, nativeOutput_size, size]
    simp [payload, pure, Except.pure]
  change executeCoreScript flags ctx oracles { scriptBytes := nativeOutput output } = _
  simp +decide [executeCoreScript, nativeOutput_size, size, executeCoreRawLoop,
    first, second, coreRawStep, coreLegacyDisabledOpcode, coreLegacyMinimalPush,
    runtimeStep, executeRuntimeElement, ScriptElement.pushSize, prepareValidationWeight,
    evaluate.eq_1, evaluate.eq_2, evaluate.eq_3, checkRuntimeStack,
    maxScriptElementSize, maxStackSize, scriptNum, trueElement,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- For a truthy output key, native P2TR verification reduces to its witness
verifier. Empty scriptSig execution, P2SH exclusion, and cleanstack are proved. -/
theorem verifyCoreScripts_taproot
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (verifyWitness : CoreWitnessVerifier) (output : ByteArray) (witness : List ByteArray)
    (size : output.size = 32) (truth : castToBool output = true)
    (enabled : flags.witness = true)
    (accepted : verifyWitness witness 1 output false = .ok ()) :
    verifyCoreScripts (executeCoreScript flags ctx oracles) verifyWitness flags
      ByteArray.empty (⟨#[0x51, 0x20]⟩ ++ output) witness = .ok () := by
  have empty : executeCoreScript flags ctx oracles { scriptBytes := ByteArray.empty } =
      .ok [] := by
    simp [executeCoreScript, executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have noP2SH : coreScriptIsP2SH (⟨#[0x51, 0x20]⟩ ++ output) = false := by
    change coreScriptIsP2SH (nativeOutput output) = false
    simp [coreScriptIsP2SH, nativeOutput_size, size]
  have pub := executeCoreScript_taprootOutput flags ctx oracles output size
  simp only [verifyCoreScripts, pushOnly, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool output then .ok () else .error (CoreVerificationError.script .evalFalse))
    _) = .ok ()
  simp [truth, enabled, decodeCoreWitnessProgram_taproot output size, noP2SH, accepted,
    ByteArray.size_empty, Except.bind, pure, Except.pure]

/-- No-annex script-path acceptance reaches the complete Core VerifyScript
entry point with the actual raw executor and commitment verifier. -/
theorem verifyCoreScripts_of_taproot_runtime
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : List ByteArray)
    (bytes control output root : ByteArray) (script : Script)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (committed : verifyTaprootControlBlock output bytes control =
      .ok { leafVersion := 0xc0, leafHash := tapleafHash bytes 0xc0, merkleRoot := root })
    (outputTruth : castToBool output = true)
    (encoded : CoreTapscriptEncoding bytes 0 script)
    (count : arguments.length ≤ maxStackSize)
    (sizes : ∀ item ∈ arguments, item.size ≤ maxScriptElementSize)
    {top : StackElement} {alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits (oracles .tapscript bytes)
      script arguments.reverse [] flags.script
      (coreTapscriptContext ctx (coreTaprootRequest arguments bytes control))
      (coreTaprootRequest arguments bytes control).validationWeight =
        .success [top] alt weight)
    (truth : castToBool top = true) :
    verifyCoreScripts (executeCoreScript flags ctx oracles)
      (fun witness version program isP2SH => verifyCoreWitnessProgram
        (executeCoreScript flags ctx oracles) flags witness version program isP2SH keyPath)
      flags ByteArray.empty (⟨#[0x51, 0x20]⟩ ++ output)
      (arguments ++ [bytes, control]) = .ok () := by
  apply verifyCoreScripts_taproot flags ctx oracles _ output _
    (taprootCommitment_not_annex committed).1 outputTruth enabled
  apply verifyCoreWitnessProgram_scriptPath _ flags arguments bytes control output root
    keyPath taproot committed
  exact executeCoreWitnessScript_of_runtime flags ctx oracles
    (coreTaprootRequest arguments bytes control) script rfl locktime sequence encoded
    (by simpa [coreTaprootRequest] using count)
    (by simpa [coreTaprootRequest] using sizes) executed truth

end LeanMiniscript.Extraction
