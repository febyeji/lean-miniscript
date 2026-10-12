import LeanMiniscript.Extraction.BitcoinCoreExecutionProofs
import LeanMiniscript.Extraction.BitcoinCoreWitness

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin CoreWitnessScan

private theorem encoded_not_opSuccess
    {instruction : CoreRawInstruction} {element : ScriptElement}
    (encoded : instruction.Encodes element) :
    isCoreOpSuccess instruction.opcode.toNat = false := by
  rcases encoded.opcodeCases with push | number | range | ⟨opcode, byte⟩
  · simp only [isCoreOpSuccess, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · simp [isCoreOpSuccess, number]
  · simp only [isCoreOpSuccess, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rw [byte]; cases opcode <;> decide

private theorem scanCoreOpSuccess_encoded {bytes : ByteArray} {offset fuel : Nat}
    {script : Script} (encoded : CoreTapscriptEncoding bytes offset script)
    (enough : script.length < fuel) :
    scanCoreOpSuccess bytes fuel offset = .ok false := by
  induction script generalizing offset fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => simp [scanCoreOpSuccess, show offset = bytes.size from encoded, pure, Except.pure]
  | cons element rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [CoreTapscriptEncoding] at encoded
          cases decoded : readCoreRawInstruction bytes offset with
          | error error => simp [decoded] at encoded
          | ok instruction =>
              simp only [decoded] at encoded
              simp [scanCoreOpSuccess, Nat.not_le.mpr encoded.1, decoded,
                encoded_not_opSuccess encoded.2.2.1,
                ih encoded.2.2.2 (by simpa using enough), Except.mapError,
                bind, Except.bind]

/-- A complete typed encoding passes the full raw OP_SUCCESS scan, including
skipped branches and pushed bytes that happen to equal success opcodes. -/
theorem CoreTapscriptEncoding.no_opSuccess {bytes : ByteArray} {script : Script}
    (encoded : CoreTapscriptEncoding bytes 0 script) :
    coreTapscriptHasOpSuccess bytes = .ok false :=
  scanCoreOpSuccess_encoded encoded (by have := encoded.length_bound; omega)

/-- The script-path request for a leaf with wire-order arguments and no annex. -/
def coreTaprootRequest (arguments : List ByteArray) (script control : ByteArray) :
    CoreScriptExecutionRequest :=
  { scriptBytes := script
    stack := arguments.reverse
    sigVersion := .tapscript
    validationWeight := (serializeWitness (arguments ++ [script, control])).size + 50
    tapleafHash := some (tapleafHash script 0xc0) }

/-- Initial argument bounds, typed execution, and a truthy singleton suffice
for the Core witness-script boundary. Commitment is checked by its caller. -/
theorem executeCoreWitnessScript_of_runtime
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script)
    (count : request.stack.length ≤ maxStackSize)
    (sizes : ∀ item ∈ request.stack, item.size ≤ maxScriptElementSize)
    {top : StackElement} {alt : Stack} {weight : Nat}
    (executed : evaluateWithRuntimeLimits (oracles .tapscript request.scriptBytes)
      script request.stack [] flags.script (coreTapscriptContext ctx request)
      request.validationWeight = .success [top] alt weight)
    (truth : castToBool top = true) :
    executeCoreWitnessScript (executeCoreScript flags ctx oracles) flags request = .ok () := by
  have elements : request.stack.any (fun item => item.size > maxScriptElementSize) = false := by
    simp only [List.any_eq_false]; intro item member
    simpa using Nat.not_lt.mpr (sizes item member)
  have raw := executeCoreScript_eq_runtime flags ctx oracles request script
    version locktime sequence encoded
  rw [executed] at raw
  simp only [coreRuntimeResult] at raw
  simp [executeCoreWitnessScript, version, encoded.no_opSuccess,
    Nat.not_lt.mpr count, elements, raw, bind, Except.bind]
  change (if castToBool top then Except.ok () else .error (CoreVerificationError.script .evalFalse)) = .ok ()
  simp [truth]

private theorem commitment_shape {output script control : ByteArray}
    {commitment : TaprootCommitment}
    (verified : verifyTaprootControlBlock output script control = .ok commitment) :
    output.size = 32 ∧ control[0]! &&& 0xfe = commitment.leafVersion := by
  unfold verifyTaprootControlBlock at verified
  cases parsed : parseTaprootControlBlock control with
  | error error => simp [parsed, bind, Except.bind] at verified
  | ok parsedControl =>
      simp only [parsed, bind, Except.bind] at verified
      split at verified
      · cases verified
      · rename_i size
        simp only [parseTaprootControlBlock] at parsed
        split at parsed
        · cases parsed
        · cases parsed
          split at verified
          · cases verified
          · split at verified
            · cases verified
            · simp only [pure, Except.pure, Except.ok.injEq] at verified
              subst commitment
              exact ⟨by omega, rfl⟩

/-- A committed version-0xc0 control block cannot be removed as an annex. -/
theorem taprootCommitment_not_annex {output script control root : ByteArray}
    (verified : verifyTaprootControlBlock output script control =
      .ok { leafVersion := 0xc0, leafHash := tapleafHash script 0xc0, merkleRoot := root }) :
    output.size = 32 ∧ (control[0]! == 0x50) = false := by
  obtain ⟨size, version⟩ := commitment_shape verified
  refine ⟨size, ?_⟩
  apply beq_eq_false_iff_ne.mpr
  intro annex
  rw [annex] at version
  exact (by decide : (0x50 : UInt8) &&& 0xfe ≠ 0xc0) version

/-- A committed leaf and accepted witness-script execution pass native
Taproot dispatch. The control block also certifies the output-key size and
that the last witness item is not an annex. -/
theorem verifyCoreWitnessProgram_scriptPath
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (arguments : List ByteArray) (script control output root : ByteArray)
    (keyPath : CoreKeyPathChecker)
    (taproot : flags.taproot = true)
    (committed : verifyTaprootControlBlock output script control =
      .ok { leafVersion := 0xc0, leafHash := tapleafHash script 0xc0, merkleRoot := root })
    (accepted : executeCoreWitnessScript execute flags
      (coreTaprootRequest arguments script control) = .ok ()) :
    verifyCoreWitnessProgram execute flags (arguments ++ [script, control])
      1 output false keyPath = .ok () := by
  obtain ⟨size, noAnnex⟩ := taprootCommitment_not_annex committed
  simpa [verifyCoreWitnessProgram, size, taproot, List.reverse_append, noAnnex,
    committed, coreTaprootRequest, bind, Except.bind, Except.mapError,
    pure, Except.pure] using accepted

end LeanMiniscript.Extraction
