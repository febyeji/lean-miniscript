import LeanMiniscript.Extraction.BitcoinCoreTaprootProofs
import LeanMiniscript.Extraction.MiniscriptCompilation
import LeanMiniscript.Miniscript.CompilePushBoundsProofs

/-!
# Core acceptance of compiled Tapscript

Core's VerifyScript acceptance implies checked-model acceptance of the same
witness under `CompiledScriptBytes`, `CompiledScriptSpend`, and
`CompiledScriptRun` for a sane Tapscript fragment. The inversion follows the
native P2TR output, script-path commitment, and witness execution boundaries.

Witness equality requires separate proofs for each fragment shape.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript CoreScriptExecution

/-- Inversion at the VerifyScript boundary for a native P2TR output: with an
empty scriptSig, a truthy 32-byte program and WITNESS enabled, acceptance
implies acceptance of the witness program. -/
theorem coreVerifyScript_taproot_inversion
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (output : ByteArray) (witness : List ByteArray)
    (size : output.size = 32) (truth : castToBool output = true)
    (enabled : flags.witness = true)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty
      (⟨#[0x51, 0x20]⟩ ++ output) witness = .ok ()) :
    verifyCoreWitnessProgram (executeCoreScript flags ctx oracles) flags witness 1 output
      false keyPath = .ok () := by
  have empty : executeCoreScript flags ctx oracles { scriptBytes := ByteArray.empty } =
      .ok [] := by
    simp [executeCoreScript, executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have noP2SH : coreScriptIsP2SH (⟨#[0x51, 0x20]⟩ ++ output) = false := by
    have width : (⟨#[0x51, 0x20]⟩ ++ output).size = 2 + output.size := by
      change (ByteArray.mk #[0x51, 0x20] ++ output).size = _
      rw [ByteArray.size_append]
      rfl
    simp [coreScriptIsP2SH, width, size]
  have pub := executeCoreScript_taprootOutput flags ctx oracles output size
  simp only [coreVerifyScript, verifyScriptWith, verifyCoreScripts, pushOnly, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub] at accepted
  change (Except.bind
    (if castToBool output then .ok () else .error (CoreVerificationError.script .evalFalse))
    _) = .ok () at accepted
  simp [truth, enabled, decodeCoreWitnessProgram_taproot output size, noP2SH,
    ByteArray.size_empty, Except.bind, pure, Except.pure] at accepted
  revert accepted
  cases verifyCoreWitnessProgram (executeCoreScript flags ctx oracles) flags
      witness 1 output false keyPath with
  | error error => intro accepted; cases accepted
  | ok value => cases value; intro _; rfl

/-- Inversion at the witness-program boundary for the version-1 script path:
acceptance of the full witness is acceptance of the witness-script execution
request, with the same leaf bytes and control block. -/
theorem verifyCoreWitnessProgram_scriptPath_inversion
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (arguments : List ByteArray) (script control output root : ByteArray)
    (keyPath : CoreKeyPathChecker)
    (taproot : flags.taproot = true)
    (committed : verifyTaprootControlBlock output script control =
      .ok { leafVersion := 0xc0, leafHash := tapleafHash script 0xc0, merkleRoot := root })
    (accepted : verifyCoreWitnessProgram execute flags (arguments ++ [script, control])
      1 output false keyPath = .ok ()) :
    executeCoreWitnessScript execute flags (coreTaprootRequest arguments script control) =
      .ok () := by
  obtain ⟨size, noAnnex⟩ := taprootCommitment_not_annex committed
  simpa [verifyCoreWitnessProgram, size, taproot, List.reverse_append, noAnnex,
    committed, coreTaprootRequest, bind, Except.bind, Except.mapError,
    pure, Except.pure] using accepted

/-- Inversion at the witness-script boundary: acceptance of a Tapscript
request whose bytes carry a complete typed encoding implies the initial
stack bounds and a truthy singleton executor result. -/
theorem executeCoreWitnessScript_tapscript_inversion
    (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (request : CoreScriptExecutionRequest) (script : Script)
    (version : request.sigVersion = .tapscript)
    (encoded : CoreTapscriptEncoding request.scriptBytes 0 script)
    (accepted : executeCoreWitnessScript execute flags request = .ok ()) :
    request.stack.length ≤ maxStackSize ∧
      (∀ item ∈ request.stack, item.size ≤ maxScriptElementSize) ∧
      ∃ top, execute request = .ok [top] ∧ castToBool top = true := by
  unfold executeCoreWitnessScript at accepted
  simp only [version, ↓reduceIte, encoded.no_opSuccess, bind, Except.bind,
    Bool.false_eq_true] at accepted
  by_cases count : request.stack.length > maxStackSize
  · simp [count] at accepted
  · simp only [count, ↓reduceIte] at accepted
    by_cases pushes : request.stack.any (fun item => item.size > maxScriptElementSize) = true
    · simp [pushes] at accepted
    · simp only [pushes, Bool.false_eq_true, ↓reduceIte] at accepted
      refine ⟨Nat.le_of_not_gt count, ?_, ?_⟩
      · intro item member
        exact Nat.le_of_not_gt fun big =>
          pushes (List.any_eq_true.mpr ⟨item, member, by simpa using big⟩)
      · cases executed : execute request with
        | error error => simp [executed] at accepted
        | ok stack =>
            simp only [executed] at accepted
            cases stack with
            | nil =>
                change (Except.error (CoreVerificationError.script .cleanStack)) =
                  Except.ok () at accepted
                cases accepted
            | cons top rest =>
                cases rest with
                | nil =>
                    change (if castToBool top then Except.ok ()
                      else Except.error (CoreVerificationError.script .evalFalse)) =
                        Except.ok () at accepted
                    cases truth : castToBool top with
                    | true => exact ⟨top, rfl, truth⟩
                    | false =>
                        simp only [truth] at accepted
                        cases accepted
                | cons next rest =>
                    change (Except.error (CoreVerificationError.script .cleanStack)) =
                      Except.ok () at accepted
                    cases accepted

/-- Core acceptance of a Tapscript spend of a compiled sane Miniscript
fragment implies that the checked model semantics accepts the same witness:
the fragment's compiled script runs the witness to a truthy singleton under
the transaction context Core assigns to the leaf. Every premise is one the
`TapscriptNonMalleability` proof already has; this is the inversion of
`verifyCoreScripts_of_taproot_runtime` for an arbitrary accepted witness. -/
theorem tapscript_bounded_accepts_of_coreVerifyScript
    (sane : SaneFragment .tapscript) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    (∀ item ∈ other, item.size ≤ maxScriptElementSize) ∧
    Accepts .tapscript (compile sane.checked.fragment) other flags.script env.txCtx := by
  obtain ⟨serializedScript, hashes⟩ := serialized
  obtain ⟨output, control, root, spendKey, rest, committed, outputTruth⟩ := spend
  subst spendKey rest
  obtain ⟨enabled, taproot, locktime, sequence, modeled, _sound, _encodings, context,
    agreement⟩ := run
  change (oracles .tapscript bytes).RefinesModel at agreement
  obtain ⟨size, _⟩ := taprootCommitment_not_annex committed
  have small := compile_pushSize_le (fun data => by rw [hashes data]; decide)
    sane.checked.wellFormed
  have encoded : CoreTapscriptEncoding bytes 0 (compile sane.checked.fragment) :=
    CoreTapscriptEncoding.of_serializeScript _ bytes
      (fun element member => by have := small element member; omega) serializedScript
  have program := coreVerifyScript_taproot_inversion flags ctx oracles keyPath output
    (other ++ [bytes, control]) size outputTruth enabled accepted
  have witnessScript := verifyCoreWitnessProgram_scriptPath_inversion
    (executeCoreScript flags ctx oracles) flags other bytes control output root keyPath
    (taproot rfl) committed program
  obtain ⟨_count, sizes, top, executed, truth⟩ :=
    executeCoreWitnessScript_tapscript_inversion (executeCoreScript flags ctx oracles) flags
      (coreTaprootRequest other bytes control) (compile sane.checked.fragment) rfl encoded
      witnessScript
  obtain ⟨alt, evaluated⟩ := executeCoreScript_eval_success flags ctx oracles
    (coreTaprootRequest other bytes control) (compile sane.checked.fragment) rfl
    locktime sequence encoded agreement [top] executed
  have leafContext : env.txCtx =
      coreTapscriptContext ctx (coreTaprootRequest other bytes control) := by
    rw [context]
    rfl
  rw [← leafContext] at evaluated
  constructor
  · simpa [coreTaprootRequest, Witness.toInitialStack] using sizes
  refine ⟨modeled, ?_, top, alt, ?_, truth⟩
  · simp [ModeledContextVersion, context, compiledScriptContext]
  · simpa [Executes, coreTaprootRequest, Witness.toInitialStack] using evaluated

/-- Project checked-model acceptance of the third-party witness. -/
theorem tapscript_accepts_of_coreVerifyScript
    (sane : SaneFragment .tapscript) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    Accepts .tapscript (compile sane.checked.fragment) other flags.script env.txCtx :=
  (tapscript_bounded_accepts_of_coreVerifyScript sane bytes scriptPubKey suffix env flags ctx
    oracles keyPath other serialized spend run accepted).2

end LeanMiniscript.Extraction
