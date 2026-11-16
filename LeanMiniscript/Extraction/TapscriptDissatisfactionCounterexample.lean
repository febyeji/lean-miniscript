import LeanMiniscript.Extraction.MiniscriptCompilation
import LeanMiniscript.Extraction.BitcoinCoreTaprootProofs

/-!
MF-756: `F₀ = 0`, `Fₙ₊₁ = and_b(0, a:Fₙ)` has no satisfaction path, so the
Tapscript sanity check omits its execution-stack bound. Every environment
generates an empty dissatisfaction. At depth 1000 the 4001-byte compiled script
pushes onto 1000 saved alt-stack items and fails with STACK_SIZE.

`incompatible` retains the obligation's cryptographic, commitment and run
premises. It does not construct an environment or a Taproot commitment.
The sanity certificate and runtime failure are unconditional; the full Core
VerifyScript failure assumes only the commitment, truthy output and flags.
-/

namespace LeanMiniscript.Extraction.TapscriptDissatisfactionCounterexample

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script

/-- Each layer saves a false value on the alternate stack. -/
def nested : Nat → CoreFragment
  | 0 => .zero
  | n + 1 => .and_b .zero (.a (nested n))

def mods (n : Nat) : CorrectnessModifiers := { z := n == 0, d := true, u := true }

theorem typed (n : Nat) : HasType .tapscript (nested n) ⟨.B, mods n⟩ := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .and_b .zero (.a_wrap ih)

theorem wf (n : Nat) : (nested n).WellFormed .tapscript := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨trivial, ih, ?_⟩
      simp [CoreFragment.andTimelocksCompatible, CoreFragment.timelocks,
        TimelockUsage.compatibleWith, TimelockUsage.empty]

theorem keys (n : Nat) : (nested n).keys = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nested, CoreFragment.keys, ih]

theorem malleability (n : Nat) :
    HasMalleability .tapscript (nested n) { s := true, e := true, nonMalleable := true } := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .and_b .zero (.a ih)

theorem candidates (n : Nat) (env : SatEnv) :
    satisfactionCandidates (nested n) env = { dsat := .usable [] false } := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nested, satisfactionCandidates, ih]
      rfl

theorem generated (n : Nat) (env : SatEnv) : dissatisfy (nested n) env = some [] := by
  rw [dissatisfy, candidates]
  rfl

/-- Serialized OP_0/TOALTSTACK prefixes and FROMALTSTACK/BOOLAND suffixes. -/
def bytes : Nat → ByteArray
  | 0 => ⟨#[0]⟩
  | n + 1 => ⟨#[0, 0x6b]⟩ ++ bytes n ++ ⟨#[0x6c, 0x9a]⟩

private theorem serialize_append (first second : Script) (a b : ByteArray)
    (left : serializeScript first = .ok a) (right : serializeScript second = .ok b) :
    serializeScript (first ++ second) = .ok (a ++ b) := by
  induction first generalizing a with
  | nil =>
      have empty : a = ByteArray.empty := (Except.ok.inj left).symm
      subst a
      simpa using right
  | cons element rest ih =>
      simp only [serializeScript] at left
      cases head : serializeElement element <;>
        simp only [head, bind, Except.bind] at left
      next => cases left
      next data =>
        cases tail : serializeScript rest <;>
          simp only [tail, pure, Except.pure] at left
        next => cases left
        next restData =>
          cases left
          simp [serializeScript, head, ih _ tail, ByteArray.append_assoc,
            bind, Except.bind, pure, Except.pure]

theorem serialized (n : Nat) (hash : PubKey → Hash160) :
    serializeScript (compileWithKeyHash hash (nested n)) = .ok (bytes n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [nested, compileWithKeyHash, bytes, List.append_assoc,
        List.cons_append, List.nil_append] using
        (serialize_append _ _ _ _
          (serialize_append [.pushNum 0, .op .OP_TOALTSTACK] _
            (ByteArray.mk #[0, 0x6b]) _ (by decide) ih)
          (show serializeScript [.op .OP_FROMALTSTACK, .op .OP_BOOLAND] =
            .ok (ByteArray.mk #[0x6c, 0x9a]) from rfl))

theorem byteSize (n : Nat) : (bytes n).size = 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bytes, ByteArray.size_append, ih]
      change 2 + (4 * n + 1) + 2 = _
      omega

theorem noSatisfactionPath (n : Nat) : (stackPathBounds (nested n)).sat = none := by
  cases n <;> simp [nested, stackPathBounds, StackTraceSet.sequential]

theorem resourceAccepted (n : Nat) (size : 4 * n + 1 ≤ 329482) :
    WithinResourceLimits .tapscript (nested n) := by
  simp only [WithinResourceLimits, resourceLimitsSatisfied, satisfactionOpsWithinLimit,
    dissatisfactionOpsWithinLimit, satisfactionStackWithinLimit,
    maxSatisfactionExecutionStack, noSatisfactionPath, Option.map_none, Bool.and_true]
  change compiledScriptSizeWithinLimit .tapscript (nested n) = true
  unfold compiledScriptSizeWithinLimit resourceSerializedScriptSize compileForResourceAnalysis
    Script.serializedScriptSize
  simp only [serialized, Except.map, byteSize]
  exact decide_eq_true size

/-- The current, unchanged sanity boundary accepts depth 1000. -/
def sane : SaneFragment .tapscript where
  checked := {
    fragment := nested 1000
    ty := ⟨.B, mods 1000⟩
    wellFormed := wf 1000
    hasType := typed 1000
  }
  malleability := { s := true, e := true, nonMalleable := true }
  topLevel := rfl
  hasMalleability := malleability 1000
  noDuplicateKeys := by simp [CoreFragment.NoDuplicateKeys, keys]
  nonMalleable := rfl
  needsSignature := rfl
  withinResourceLimits := resourceAccepted 1000 (by decide)

theorem validDissatisfiable : ValidDissatisfiableMiniscript .tapscript (nested 1000) :=
  ⟨mods 1000, ⟨wf 1000, typed 1000⟩, rfl⟩

/-- The next OP_0 exceeds the combined stack limit, for any signature budget. -/
theorem runtimeOverflow (n : Nat) (oracle : CryptoOracle) (flags : ScriptFlags)
    (ctx : TxContext) (version : ctx.sigVersion = .tapscript) (weight : Nat)
    (alt : Stack) (rest : Script) (full : n + alt.length = 1000) :
    evaluateRuntime oracle (compile (nested n) ++ rest)
      { stack := [], altStack := alt, weight := weight } flags ctx =
      .failure .stackSize := by
  induction n generalizing alt rest with
  | zero =>
      have length : alt.length = 1000 := by omega
      simp [compile, nested, compileWithKeyHash, evaluateRuntime,
        runtimeStep_pushNumber, runtimeInstruction, executeRuntimeElement,
        ScriptElement.pushSize, prepareValidationWeight, evaluate.eq_1,
        evaluate.eq_3, checkRuntimeStack, length, maxStackSize,
        scriptNum_zero, falseElement, ByteArray.size, maxScriptElementSize,
        bind, Except.bind, pure, Except.pure]
  | succ n ih =>
      have length : 1 + alt.length ≤ maxStackSize := by unfold maxStackSize; omega
      simp only [compile, nested, compileWithKeyHash, List.append_assoc,
        List.cons_append, List.nil_append]
      simp [evaluateRuntime, runtimeStep_tapscript _ _ _ _ version,
        runtimeInstruction, executeRuntimeElement, ScriptElement.pushSize,
        prepareValidationWeight, evaluate, checkRuntimeStack,
        scriptNum_zero, falseElement, ByteArray.size, maxScriptElementSize,
        Nat.not_lt.mpr length,
        Nat.add_comm alt.length 1, bind, Except.bind, pure, Except.pure]
      exact ih _ _ (by simp only [List.length_cons]; omega)

/-- Below the overflow edge, execution leaves a false singleton and preserves
    the entire signature budget. The continuation can inspect that result. -/
theorem runtimeWithinLimit (n : Nat) (oracle : CryptoOracle) (flags : ScriptFlags)
    (ctx : TxContext) (version : ctx.sigVersion = .tapscript) (weight : Nat)
    (alt : Stack) (rest : Script) (bound : n + alt.length < 1000) :
    evaluateRuntime oracle (compile (nested n) ++ rest)
      { stack := [], altStack := alt, weight := weight } flags ctx =
    evaluateRuntime oracle rest
      { stack := [falseElement], altStack := alt, weight := weight } flags ctx := by
  induction n generalizing alt rest with
  | zero =>
      have length : 1 + alt.length ≤ maxStackSize := by unfold maxStackSize; omega
      simp [compile, nested, compileWithKeyHash, evaluateRuntime,
        runtimeStep_pushNumber, runtimeInstruction, executeRuntimeElement,
        ScriptElement.pushSize, prepareValidationWeight, evaluate.eq_1,
        evaluate.eq_3, checkRuntimeStack, Nat.not_lt.mpr length,
        scriptNum_zero, falseElement, ByteArray.size, maxScriptElementSize,
        bind, Except.bind, pure, Except.pure]
  | succ n ih =>
      have length : 1 + alt.length ≤ maxStackSize := by unfold maxStackSize; omega
      have lengthTwo : 2 + alt.length ≤ maxStackSize := by unfold maxStackSize; omega
      simp only [compile, nested, compileWithKeyHash, List.append_assoc,
        List.cons_append, List.nil_append]
      simp [evaluateRuntime, runtimeStep_tapscript _ _ _ _ version,
        runtimeInstruction, executeRuntimeElement, ScriptElement.pushSize,
        prepareValidationWeight, evaluate, checkRuntimeStack,
        scriptNum_zero, falseElement, ByteArray.size, maxScriptElementSize,
        Nat.not_lt.mpr length, Nat.add_comm alt.length 1,
        bind, Except.bind, pure, Except.pure]
      rw [show evaluateRuntime oracle (compileWithKeyHash modelKeyHash (nested n) ++
          .op .OP_FROMALTSTACK :: .op .OP_BOOLAND :: rest)
          { stack := [], altStack := ByteArray.mk #[] :: alt, weight := weight } flags ctx = _
          from ih _ _ (by simp only [List.length_cons]; omega)]
      simp [evaluateRuntime, runtimeStep_tapscript _ _ _ _ version,
        runtimeInstruction, executeRuntimeElement, ScriptElement.pushSize,
        prepareValidationWeight, evaluate, checkRuntimeStack,
        falseElement, ByteArray.size, maxScriptElementSize,
        Nat.not_lt.mpr length, Nat.not_lt.mpr lengthTwo,
        bind, Except.bind, pure, Except.pure, boolToElement,
        decodeBinaryScriptNums, decodeScriptNum, scriptNumIsMinimal,
        scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]

/-- The adjacent depth reaches exactly the 1000-item combined stack limit,
    returns false, and spends no validation weight. -/
theorem runtimeEdge (oracle : CryptoOracle) (flags : ScriptFlags)
    (ctx : TxContext) (version : ctx.sigVersion = .tapscript) (weight : Nat) :
    evaluateWithRuntimeLimits oracle (compile (nested 999)) [] [] flags ctx weight =
      .success [falseElement] [] weight := by
  have completed := runtimeWithinLimit 999 oracle flags ctx version weight [] [] (by decide)
  simpa only [List.append_nil, evaluateWithRuntimeLimits, evaluateRuntime, finishRuntime,
    List.isEmpty_nil, ↓reduceIte] using completed

theorem pushes (n : Nat) : ∀ element ∈ compile (nested n), element.pushSize ≤ 75 := by
  have zeroPush : (ScriptElement.pushNum 0).pushSize ≤ 75 := by decide
  induction n with
  | zero => simpa [compile, nested, compileWithKeyHash] using zeroPush
  | succ n ih =>
      intro element member
      have selected : element = .pushNum 0 ∨ element = .op .OP_TOALTSTACK ∨
          element ∈ compile (nested n) ∨ element = .op .OP_FROMALTSTACK ∨
          element = .op .OP_BOOLAND := by
        simpa [compile, nested, compileWithKeyHash] using member
      rcases selected with rfl | rfl | member | rfl | rfl
      · exact zeroPush
      · decide
      · exact ih element member
      · decide
      · decide

theorem encoded (n : Nat) : CoreTapscriptEncoding (bytes n) 0 (compile (nested n)) :=
  CoreTapscriptEncoding.of_serializeScript _ _
    (fun element member => by have := pushes n element member; omega)
    (serialized n modelKeyHash)

/-- The typed runtime failure transfers to Core's raw byte executor. -/
theorem rawStackSize (n : Nat) (full : n = 1000) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (control : ByteArray) :
    executeCoreScript flags ctx oracles (coreTaprootRequest [] (bytes n) control) =
      .error (.script .stackSize) := by
  rw [executeCoreScript_eq_runtime flags ctx oracles _ _ rfl (encoded n)]
  have failed := runtimeOverflow n (oracles .tapscript (bytes n)) flags.script
    (coreTapscriptContext ctx (coreTaprootRequest [] (bytes n) control)) rfl
    (coreTaprootRequest [] (bytes n) control).validationWeight [] [] (by simpa using full)
  have runtime : evaluateWithRuntimeLimits (oracles .tapscript (bytes n))
      (compile (nested n)) [] [] flags.script
      (coreTapscriptContext ctx (coreTaprootRequest [] (bytes n) control))
      (coreTaprootRequest [] (bytes n) control).validationWeight =
        .failure .stackSize := by simpa only [evaluateWithRuntimeLimits, List.append_nil] using failed
  simp only [coreTaprootRequest, List.reverse_nil] at runtime ⊢
  rw [runtime]
  rfl

/-- A committed leaf propagates STACK_SIZE through the full VerifyScript entry. -/
theorem coreStackSize (n : Nat) (full : n = 1000) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (output control root : ByteArray)
    (enabled : flags.witness = true) (taproot : flags.taproot = true)
    (committed : LeanMiniscript.Bitcoin.verifyTaprootControlBlock output (bytes n) control =
      .ok { leafVersion := 0xc0,
            leafHash := LeanMiniscript.Bitcoin.tapleafHash (bytes n) 0xc0,
            merkleRoot := root })
    (truth : castToBool output = true) :
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty
      (ByteArray.mk #[0x51, 0x20] ++ output) [bytes n, control] =
      .error (.script .stackSize) := by
  obtain ⟨size, noAnnex⟩ := taprootCommitment_not_annex committed
  have witnessFailure : executeCoreWitnessScript (executeCoreScript flags ctx oracles)
      flags (coreTaprootRequest [] (bytes n) control) = .error (.script .stackSize) := by
    rw [executeCoreWitnessScript]
    simp only [coreTaprootRequest, (encoded n).no_opSuccess, List.reverse_nil,
      List.length_nil, List.any_nil, maxStackSize]
    have raw := rawStackSize n full flags ctx oracles control
    simp only [coreTaprootRequest, List.reverse_nil, List.nil_append] at raw
    simp [raw, bind, Except.bind]
  have programFailure : verifyCoreWitnessProgram (executeCoreScript flags ctx oracles)
      flags [bytes n, control] 1 output false keyPath = .error (.script .stackSize) := by
    simpa [verifyCoreWitnessProgram, size, taproot, noAnnex,
      committed, coreTaprootRequest, bind, Except.bind, Except.mapError,
      pure, Except.pure] using witnessFailure
  have empty : executeCoreScript flags ctx oracles { scriptBytes := ByteArray.empty } =
      .ok [] := by simp [executeCoreScript, CoreScriptExecution.executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have pub := executeCoreScript_taprootOutput flags ctx oracles output size
  simp only [coreVerifyScript, verifyScriptWith, verifyCoreScripts, pushOnly, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool output then .ok () else .error (CoreVerificationError.script .evalFalse))
    _) = .error (.script .stackSize)
  simp [truth, enabled, decodeCoreWitnessProgram_taproot output size,
    programFailure, ByteArray.size_empty, Except.bind]

/-- Under the original byte/spend/run premises, the claimed EVAL_FALSE result
    contradicts Core's STACK_SIZE result for this sane fragment. -/
theorem incompatible (environment : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (scriptPubKey : ByteArray) (suffix : List ByteArray)
    (hashes : ∀ data, (LeanMiniscript.Script.hash160 data).size = 20)
    (spend : CompiledScriptSpend .tapscript (bytes 1000) scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript environment flags ctx oracles (bytes 1000)) :
    ¬ TapscriptDissatisfaction := by
  intro claimed
  have predicted := claimed sane (bytes 1000) scriptPubKey suffix environment flags ctx
    oracles keyPath [] ⟨serialized 1000 modelKeyHash, hashes⟩ spend run
    validDissatisfiable (generated 1000 environment)
  obtain ⟨output, control, root, rfl, rfl, committed, truth⟩ := spend
  change coreVerifyScript flags ctx oracles keyPath ByteArray.empty
    (ByteArray.mk #[0x51, 0x20] ++ output) [bytes 1000, control] = _ at predicted
  rw [coreStackSize 1000 rfl flags ctx oracles keyPath output control root run.1
    (run.2.1 rfl) committed truth] at predicted
  cases predicted

end LeanMiniscript.Extraction.TapscriptDissatisfactionCounterexample
