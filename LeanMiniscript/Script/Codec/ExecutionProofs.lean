import LeanMiniscript.Script.Codec.NormalizationProofs
import LeanMiniscript.Script.ValidationWeight

namespace LeanMiniscript.Script

/-!
Canonical codec round trips preserve complete execution results for every
cryptographic oracle, including errors, alternate stacks and remaining weight.
-/

private theorem evaluate_normalizeSerializedElement_cons
    (oracle : CryptoOracle) (element : ScriptElement) (rest : Script)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (normalizeSerializedElement element :: rest) stack alt flags ctx =
      evaluate oracle (element :: rest) stack alt flags ctx := by
  apply normalizeSerializedElement_preserves
    (fun element => evaluate oracle (element :: rest) stack alt flags ctx)
  intro value
  rw [evaluate.eq_2, evaluate.eq_3]

/-- Normalization preserves success and failure, with no balance, resource,
    serialization-success or oracle-refinement premise. -/
theorem evaluate_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (stack alt : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (normalizeSerializedScript script) stack alt flags ctx =
      evaluate oracle script stack alt flags ctx := by
  cases script with
  | nil => rfl
  | cons element rest =>
      change evaluate oracle
        (normalizeSerializedElement element :: normalizeSerializedScript rest)
        stack alt flags ctx = _
      rw [evaluate_normalizeSerializedElement_cons]
      have tail (nextStack nextAlt : Stack) :=
        evaluate_normalizeSerializedScript oracle rest nextStack nextAlt flags ctx
      have unclosed (selected : Bool) (nextStack nextAlt : Stack) :=
        evaluate_normalizeSerializedScript oracle
          (selectUnclosedConditional rest selected) nextStack nextAlt flags ctx
      have closed (frame : ConditionalFrame) (split : splitConditional rest = some frame)
          (selected : Bool) (nextStack nextAlt : Stack) :=
        evaluate_normalizeSerializedScript oracle
          (frame.select selected) nextStack nextAlt flags ctx
      rw [evaluate.eq_def oracle (element :: normalizeSerializedScript rest),
        evaluate.eq_def oracle (element :: rest)]
      cases element with
      | pushData | pushNum => exact tail _ _
      | op opcode =>
          cases opcode <;> simp only [tail]
          all_goals
            cases stack with
            | nil => rfl
            | cons top remaining =>
                simp only [selectUnclosedConditional_normalizeSerializedScript]
                split
                · cases splitEq : splitConditional rest with
                  | none =>
                      rw [splitConditional_normalizeSerializedScript, splitEq]
                      simp only [Option.map_none, unclosed]
                  | some frame =>
                      rw [splitConditional_normalizeSerializedScript, splitEq]
                      simp only [Option.map_some, ConditionalFrame.select_map]
                      exact closed frame splitEq _ _ _
                · rfl
termination_by script.length
decreasing_by
  all_goals simp_wf
  · exact Nat.lt_succ_of_le (selectUnclosedConditional_length_le rest selected)
  · have smaller := ConditionalFrame.select_length_lt split selected
    omega

theorem pushSize_normalizeSerializedElement (element : ScriptElement) :
    (normalizeSerializedElement element).pushSize = element.pushSize := by
  apply normalizeSerializedElement_preserves
  intro value
  rfl

theorem executeRuntimeElement_normalizeSerializedElement
    (oracle : CryptoOracle) (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    executeRuntimeElement oracle (normalizeSerializedElement element) state flags ctx =
      executeRuntimeElement oracle element state flags ctx := by
  apply normalizeSerializedElement_preserves
    (fun element => executeRuntimeElement oracle element state flags ctx)
  intro value
  simp [executeRuntimeElement, ScriptElement.pushSize, prepareValidationWeight,
    evaluate.eq_1, evaluate.eq_2, evaluate.eq_3]

theorem runtimeStep_normalizeSerializedElement
    (oracle : CryptoOracle) (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (normalizeSerializedElement element) state flags ctx =
      runtimeStep oracle element state flags ctx := by
  simp only [runtimeStep, executeRuntimeElement_normalizeSerializedElement]

/-- Every source-order step, including skipped pushes, preserves its state or
    exact error. Open conditionals and arbitrary initial resource states are covered. -/
theorem evaluateRuntime_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluateRuntime oracle (normalizeSerializedScript script) state flags ctx =
      evaluateRuntime oracle script state flags ctx := by
  induction script generalizing state with
  | nil => rfl
  | cons element rest ih =>
      simp only [normalizeSerializedScript, List.map_cons, evaluateRuntime,
        runtimeStep_normalizeSerializedElement] at *
      cases runtimeStep oracle element state flags ctx <;> simp [ih]

theorem evaluateWithRuntimeLimits_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (stack alt : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    evaluateWithRuntimeLimits oracle (normalizeSerializedScript script)
        stack alt flags ctx weight =
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight :=
  evaluateRuntime_normalizeSerializedScript oracle script _ flags ctx

/-- Witness-byte binding, annex checks, initial limits, transaction-derived
    sighashes and runtime execution produce the same complete result. -/
theorem evaluateTapscript_normalizeSerializedScript
    (oracle : CryptoOracle) (script : Script) (witness : TapscriptWitness)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluateTapscript oracle (normalizeSerializedScript script) witness flags ctx =
      evaluateTapscript oracle script witness flags ctx := by
  simp only [evaluateTapscript, serializeScript_normalizeSerializedScript,
    evaluateWithRuntimeLimits_normalizeSerializedScript]

/-- Successful serialization followed by decoding and execution has exactly
    the original result. Decode errors remain explicit in the result type. -/
theorem evaluate_deserializeScript_serializeScript
    (oracle : CryptoOracle) (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    (deserializeScript encoded).map (fun decoded => evaluate oracle decoded stack alt flags ctx) =
      .ok (evaluate oracle script stack alt flags ctx) := by
  rw [deserializeScript_serializeScript script encoded serialized]
  simp only [Except.map, evaluate_normalizeSerializedScript]

theorem evaluateWithRuntimeLimits_deserializeScript_serializeScript
    (oracle : CryptoOracle) (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    (deserializeScript encoded).map (fun decoded =>
        evaluateWithRuntimeLimits oracle decoded stack alt flags ctx weight) =
      .ok (evaluateWithRuntimeLimits oracle script stack alt flags ctx weight) := by
  rw [deserializeScript_serializeScript script encoded serialized]
  simp only [Except.map, evaluateWithRuntimeLimits_normalizeSerializedScript]

theorem evaluateTapscript_deserializeScript_serializeScript
    (oracle : CryptoOracle) (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    (deserializeScript encoded).map (fun decoded =>
        evaluateTapscript oracle decoded witness flags ctx) =
      .ok (evaluateTapscript oracle script witness flags ctx) := by
  rw [deserializeScript_serializeScript script encoded serialized]
  simp only [Except.map, evaluateTapscript_normalizeSerializedScript]

end LeanMiniscript.Script
