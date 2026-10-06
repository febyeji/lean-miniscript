import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Script.TapscriptExecutionProofs

/-! Oracle-refinement agreement for executable Tapscript acceptance. -/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- The executable check exactly reflects the existing acceptance proposition
    when the supplied cryptographic oracle agrees with the model. -/
theorem checkTapscriptAcceptance_iff
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags) (txCtx : TxContext) :
    (∃ weight, checkTapscriptAcceptance oracle script witness flags txCtx = .ok weight) ↔
      TapscriptAccepts script witness flags txCtx := by
  by_cases enabled : flags.minimalData = true
  · have checkEq : checkTapscriptAcceptance oracle script witness flags txCtx =
        (evaluateTapscript CryptoOracle.model script witness flags txCtx).checkAcceptance := by
      simp [checkTapscriptAcceptance, enabled, evaluateTapscript_eq_model agreement]
    constructor
    · rintro ⟨weight, checked⟩
      rw [checkEq] at checked
      obtain ⟨top, alt, evaluated, truth⟩ :=
        (WeightedResult.checkAcceptance_ok_iff _ weight).mp checked
      exact ⟨enabled, top, alt, weight, evaluated, truth⟩
    · rintro ⟨_, top, alt, weight, evaluated, truth⟩
      refine ⟨weight, ?_⟩
      rw [checkEq]
      exact (WeightedResult.checkAcceptance_ok_iff _ weight).mpr ⟨top, alt, evaluated, truth⟩
  · have checkEq : checkTapscriptAcceptance oracle script witness flags txCtx =
        .error .tapscriptFlags := by
      simp [checkTapscriptAcceptance, enabled]
    constructor
    · rintro ⟨weight, checked⟩
      rw [checkEq] at checked
      contradiction
    · rintro ⟨modeled, _⟩
      exact False.elim (enabled modeled)

private def contractExampleFlags : ScriptFlags := {}

private def contractExampleTxCtx : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩
  sigVersion := .witnessV0

/-- The acceptance contract is inhabited by the canonical true script. -/
example : Accepts .p2wsh [.pushNum 1] []
    contractExampleFlags contractExampleTxCtx := by
  refine ⟨?_, rfl, ?_⟩
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨trueElement, [], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_one] using
      (Eval.pushNum 1 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 1] [])
        (Eval.empty [scriptNum 1] [] contractExampleFlags contractExampleTxCtx))

/-- Clean-stack acceptance constrains the final main stack, not the internal
    alternate stack. -/
example : Accepts .p2wsh
    [.pushNum 1, .op .OP_TOALTSTACK, .pushNum 1] []
    contractExampleFlags contractExampleTxCtx := by
  refine ⟨?_, rfl, ?_⟩
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨scriptNum 1, [scriptNum 1], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack] using
      (Eval.pushNum 1 [.op .OP_TOALTSTACK, .pushNum 1] [] []
        contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 1] [scriptNum 1])
        (Eval.toAltStackNext (x := scriptNum 1)
          (Eval.pushNum 1 [] [] [scriptNum 1]
            contractExampleFlags contractExampleTxCtx
            (.success [scriptNum 1] [scriptNum 1])
            (Eval.empty [scriptNum 1] [scriptNum 1]
              contractExampleFlags contractExampleTxCtx))))

/-- A successful false result is a dissatisfaction, not an execution error. -/
example : Dissatisfies .p2wsh [.pushNum 0] []
    contractExampleFlags contractExampleTxCtx := by
  refine ⟨?_, rfl, ?_⟩
  · simp [ModeledContextFlags, contractExampleFlags]
  · refine ⟨falseElement, [], ?_, by native_decide⟩
    simpa [Executes, Witness.toInitialStack, scriptNum_zero] using
      (Eval.pushNum 0 [] [] [] contractExampleFlags contractExampleTxCtx
        (.success [scriptNum 0] [])
        (Eval.empty [scriptNum 0] [] contractExampleFlags contractExampleTxCtx))

/-- P2WSH acceptance rejects a flag set that disables the modeled MINIMALIF
    requirement before execution is considered. -/
example : ¬ ModeledContextFlags .p2wsh
    ({ minimalIf := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

/-- Both modeled contexts reject non-minimal numeric operands at their checked
    acceptance boundary. -/
example : ¬ ModeledContextFlags .tapscript
    ({ minimalData := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

/-- P2WSH acceptance requires the modeled pre-Tapscript encoding checks. -/
example : ¬ ModeledContextFlags .p2wsh
    ({ strictEncoding := false } : ScriptFlags) := by
  simp [ModeledContextFlags]

end LeanMiniscript.Miniscript
