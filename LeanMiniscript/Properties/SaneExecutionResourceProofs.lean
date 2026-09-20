import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Properties.ResourceCompilerMetricProofs
import LeanMiniscript.Properties.ResourcePathProofs
import LeanMiniscript.Properties.SatisfactionExecutionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

private theorem resourceLimitComponents
    {ctx : ScriptContext} (sane : SaneFragment ctx) :
    satisfactionOpsWithinLimit ctx sane.checked.fragment = true ∧
      satisfactionStackWithinLimit ctx sane.checked.fragment = true := by
  have limits := sane.withinResourceLimits
  unfold WithinResourceLimits resourceLimitsSatisfied at limits
  have outer := Bool.and_eq_true_iff.mp limits
  have inner := Bool.and_eq_true_iff.mp outer.1
  exact ⟨inner.2, outer.2⟩

end LeanMiniscript.Properties

namespace LeanMiniscript.Miniscript.SaneFragment

open LeanMiniscript.Properties
open LeanMiniscript.Script

/-- A generated witness for a sane P2WSH fragment has at most the standard
    number of initial witness items. -/
theorem p2wsh_satisfyFinal_witness_length_le
    (sane : SaneFragment .p2wsh) {env : SatEnv} {witness : Witness}
    (generated : satisfyFinal sane.checked.fragment env = some witness) :
    witness.length ≤ MAX_STANDARD_P2WSH_STACK_ITEMS := by
  obtain ⟨limit, limitEq, witnessLe⟩ :=
    sane.satisfyFinal_length_le_maxSatisfactionInitialStack generated
  have stackWithin := (resourceLimitComponents sane).2
  simp only [satisfactionStackWithinLimit] at stackWithin
  rw [limitEq] at stackWithin
  have limitLe : limit ≤ Int.ofNat MAX_STANDARD_P2WSH_STACK_ITEMS :=
    of_decide_eq_true stackWithin
  exact Int.ofNat_le.mp (Int.le_trans witnessLe limitLe)

/-- A generated execution for a sane P2WSH fragment respects the standard
    witness-item limit and the consensus static-plus-multisig opcode limit. -/
theorem p2wsh_satisfyFinal_executionLimits
    (sane : SaneFragment .p2wsh) {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfyFinal sane.checked.fragment env = some witness) :
    ∃ result resources,
      EvalResources sane.compile witness.toInitialStack [] flags env.txCtx
        [result] [] resources ∧
      castToBool result = true ∧
      witness.length ≤ MAX_STANDARD_P2WSH_STACK_ITEMS ∧
      nonPushOpCount sane.compile +
          resources.executedMultiSigKeys ≤ MAX_OPS_PER_SCRIPT := by
  obtain ⟨result, resources, stackLimit, dynamicLimit, evaluated, truth,
      stackEq, dynamicEq, peakLe, dynamicLe⟩ :=
    satisfyFinal_evalResources_le sane.validMiniscript sound encodings version
      modeled generated
  have opsWithin := (LeanMiniscript.Properties.resourceLimitComponents sane).1
  simp only [satisfactionOpsWithinLimit, maxSatisfactionOpCount_eq_compile,
    dynamicEq, Option.map_some] at opsWithin
  have summaryCharge :
      nonPushOpCount (LeanMiniscript.Miniscript.compile sane.checked.fragment) +
          dynamicLimit ≤ MAX_OPS_PER_SCRIPT :=
    of_decide_eq_true opsWithin
  have actualCharge :
      nonPushOpCount sane.compile +
          resources.executedMultiSigKeys ≤ MAX_OPS_PER_SCRIPT := by
    simpa [SaneFragment.compile, compileChecked] using
      (show
        nonPushOpCount
              (LeanMiniscript.Miniscript.compile sane.checked.fragment) +
            resources.executedMultiSigKeys ≤ MAX_OPS_PER_SCRIPT by
        omega)
  have evaluatedSane :
      EvalResources sane.compile witness.toInitialStack [] flags env.txCtx
        [result] [] resources := by
    simpa [SaneFragment.compile, compileChecked] using evaluated
  exact ⟨result, resources, evaluatedSane, truth,
    sane.p2wsh_satisfyFinal_witness_length_le generated, actualCharge⟩

/-- A generated execution for a sane Tapscript fragment never exceeds the
    consensus combined main/alternate-stack limit. -/
theorem tapscript_satisfyFinal_executionStack_le
    (sane : SaneFragment .tapscript) {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (generated : satisfyFinal sane.checked.fragment env = some witness) :
    ∃ result resources,
      EvalResources sane.compile witness.toInitialStack [] flags env.txCtx
        [result] [] resources ∧
      castToBool result = true ∧
      resources.peakStackItems ≤ MAX_STACK_SIZE := by
  obtain ⟨result, resources, stackLimit, dynamicLimit, evaluated, truth,
      stackEq, dynamicEq, peakLe, dynamicLe⟩ :=
    satisfyFinal_evalResources_le sane.validMiniscript sound encodings version
      modeled generated
  have stackWithin := (LeanMiniscript.Properties.resourceLimitComponents sane).2
  simp only [satisfactionStackWithinLimit, maxSatisfactionExecutionStack,
    stackEq, Option.map_some] at stackWithin
  have summaryPeak :
      stackLimit.exec + 1 ≤ Int.ofNat MAX_STACK_SIZE :=
    of_decide_eq_true stackWithin
  have evaluatedSane :
      EvalResources sane.compile witness.toInitialStack [] flags env.txCtx
        [result] [] resources := by
    simpa [SaneFragment.compile, compileChecked] using evaluated
  exact ⟨result, resources, evaluatedSane, truth,
    Int.ofNat_le.mp (Int.le_trans peakLe summaryPeak)⟩

end LeanMiniscript.Miniscript.SaneFragment
