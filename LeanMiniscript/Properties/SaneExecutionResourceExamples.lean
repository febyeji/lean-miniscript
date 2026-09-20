import LeanMiniscript.Properties.SaneExecutionResourceProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Properties
open LeanMiniscript.Script

/-! # Sane generated-execution limit examples -/

/-- The witness-item corollary does not require execution-oracle assumptions. -/
example (sane : SaneFragment .p2wsh) {env : SatEnv} {witness : Witness}
    (generated : satisfyFinal sane.checked.fragment env = some witness) :
    witness.length ≤ MAX_STANDARD_P2WSH_STACK_ITEMS := by
  exact sane.p2wsh_satisfyFinal_witness_length_le generated

/-- P2WSH accounting combines static opcodes from the compiled script with
    the CHECKMULTISIG key charge observed along the selected execution. -/
example (sane : SaneFragment .p2wsh) {env : SatEnv} {witness : Witness}
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
  exact sane.p2wsh_satisfyFinal_executionLimits sound encodings version
    modeled generated

/-- Tapscript accounting bounds the observed peak across the main and
    alternate stacks. -/
example (sane : SaneFragment .tapscript) {env : SatEnv} {witness : Witness}
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
  exact sane.tapscript_satisfyFinal_executionStack_le sound encodings version
    modeled generated

end LeanMiniscript.Miniscript
