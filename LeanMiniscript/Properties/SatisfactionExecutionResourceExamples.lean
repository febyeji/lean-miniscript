import LeanMiniscript.Properties.SatisfactionExecutionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-! Build-checked uses of the generated satisfaction resource theorem. -/

private abbrev conditionalKeySpend (key : PubKey) : CoreFragment :=
  .or_i (.c (.pk_k key)) (.c (.pk_k key))

/-- A selected conditional key-spend witness has one concrete resource
    observation bounded by its jointly selected stack and opcode path. -/
example {key : PubKey} {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (valid : ValidMiniscript .tapscript (conditionalKeySpend key))
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (generated : satisfyFinal (conditionalKeySpend key) env = some witness) :
    ∃ result resources stackLimit dynamicLimit,
      EvalResources (compile (conditionalKeySpend key)) witness.toInitialStack
        [] flags env.txCtx [result] [] resources ∧
      castToBool result = true ∧
      (stackPathBounds (conditionalKeySpend key)).sat = some stackLimit ∧
      (opPathBounds (conditionalKeySpend key)).sat = some dynamicLimit ∧
      Int.ofNat resources.peakStackItems ≤ stackLimit.exec + 1 ∧
      resources.executedMultiSigKeys ≤ dynamicLimit := by
  exact satisfyFinal_evalResources_le valid sound encodings version modeled
    generated

/-- A selected legacy multisignature witness is bounded by the same path's
    stack summary and executed-key charge summary. -/
example {key : PubKey} {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (valid : ValidMiniscript .p2wsh (.multi 1 [key]))
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (generated : satisfyFinal (.multi 1 [key]) env = some witness) :
    ∃ result resources stackLimit dynamicLimit,
      EvalResources (compile (.multi 1 [key])) witness.toInitialStack [] flags
        env.txCtx [result] [] resources ∧
      castToBool result = true ∧
      (stackPathBounds (.multi 1 [key])).sat = some stackLimit ∧
      (opPathBounds (.multi 1 [key])).sat = some dynamicLimit ∧
      Int.ofNat resources.peakStackItems ≤ stackLimit.exec + 1 ∧
      resources.executedMultiSigKeys ≤ dynamicLimit := by
  exact satisfyFinal_evalResources_le valid sound encodings version modeled
    generated

end LeanMiniscript.Properties
