import LeanMiniscript.Properties.ResourcePathProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript

/-! Regression examples for generated witness stack-path bounds. -/

/-- The public extraction theorem applies to the smallest valid B fragment.
    A final `.one` witness is semantically unavailable, so the selected premise
    also records that boundary. -/
example (scriptCtx : ScriptContext) (env : SatEnv) {witness : Witness}
    (selected : satisfyFinal .one env = some witness) :
    ∃ limit,
      maxSatisfactionInitialStack .one = some limit ∧
      Int.ofNat witness.length ≤ limit := by
  apply satisfyFinal_length_le_maxSatisfactionInitialStack
    (scriptCtx := scriptCtx) (env := env)
  · exact ⟨{ z := true, u := true }, ⟨by simp [CoreFragment.WellFormed],
      HasType.one⟩⟩
  · exact selected

private def andVGeneratedDsat (key : PubKey) : CoreFragment :=
  .and_v (.v .one) (.multi 1 [key])

private def andorGeneratedDsat (key : PubKey) : CoreFragment :=
  .andor (.c (.pk_k key)) (.multi 1 [key]) .zero

/-- The `and_v` dissatisfaction summary covers the generated second-child
    dissatisfaction after a satisfying V prefix. -/
example (key : PubKey) :
    wellTyped .p2wsh (andVGeneratedDsat key) ∧
      (stackPathBounds (andVGeneratedDsat key)).dsat = some ⟨1, 4⟩ ∧
      (opPathBounds (andVGeneratedDsat key)).dsat = some 1 := by
  refine ⟨⟨⟨.B, { n := true, u := true }⟩, ?_⟩, rfl, rfl⟩
  simpa [andVGeneratedDsat, branchBase] using
    (HasType.and_v (HasType.v_wrap HasType.one)
      (HasType.multi 1 [key] (by omega) (by simp)) (by decide))

/-- The `andor` dissatisfaction summary includes the usable noncanonical true
    branch when it dominates the canonical false branch. -/
example (key : PubKey) (validKey : validResolvedPubKey .p2wsh key) :
    CoreFragment.WellFormed .p2wsh (andorGeneratedDsat key) ∧
      wellTyped .p2wsh (andorGeneratedDsat key) ∧
      (stackPathBounds (andorGeneratedDsat key)).dsat = some ⟨2, 4⟩ ∧
      (opPathBounds (andorGeneratedDsat key)).dsat = some 1 := by
  refine ⟨?_, ⟨⟨.B, { d := true, u := true }⟩, ?_⟩, rfl, rfl⟩
  · simp [andorGeneratedDsat, CoreFragment.WellFormed,
      CoreFragment.allKeysValid, ScriptContext.permitsLegacyMulti,
      validThreshold, validLegacyMultiKeyCount,
      CoreFragment.andorTimelocksCompatible,
      CoreFragment.andTimelocksCompatible,
      CoreFragment.timelocks, TimelockUsage.empty,
      TimelockUsage.compatibleWith, validKey]
  simpa [andorGeneratedDsat, branchBase] using
    (HasType.andor
      (HasType.c_wrap (HasType.pk_k key)) rfl rfl
      (HasType.multi 1 [key] (by omega) (by simp)) HasType.zero
      (by decide) rfl)

private def singleSignedThreshold (key : PubKey) : CoreFragment :=
  .thresh 1 [.c (.pk_k key)]

private theorem singleSignedThreshold_valid (key : PubKey)
    (validKey : validResolvedPubKey .p2wsh key) :
    ValidMiniscript .p2wsh (singleSignedThreshold key) := by
  have wellFormed :
      CoreFragment.WellFormed .p2wsh (singleSignedThreshold key) := by
    simp [singleSignedThreshold, CoreFragment.WellFormed,
      CoreFragment.allWellFormed, validThreshold, validKey]
  refine ⟨{ o := true, d := true, u := true }, wellFormed, ?_⟩
  simpa [singleSignedThreshold, CorrectnessModifiers.allZ,
      CorrectnessModifiers.oneOWithRestZ, MiniType.modifiers] using
    (HasType.thresh (ctx := .p2wsh)
      (k := 1) (X := .c (.pk_k key)) (Xs := []) (restTypes := [])
      (HasType.c_wrap (HasType.pk_k key)) rfl rfl
      HasTypeList.nil (by simp [thresholdRestTypes]) (by omega) (by simp))

/-- A concrete one-of-one threshold path has a one-item initial-witness bound,
    and every selected final witness is covered by that computed value. -/
example (key : PubKey) (validKey : validResolvedPubKey .p2wsh key)
    (env : SatEnv) {witness : Witness}
    (selected : satisfyFinal (singleSignedThreshold key) env = some witness) :
    maxSatisfactionInitialStack (singleSignedThreshold key) = some 1 ∧
      Int.ofNat witness.length ≤ 1 := by
  have exactLimit :
      maxSatisfactionInitialStack (singleSignedThreshold key) = some 1 := by
    rfl
  obtain ⟨limit, computed, bounded⟩ :=
    satisfyFinal_length_le_maxSatisfactionInitialStack
      (singleSignedThreshold_valid key validKey) selected
  rw [exactLimit] at computed
  cases computed
  exact ⟨exactLimit, bounded⟩

end LeanMiniscript.Properties
