import LeanMiniscript.Properties.SatisfactionGeneratedResourceRecursiveProofs
import LeanMiniscript.Miniscript.Soundness

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Generated satisfaction execution resources

The recursive resource contract yields one concrete successful observation for
the public final witness.  Both bounds come from the same selected satisfaction
path.
-/

/-- A successful final generated satisfaction has a concrete resource
    observation whose stack peak and executed legacy-multisignature key charge
    are bounded by the jointly selected public satisfaction summaries. -/
theorem satisfyFinal_evalResources_le
    {ctx : ScriptContext} {fragment : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (valid : ValidMiniscript ctx fragment)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfyFinal fragment env = some witness) :
    ∃ result resources stackLimit dynamicLimit,
      EvalResources (compile fragment) witness.toInitialStack [] flags env.txCtx
        [result] [] resources ∧
      castToBool result = true ∧
      (stackPathBounds fragment).sat = some stackLimit ∧
      (opPathBounds fragment).sat = some dynamicLimit ∧
      Int.ofNat resources.peakStackItems ≤ stackLimit.exec + 1 ∧
      resources.executedMultiSigKeys ≤ dynamicLimit := by
  rcases valid with ⟨mods, wellFormed, typed⟩
  have supported := supportsGeneratedResources_of_wellFormed_hasType
    version modeled sound encodings typed wellFormed
  have contract := supported.satisfyContract
    (satisfyFinal_some_satisfy generated)
  cases contract with
  | @b _ result value trace dynamic input facts executed bounded stackSelected
      opSelected =>
      obtain ⟨resources, observed, peak, charge⟩ := bounded.run [] []
      refine ⟨result, resources, trace, dynamic, ?_, facts.truth, ?_, ?_, ?_,
        charge⟩
      · simpa using observed
      · simpa [selectedStackSummary] using stackSelected
      · simpa [selectedOpSummary] using opSelected
      · simp only [List.append_nil, List.length_singleton, List.length_nil,
          Nat.add_zero] at peak
        simpa [Int.add_comm] using peak

end LeanMiniscript.Properties
