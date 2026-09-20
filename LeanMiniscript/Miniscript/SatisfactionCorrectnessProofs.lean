import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Core and surface satisfaction and dissatisfaction correctness

The recursive generated contract already supplies exact B execution for every
usable top-level candidate. This module closes the public core clean-stack
targets and transports them across the surface desugaring boundary.
-/

namespace GeneratedContract

/-- A top-level B contract yields the clean one-item result used by public
    acceptance and dissatisfaction. -/
theorem cleanStackResult
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) :
    CleanStackResult (compile fragment) witness flags txCtx expected := by
  cases contract with
  | b input facts executed =>
      exact BExecutionOutcome.cleanStackResult ⟨_, executed, facts.truth⟩

end GeneratedContract

/-- Every usable satisfaction generated for a valid core Miniscript is
    accepted by the resource-free modeled execution predicate. -/
theorem satisfactionCorrectnessCore : SatisfactionCorrectnessCore := by
  intro ctx fragment env witness flags valid sound encodings version modeled
    generated
  rcases valid with ⟨mods, wellFormed, typed⟩
  have supported := supportsGeneratedContract_of_wellFormed_hasType
    version modeled sound encodings typed wellFormed
  exact ⟨modeled, version,
    (supported.satisfyContract generated).cleanStackResult⟩

/-- The final HASSIG-filtered satisfaction API inherits core satisfaction
    correctness from the ordinary selected candidate. -/
theorem satisfyFinalCorrectnessCore
    {ctx : ScriptContext} {fragment : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (valid : ValidMiniscript ctx fragment)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfyFinal fragment env = some witness) :
    Accepts ctx (compile fragment) witness flags env.txCtx :=
  satisfactionCorrectnessCore valid sound encodings version modeled
    (satisfyFinal_some_satisfy generated)

/-- Every usable dissatisfaction generated for a valid dissatisfiable core
    Miniscript executes successfully to a clean false result. -/
theorem dissatisfactionCorrectnessCore : DissatisfactionCorrectnessCore := by
  intro ctx fragment env witness flags valid sound encodings version modeled
    generated
  rcases valid with ⟨mods, ⟨wellFormed, typed⟩, dissatisfiable⟩
  have supported := supportsGeneratedContract_of_wellFormed_hasType
    version modeled sound encodings typed wellFormed
  exact ⟨modeled, version,
    (supported.dissatisfyContract generated).cleanStackResult⟩

/-- Surface satisfaction inherits core correctness because surface compilation
    is compilation of the desugared core fragment. -/
theorem satisfactionCorrectnessSurface : SatisfactionCorrectnessSurface := by
  intro ctx fragment env witness flags valid sound encodings version modeled
    generated
  simpa [compileSurface, compileSurfaceWithKeyHash, compile] using
    satisfactionCorrectnessCore valid sound encodings version modeled
      generated

/-- Surface compilation inherits final HASSIG-filtered satisfaction
    correctness through desugaring. -/
theorem satisfyFinalCorrectnessSurface
    {ctx : ScriptContext} {fragment : SurfaceFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (valid : ValidSurfaceMiniscript ctx fragment)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfyFinal (desugar fragment) env = some witness) :
    Accepts ctx (compileSurface fragment) witness flags env.txCtx :=
  satisfactionCorrectnessSurface valid sound encodings version modeled
    (satisfyFinal_some_satisfy generated)

/-- Surface dissatisfaction is the corresponding desugaring corollary of core
    dissatisfaction correctness. -/
theorem dissatisfactionCorrectnessSurface :
    DissatisfactionCorrectnessSurface := by
  intro ctx fragment env witness flags valid sound encodings version modeled
    generated
  simpa [compileSurface, compileSurfaceWithKeyHash, compile] using
    dissatisfactionCorrectnessCore valid sound encodings version modeled
      generated

end LeanMiniscript.Miniscript
