import LeanMiniscript.Properties.SatisfactionGeneratedBudgetRecursiveProofs
import LeanMiniscript.Miniscript.Soundness

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

/-- Every generated final Tapscript satisfaction funds its active signature
debit from its argument payload. Resource uniqueness makes the bound apply to
any observation of the generated execution. The recursive contract reserves
pending K signatures and composes payload budgets in witness order.
This theorem inherits the existing generated-satisfaction native_decide facts. -/
theorem satisfyFinal_signatureWeight_le_payload
    {fragment : CoreFragment} {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags} {top : StackElement} {resources : ExecutionResources}
    (valid : ValidMiniscript .tapscript fragment)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (generated : satisfyFinal fragment env = some witness)
    (observed : EvalResources (compile fragment) witness.toInitialStack [] flags env.txCtx
      [top] [] resources) :
    resources.signatureWeight ≤ (witness.map ByteArray.size).sum := by
  rcases valid with ⟨mods, wellFormed, typed⟩
  have supported := supportsGeneratedBudgets_of_wellFormed_hasType
    version modeled sound encodings typed wellFormed
  have contract := supported.satisfyContract (satisfyFinal_some_satisfy generated)
  cases contract with
  | b input facts executed frame funded =>
      obtain ⟨actual, evaluated, cost⟩ := frame [] []
      have same := observed.resources_unique (by simpa using evaluated)
      rw [same]
      exact Nat.le_trans cost funded

end LeanMiniscript.Properties
