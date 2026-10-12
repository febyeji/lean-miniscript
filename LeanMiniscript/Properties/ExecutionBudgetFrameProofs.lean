import LeanMiniscript.Properties.ExecutionResourceFrameProofs
import LeanMiniscript.Script.RuntimeCompletenessProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

/-- A signature-debit bound uniform in the protected stack suffix. -/
def ExecutesBudgetFrame (script : Script) (inputs outputs : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (budget : Nat) : Prop :=
  ∀ rest alt, ∃ resources,
    EvalResources script (inputs ++ rest) alt flags ctx (outputs ++ rest) alt resources ∧
    resources.signatureWeight ≤ budget

namespace ExecutesBudgetFrame

theorem of_zero {script : Script} {inputs outputs : Stack} {flags : ScriptFlags}
    {ctx : TxContext} (executed : ExecutesStackFrame script inputs outputs flags ctx)
    (zero : staticValidationWeight script = 0) :
    ExecutesBudgetFrame script inputs outputs flags ctx 0 := by
  intro rest alt
  obtain ⟨resources, observed⟩ := EvalResources.exists_of_eval_success (executed rest alt)
  exact ⟨resources, observed, zero ▸ observed.signatureWeight_le_static⟩

theorem of_resource_zero {script : Script} {inputs outputs : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {trace : StackTraceBound} {dynamic : Nat}
    (frame : ExecutesResourceFrame script inputs outputs flags ctx trace dynamic)
    (zero : staticValidationWeight script = 0) :
    ExecutesBudgetFrame script inputs outputs flags ctx 0 := by
  apply of_zero _ zero
  intro rest alt
  obtain ⟨_, observed, _, _⟩ := frame.run rest alt
  exact observed.toEval

theorem single {element : ScriptElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (executed : ExecutesStackFrame [element] inputs outputs flags ctx)
    (cost : ∀ rest, executedSignatureWeight element (inputs ++ rest) ctx ≤ budget) :
    ExecutesBudgetFrame [element] inputs outputs flags ctx budget := by
  intro rest alt
  refine ⟨_, EvalResources.step (executed rest alt)
    (EvalResources.empty (outputs ++ rest) alt flags ctx), ?_⟩
  simpa using cost rest

theorem empty (inputs : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [] inputs inputs flags ctx 0 := by
  intro rest alt
  exact ⟨_, .empty _ _ _ _, Nat.le_refl 0⟩

theorem append {left right : Script} {inputs middle outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {first second : Nat}
    (a : ExecutesBudgetFrame left inputs middle flags ctx first)
    (b : ExecutesBudgetFrame right middle outputs flags ctx second) :
    ExecutesBudgetFrame (left ++ right) inputs outputs flags ctx (first + second) := by
  intro rest alt
  obtain ⟨ar, ae, ab⟩ := a rest alt
  obtain ⟨br, be, bb⟩ := b rest alt
  exact ⟨_, ae.append be, Nat.add_le_add ab bb⟩

theorem mono {script : Script} {inputs outputs : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {budget upper : Nat}
    (frame : ExecutesBudgetFrame script inputs outputs flags ctx budget)
    (bound : budget ≤ upper) :
    ExecutesBudgetFrame script inputs outputs flags ctx upper := by
  intro rest alt
  obtain ⟨resources, observed, cost⟩ := frame rest alt
  exact ⟨resources, observed, Nat.le_trans cost bound⟩

theorem withSuffix {script : Script} {inputs outputs suffix : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (frame : ExecutesBudgetFrame script inputs outputs flags ctx budget) :
    ExecutesBudgetFrame script (inputs ++ suffix) (outputs ++ suffix) flags ctx budget := by
  intro rest alt
  simpa [List.append_assoc] using frame (suffix ++ rest) alt

theorem outputs_eq {script : Script} {inputs outputs target : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (frame : ExecutesBudgetFrame script inputs outputs flags ctx budget)
    (executed : ExecutesStackFrame script inputs target flags ctx) : outputs = target := by
  obtain ⟨_, observed, _⟩ := frame [] []
  simpa using Eval.result_unique observed.toEval (executed [] [])

theorem alignOutputs {script : Script} {inputs outputs target : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (frame : ExecutesBudgetFrame script inputs outputs flags ctx budget)
    (executed : ExecutesStackFrame script inputs target flags ctx) :
    ExecutesBudgetFrame script inputs target flags ctx budget := by
  rw [← frame.outputs_eq executed]
  exact frame

theorem compileVerify {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (balanced : BalancedControlFlow script)
    (frame : ExecutesBudgetFrame (script ++ [.op .OP_VERIFY]) inputs outputs flags ctx budget) :
    ExecutesBudgetFrame (LeanMiniscript.Miniscript.compileVerify script) inputs outputs flags ctx budget := by
  intro rest alt
  obtain ⟨resources, observed, bound⟩ := frame rest alt
  exact ⟨resources, EvalResources.compileVerify_success balanced observed, bound⟩

theorem ifSelected {script : Script} {frame : ConditionalFrame} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (split : splitConditional script = some frame)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesBudgetFrame (frame.select (castToBool selector)) inputs outputs flags ctx budget) :
    ExecutesBudgetFrame (.op .OP_IF :: script) (selector :: inputs) outputs flags ctx budget := by
  intro rest alt
  obtain ⟨resources, observed, bound⟩ := selected rest alt
  exact ⟨_, .if_execute split minimal observed, by simpa using bound⟩

theorem notifSelected {script : Script} {frame : ConditionalFrame} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext} {budget : Nat}
    (split : splitConditional script = some frame)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesBudgetFrame (frame.select (!castToBool selector)) inputs outputs flags ctx budget) :
    ExecutesBudgetFrame (.op .OP_NOTIF :: script) (selector :: inputs) outputs flags ctx budget := by
  intro rest alt
  obtain ⟨resources, observed, bound⟩ := selected rest alt
  exact ⟨_, .notif_execute split minimal observed, by simpa using bound⟩

end ExecutesBudgetFrame

end LeanMiniscript.Properties
