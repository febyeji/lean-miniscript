import LeanMiniscript.Miniscript.WitnessBudgetProofs
import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

/-- Payload bytes available to fund signature debits. -/
def witnessPayload (witness : Witness) : Nat := (witness.map ByteArray.size).sum

@[simp] theorem witnessPayload_combine (first second : Witness) :
    witnessPayload (Witness.combine first second) = witnessPayload first + witnessPayload second := by
  simp [witnessPayload, Witness.combine, Nat.add_comm]

@[simp] theorem witnessPayload_selector (witness : Witness) (selector : StackElement) :
    witnessPayload (Witness.withSelector witness selector) = witnessPayload witness + selector.size := by
  simp [witnessPayload, Witness.withSelector]

@[simp] theorem witnessPayload_append (first second : Witness) :
    witnessPayload (first ++ second) = witnessPayload first + witnessPayload second := by
  simp [witnessPayload]

@[simp] theorem witnessPayload_initial (witness : Witness) :
    witnessPayload witness.toInitialStack = witnessPayload witness := by
  simp [witnessPayload, Witness.toInitialStack]

@[simp] theorem witnessPayload_frames (frames : List Witness) :
    witnessPayload (frames.map Witness.toInitialStack).flatten = (frames.map witnessPayload).sum := by
  induction frames with
  | nil => rfl
  | cons frame frames ih => simp [ih]

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

/-- Generated execution with enough witness payload for its signature debit.
K fragments also reserve the debit of the signature they leave for c:. -/
inductive GeneratedBudgetContract (fragment : CoreFragment) (witness : Witness)
    (expected : Bool) (flags : ScriptFlags) (txCtx : TxContext) : MiniType → Prop where
  | b {mods : CorrectnessModifiers} {result : StackElement} {value : Int} {budget : Nat}
      (input : GeneratedInput witness expected mods)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : BExecution fragment witness.toInitialStack result flags txCtx)
      (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [result] flags txCtx budget)
      (funded : budget ≤ witnessPayload witness) :
      GeneratedBudgetContract fragment witness expected flags txCtx ⟨.B, mods⟩
  | v {mods : CorrectnessModifiers} {budget : Nat}
      (input : GeneratedInput witness expected mods) (expectedTrue : expected = true)
      (executed : VExecution fragment witness.toInitialStack flags txCtx)
      (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [] flags txCtx budget)
      (funded : budget ≤ witnessPayload witness) :
      GeneratedBudgetContract fragment witness expected flags txCtx ⟨.V, mods⟩
  | k {mods : CorrectnessModifiers} {budget : Nat}
      (input : GeneratedInput witness expected mods) (ownArgs : Stack) (key signature : StackElement)
      (shape : witness.toInitialStack = ownArgs ++ [signature])
      (executed : KExecution fragment ownArgs key flags txCtx)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx signature key = .ok expected)
      (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [key, signature] flags txCtx budget)
      (funded : budget + signatureValidationWeight signature ≤ witnessPayload witness) :
      GeneratedBudgetContract fragment witness expected flags txCtx ⟨.K, mods⟩
  | w {mods : CorrectnessModifiers} {result : StackElement} {value : Int} {budget : Nat}
      (input : GeneratedInput witness expected mods) (order : WStackOrder)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : WExecution fragment witness.toInitialStack result order flags txCtx)
      (frame : ∀ saved, ExecutesBudgetFrame (compile fragment) (saved :: witness.toInitialStack)
        (order.outputs saved result) flags txCtx budget)
      (funded : budget ≤ witnessPayload witness) :
      GeneratedBudgetContract fragment witness expected flags txCtx ⟨.W, mods⟩

namespace GeneratedBudgetContract

theorem toGeneratedContract {fragment : CoreFragment} {witness : Witness}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext} {ty : MiniType}
    (contract : GeneratedBudgetContract fragment witness expected flags txCtx ty) :
    GeneratedContract fragment witness expected flags txCtx ty := by
  cases contract with
  | b input facts executed => exact .b input facts executed
  | v input truth executed => exact .v input truth executed
  | k input ownArgs key signature shape executed checked => exact .k input ownArgs key signature shape executed checked
  | w input order facts executed => exact .w input order facts executed

end GeneratedBudgetContract

theorem generatedBudgetB_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {result : StackElement} {budget : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx ⟨.B, mods⟩)
    (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [result] flags txCtx budget)
    (funded : budget ≤ witnessPayload witness) :
    GeneratedBudgetContract fragment witness expected flags txCtx ⟨.B, mods⟩ := by
  cases contract with
  | b input facts executed => exact .b input facts executed (frame.alignOutputs executed) funded

theorem generatedBudgetV_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers} {budget : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx ⟨.V, mods⟩)
    (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [] flags txCtx budget)
    (funded : budget ≤ witnessPayload witness) :
    GeneratedBudgetContract fragment witness expected flags txCtx ⟨.V, mods⟩ := by
  cases contract with
  | v input truth executed => exact .v input truth executed frame funded

theorem generatedBudgetK_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {key signature : StackElement} {budget : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx ⟨.K, mods⟩)
    (frame : ExecutesBudgetFrame (compile fragment) witness.toInitialStack [key, signature] flags txCtx budget)
    (funded : budget + signatureValidationWeight signature ≤ witnessPayload witness) :
    GeneratedBudgetContract fragment witness expected flags txCtx ⟨.K, mods⟩ := by
  cases contract with
  | k input ownArgs actualKey actualSignature shape executed checked =>
      have target : ExecutesStackFrame (compile fragment) witness.toInitialStack
          [actualKey, actualSignature] flags txCtx := by
        rw [shape]
        simpa using executed.withSuffix (suffix := [actualSignature])
      have same := frame.outputs_eq target
      simp only [List.cons.injEq, and_true] at same
      obtain ⟨rfl, rfl⟩ := same
      exact .k input ownArgs _ _ shape executed checked frame funded

theorem generatedBudgetW_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {outputs : StackElement → Stack} {budget : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx ⟨.W, mods⟩)
    (frame : ∀ saved, ExecutesBudgetFrame (compile fragment) (saved :: witness.toInitialStack)
      (outputs saved) flags txCtx budget)
    (funded : budget ≤ witnessPayload witness) :
    GeneratedBudgetContract fragment witness expected flags txCtx ⟨.W, mods⟩ := by
  cases contract with
  | w input order facts executed =>
      exact .w input order facts executed (fun saved => (frame saved).alignOutputs (executed saved)) funded

end LeanMiniscript.Properties
