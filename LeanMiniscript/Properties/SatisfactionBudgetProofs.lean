import LeanMiniscript.Miniscript.WitnessBudgetProofs
import LeanMiniscript.Properties.SatisfactionResourceProofs
import LeanMiniscript.Properties.ExecutionBudgetFrameProofs

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
