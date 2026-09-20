import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
# Successful execution resource observations

This layer records resources along the active path of a successful `Eval`
derivation. Conditional observations recurse only into the branch selected by
`Eval.if_execute` or `Eval.notif_execute`, so instructions in skipped branches
do not contribute.
-/

/-- Dynamic resources observed along one successful Script execution. -/
structure ExecutionResources where
  /-- Largest combined main-stack and alternate-stack size, including the
      initial and final states. -/
  peakStackItems : Nat
  /-- Sum of decoded public-key counts for executed `OP_CHECKMULTISIG` and
      `OP_CHECKMULTISIGVERIFY` instructions. -/
  executedMultiSigKeys : Nat
  deriving Repr, DecidableEq

namespace ExecutionResources

/-- Resource observation for an execution containing only its current state. -/
def initial (stack altStack : Stack) : ExecutionResources :=
  { peakStackItems := stack.length + altStack.length
    executedMultiSigKeys := 0 }

/-- Add the state and multisignature charge immediately before one executed
    instruction to the observation of its continuation. -/
def prepend (stack altStack : Stack) (multiSigKeys : Nat)
    (tail : ExecutionResources) : ExecutionResources :=
  { peakStackItems := max (stack.length + altStack.length) tail.peakStackItems
    executedMultiSigKeys := multiSigKeys + tail.executedMultiSigKeys }

/-- Sequential composition of two successful execution observations. -/
def seq (left right : ExecutionResources) : ExecutionResources :=
  { peakStackItems := max left.peakStackItems right.peakStackItems
    executedMultiSigKeys := left.executedMultiSigKeys + right.executedMultiSigKeys }

@[simp] theorem initial_peakStackItems (stack altStack : Stack) :
    (initial stack altStack).peakStackItems = stack.length + altStack.length := rfl

@[simp] theorem initial_executedMultiSigKeys (stack altStack : Stack) :
    (initial stack altStack).executedMultiSigKeys = 0 := rfl

@[simp] theorem prepend_peakStackItems (stack altStack : Stack) (multiSigKeys : Nat)
    (tail : ExecutionResources) :
    (prepend stack altStack multiSigKeys tail).peakStackItems =
      max (stack.length + altStack.length) tail.peakStackItems := rfl

@[simp] theorem prepend_executedMultiSigKeys (stack altStack : Stack)
    (multiSigKeys : Nat) (tail : ExecutionResources) :
    (prepend stack altStack multiSigKeys tail).executedMultiSigKeys =
      multiSigKeys + tail.executedMultiSigKeys := rfl

@[simp] theorem seq_peakStackItems (left right : ExecutionResources) :
    (seq left right).peakStackItems =
      max left.peakStackItems right.peakStackItems := rfl

@[simp] theorem seq_executedMultiSigKeys (left right : ExecutionResources) :
    (seq left right).executedMultiSigKeys =
      left.executedMultiSigKeys + right.executedMultiSigKeys := rfl

theorem seq_assoc (first second third : ExecutionResources) :
    seq (seq first second) third = seq first (seq second third) := by
  cases first
  cases second
  cases third
  simp [seq, Nat.max_assoc, Nat.add_assoc]

end ExecutionResources

/-- Public-key charge for one successfully executed instruction. A malformed
    multisignature frame cannot occur in a successful single-instruction
    `Eval`; returning zero in that case keeps this inspection function total. -/
def executedMultiSigKeyCharge (element : ScriptElement) (stack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) : Nat :=
  match element with
  | .op .OP_CHECKMULTISIG | .op .OP_CHECKMULTISIGVERIFY =>
      match decodeCheckMultiSigOperandsFor flags ctx stack with
      | .ok operands => operands.pubkeys.length
      | .error _ => 0
  | _ => 0

@[simp] theorem executedMultiSigKeyCharge_checkmultisig
    {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands) :
    executedMultiSigKeyCharge (.op .OP_CHECKMULTISIG) stack flags ctx =
      operands.pubkeys.length := by
  simp [executedMultiSigKeyCharge, decoded]

@[simp] theorem executedMultiSigKeyCharge_checkmultisigverify
    {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands) :
    executedMultiSigKeyCharge (.op .OP_CHECKMULTISIGVERIFY) stack flags ctx =
      operands.pubkeys.length := by
  simp [executedMultiSigKeyCharge, decoded]

theorem executedMultiSigKeyCharge_eq_zero_of_opcode_ne
    {opcode : Opcode} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (notCheckMultiSig : opcode ≠ .OP_CHECKMULTISIG)
    (notCheckMultiSigVerify : opcode ≠ .OP_CHECKMULTISIGVERIFY) :
    executedMultiSigKeyCharge (.op opcode) stack flags ctx = 0 := by
  cases opcode <;> simp_all [executedMultiSigKeyCharge]

@[simp] theorem executedMultiSigKeyCharge_pushData
    (data : StackElement) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    executedMultiSigKeyCharge (.pushData data) stack flags ctx = 0 := rfl

@[simp] theorem executedMultiSigKeyCharge_pushNum
    (value : Int) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    executedMultiSigKeyCharge (.pushNum value) stack flags ctx = 0 := rfl

/-- A successful `Eval` together with the resources on its active execution
    path. Ordinary instructions reuse the existing single-instruction
    semantics. Conditional constructors recurse into the selected projection,
    which excludes skipped branches by construction. -/
inductive EvalResources : Script → Stack → Stack → ScriptFlags → TxContext →
    Stack → Stack → ExecutionResources → Prop where
  | empty (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
      EvalResources [] stack altStack flags ctx stack altStack
        (ExecutionResources.initial stack altStack)
  | step {element : ScriptElement} {rest : Script}
      {stack altStack nextStack nextAlt finalStack finalAlt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {tailResources : ExecutionResources}
      (head : Eval [element] stack altStack flags ctx
        (.success nextStack nextAlt))
      (tail : EvalResources rest nextStack nextAlt flags ctx
        finalStack finalAlt tailResources) :
      EvalResources (element :: rest) stack altStack flags ctx
        finalStack finalAlt
        (ExecutionResources.prepend stack altStack
          (executedMultiSigKeyCharge element stack flags ctx) tailResources)
  | if_execute {top : StackElement} {rest altStack : Stack}
      {script : Script} {frame : ConditionalFrame}
      {flags : ScriptFlags} {ctx : TxContext} {finalStack finalAlt : Stack}
      {selectedResources : ExecutionResources}
      (split : splitConditional script = some frame)
      (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (selected : EvalResources (frame.select (castToBool top)) rest altStack
        flags ctx finalStack finalAlt selectedResources) :
      EvalResources (.op .OP_IF :: script) (top :: rest) altStack flags ctx
        finalStack finalAlt
        (ExecutionResources.prepend (top :: rest) altStack 0 selectedResources)
  | notif_execute {top : StackElement} {rest altStack : Stack}
      {script : Script} {frame : ConditionalFrame}
      {flags : ScriptFlags} {ctx : TxContext} {finalStack finalAlt : Stack}
      {selectedResources : ExecutionResources}
      (split : splitConditional script = some frame)
      (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (selected : EvalResources (frame.select (!castToBool top)) rest altStack
        flags ctx finalStack finalAlt selectedResources) :
      EvalResources (.op .OP_NOTIF :: script) (top :: rest) altStack flags ctx
        finalStack finalAlt
        (ExecutionResources.prepend (top :: rest) altStack 0 selectedResources)

namespace EvalResources

/-- Erasing resource observations recovers the existing successful semantics. -/
theorem toEval
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources) :
    Eval script stack altStack flags ctx (.success finalStack finalAlt) := by
  induction observed with
  | empty => exact .empty _ _ _ _
  | step head tail ih => simpa using Eval.append head ih
  | if_execute split minimal selected ih =>
      exact .if_execute _ _ _ _ _ _ _ _ split minimal ih
  | notif_execute split minimal selected ih =>
      exact .notif_execute _ _ _ _ _ _ _ _ split minimal ih

/-- Every successful big-step evaluation has an active-path resource
    observation. -/
theorem exists_of_eval_success
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval script stack altStack flags ctx
      (.success finalStack finalAlt)) :
    ∃ resources, EvalResources script stack altStack flags ctx
      finalStack finalAlt resources := by
  generalize resultEq : ExecResult.success finalStack finalAlt = result at evaluated
  induction evaluated
  case empty =>
    cases resultEq
    exact ⟨_, EvalResources.empty _ _ _ _⟩
  case if_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  case notif_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  case if_execute =>
    cases resultEq
    rename_i top rest altStack script frame flags ctx split minimal selected ih
    rcases ih rfl with ⟨resources, observed⟩
    exact ⟨_, EvalResources.if_execute split minimal observed⟩
  case notif_execute =>
    cases resultEq
    rename_i top rest altStack script frame flags ctx split minimal selected ih
    rcases ih rfl with ⟨resources, observed⟩
    exact ⟨_, EvalResources.notif_execute split minimal observed⟩
  all_goals cases resultEq <;> try simp_all
  all_goals
    obtain ⟨resources, observed⟩ :=
      ‹∃ resources, EvalResources _ _ _ _ _ _ _ resources›
    refine ⟨_, EvalResources.step ?_ observed⟩
    grind [Eval]

/-- The initial state is included in every peak observation. -/
theorem initial_le_peak
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources) :
    stack.length + altStack.length ≤ resources.peakStackItems := by
  cases observed with
  | empty => simp [ExecutionResources.initial]
  | step => exact Nat.le_max_left _ _
  | if_execute => exact Nat.le_max_left _ _
  | notif_execute => exact Nat.le_max_left _ _

/-- Stack sizes appearing recursively along an observed active execution path. -/
inductive StackSizeSeen :
    ∀ {script : Script} {stack altStack finalStack finalAlt : Stack}
      {flags : ScriptFlags} {ctx : TxContext}
      {resources : ExecutionResources},
    EvalResources script stack altStack flags ctx finalStack finalAlt resources →
    Nat → Prop where
  | initial {script : Script} {stack altStack finalStack finalAlt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
      (observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources) :
      StackSizeSeen observed (stack.length + altStack.length)
  | step_tail {element : ScriptElement} {rest : Script}
      {stack altStack nextStack nextAlt finalStack finalAlt : Stack}
      {flags : ScriptFlags} {ctx : TxContext}
      {tailResources : ExecutionResources} {size : Nat}
      (head : Eval [element] stack altStack flags ctx (.success nextStack nextAlt))
      (tail : EvalResources rest nextStack nextAlt flags ctx
        finalStack finalAlt tailResources)
      (seen : StackSizeSeen tail size) :
      StackSizeSeen (EvalResources.step head tail) size
  | if_selected {top : StackElement} {rest altStack finalStack finalAlt : Stack}
      {script : Script} {frame : ConditionalFrame}
      {flags : ScriptFlags} {ctx : TxContext}
      {selectedResources : ExecutionResources} {size : Nat}
      (split : splitConditional script = some frame)
      (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (selected : EvalResources (frame.select (castToBool top)) rest altStack
        flags ctx finalStack finalAlt selectedResources)
      (seen : StackSizeSeen selected size) :
      StackSizeSeen (EvalResources.if_execute split minimal selected) size
  | notif_selected {top : StackElement} {rest altStack finalStack finalAlt : Stack}
      {script : Script} {frame : ConditionalFrame}
      {flags : ScriptFlags} {ctx : TxContext}
      {selectedResources : ExecutionResources} {size : Nat}
      (split : splitConditional script = some frame)
      (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (selected : EvalResources (frame.select (!castToBool top)) rest altStack
        flags ctx finalStack finalAlt selectedResources)
      (seen : StackSizeSeen selected size) :
      StackSizeSeen (EvalResources.notif_execute split minimal selected) size

/-- Every initial, intermediate, and final combined stack size on the active
    path is bounded by the recorded peak. -/
theorem StackSizeSeen.le_peak
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {resources : ExecutionResources}
    {observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources} {size : Nat}
    (seen : StackSizeSeen observed size) :
    size ≤ resources.peakStackItems := by
  induction seen with
  | initial observed => exact observed.initial_le_peak
  | step_tail head tail seen ih =>
      exact Nat.le_trans ih (Nat.le_max_right _ _)
  | if_selected split minimal selected seen ih =>
      exact Nat.le_trans ih (Nat.le_max_right _ _)
  | notif_selected split minimal selected seen ih =>
      exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- The final state is one of the recursively observed states. -/
theorem final_seen
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources) :
    StackSizeSeen observed (finalStack.length + finalAlt.length) := by
  induction observed with
  | empty => exact .initial _
  | step head tail ih => exact .step_tail head tail ih
  | if_execute split minimal selected ih => exact .if_selected split minimal selected ih
  | notif_execute split minimal selected ih => exact .notif_selected split minimal selected ih

/-- The final combined stack size is bounded by the observed peak. -/
theorem final_le_peak
    {script : Script} {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack altStack flags ctx
      finalStack finalAlt resources) :
    finalStack.length + finalAlt.length ≤ resources.peakStackItems :=
  observed.final_seen.le_peak

/-- Resource observations compose over successful sequential execution. -/
theorem append
    {left right : Script} {stack midStack altStack midAltStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {leftResources rightResources : ExecutionResources}
    (leftObserved : EvalResources left stack altStack flags ctx
      midStack midAltStack leftResources)
    (rightObserved : EvalResources right midStack midAltStack flags ctx
      finalStack finalAlt rightResources) :
    EvalResources (left ++ right) stack altStack flags ctx finalStack finalAlt
      (ExecutionResources.seq leftResources rightResources) := by
  induction leftObserved generalizing right finalStack finalAlt rightResources with
  | empty stack altStack flags ctx =>
      have initial := rightObserved.initial_le_peak
      simpa [ExecutionResources.seq, ExecutionResources.initial,
        Nat.max_eq_right initial] using rightObserved
  | step head tail ih =>
      simpa [ExecutionResources.seq, ExecutionResources.prepend,
        Nat.max_assoc, Nat.add_assoc] using
        EvalResources.step head (ih rightObserved)
  | if_execute split minimal selected ih =>
      rename_i top rest altStack script frame flags ctx midStack midAlt
        selectedResources
      have splitAppended := splitConditional_append_of_some
        (suffix := right) split
      have selectedAppended := ih rightObserved
      rw [← ConditionalFrame.select_append] at selectedAppended
      simpa [ExecutionResources.seq, ExecutionResources.prepend,
        Nat.max_assoc, Nat.add_assoc] using
        EvalResources.if_execute splitAppended minimal selectedAppended
  | notif_execute split minimal selected ih =>
      rename_i top rest altStack script frame flags ctx midStack midAlt
        selectedResources
      have splitAppended := splitConditional_append_of_some
        (suffix := right) split
      have selectedAppended := ih rightObserved
      rw [← ConditionalFrame.select_append] at selectedAppended
      simpa [ExecutionResources.seq, ExecutionResources.prepend,
        Nat.max_assoc, Nat.add_assoc] using
        EvalResources.notif_execute splitAppended minimal selectedAppended

end EvalResources

end LeanMiniscript.Script
