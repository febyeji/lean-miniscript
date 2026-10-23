import LeanMiniscript.Properties.ResourceBounds
import LeanMiniscript.Miniscript.CompileVerifyResourceProofs
import LeanMiniscript.Miniscript.ExecutionFrameProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

/-!
# Composable resource execution frames

`ExecutesResourceFrame` records the resource observation for replacing a fixed
top-first input frame with a fixed output frame.  The contract is uniform in
the protected main-stack suffix and alternate stack, so recursive Miniscript
executions can be composed without fixing their surrounding stack state.
-/

/-- Executing `script` replaces `inputs` with `outputs`, preserves the protected
    main-stack suffix and alternate stack, and stays within one stack trace and
    dynamic multisignature charge bound. -/
structure ExecutesResourceFrame (script : Script) (inputs outputs : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (trace : StackTraceBound)
    (dynamic : Nat) : Prop where
  /-- The trace covers the fixed frame's initial-to-final stack difference. -/
  netDiff_le :
    Int.ofNat inputs.length ≤ Int.ofNat outputs.length + trace.netDiff
  /-- Every surrounding stack state admits a resource observation within the
      trace and dynamic charge bounds. -/
  run : ∀ (rest altStack : Stack), ∃ resources,
    EvalResources script (inputs ++ rest) altStack flags ctx
      (outputs ++ rest) altStack resources ∧
    Int.ofNat resources.peakStackItems ≤
      Int.ofNat ((outputs ++ rest).length + altStack.length) + trace.exec ∧
    resources.executedMultiSigKeys ≤ dynamic

namespace ExecutesResourceFrame

/-- Determinism aligns a bounded resource frame with any exact execution of
    the same script and input frame. -/
theorem alignOutputs
    {script : Script} {inputs sourceOutputs targetOutputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (source : ExecutesResourceFrame script inputs sourceOutputs flags ctx
      trace dynamic)
    (target : ExecutesStackFrame script inputs targetOutputs flags ctx) :
    ExecutesResourceFrame script inputs targetOutputs flags ctx trace dynamic := by
  obtain ⟨resources, observed, _, _⟩ := source.run [] []
  have sameResult := Eval.result_unique observed.toEval (target [] [])
  have outputEq : sourceOutputs = targetOutputs := by simpa using sameResult
  subst targetOutputs
  exact source

/-- Terminal VERIFY fusion preserves an already established resource frame. -/
theorem compileVerify
    {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (balanced : BalancedControlFlow script)
    (executed : ExecutesResourceFrame (script ++ [.op .OP_VERIFY])
      inputs outputs flags ctx trace dynamic) :
    ExecutesResourceFrame (LeanMiniscript.Miniscript.compileVerify script)
      inputs outputs flags ctx trace dynamic := by
  refine ⟨executed.netDiff_le, ?_⟩
  intro rest altStack
  obtain ⟨resources, observed, peak, charge⟩ := executed.run rest altStack
  exact ⟨resources, EvalResources.compileVerify_success balanced observed,
    peak, charge⟩

/-- Every realizable frame trace has a nonnegative execution coordinate. -/
theorem exec_nonneg
    {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (executed : ExecutesResourceFrame script inputs outputs flags ctx
      trace dynamic) : 0 ≤ trace.exec := by
  obtain ⟨resources, observed, peak, _⟩ := executed.run [] []
  have final := observed.final_le_peak
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at peak final
  have castFinal := Int.ofNat_le.mpr final
  change Int.ofNat outputs.length ≤
    Int.ofNat resources.peakStackItems at castFinal
  change Int.ofNat resources.peakStackItems ≤
    Int.ofNat outputs.length + trace.exec at peak
  omega

/-- Lift one exact single-instruction execution into a bounded resource frame. -/
theorem single
    {element : ScriptElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (executed : ∀ rest altStack,
      Eval [element] (inputs ++ rest) altStack flags ctx
        (.success (outputs ++ rest) altStack))
    (netBound : Int.ofNat inputs.length ≤
      Int.ofNat outputs.length + trace.netDiff)
    (initialBound : Int.ofNat inputs.length ≤
      Int.ofNat outputs.length + trace.exec)
    (_finalBound : 0 ≤ trace.exec)
    (chargeBound : ∀ rest,
      executedMultiSigKeyCharge element (inputs ++ rest) flags ctx ≤ dynamic) :
    ExecutesResourceFrame [element] inputs outputs flags ctx trace dynamic := by
  constructor
  · exact netBound
  · intro rest altStack
    let tail := ExecutionResources.initial (outputs ++ rest) altStack
    let resources := ExecutionResources.prepend (inputs ++ rest) altStack
      (executedMultiSigKeyCharge element (inputs ++ rest) flags ctx) tail
      (executedSignatureWeight element (inputs ++ rest) ctx)
    refine ⟨resources, EvalResources.step (executed rest altStack)
      (EvalResources.empty (outputs ++ rest) altStack flags ctx), ?_, ?_⟩
    · simp only [resources, tail, ExecutionResources.prepend_peakStackItems,
        ExecutionResources.initial_peakStackItems]
      by_cases order : (inputs ++ rest).length + altStack.length ≤
          (outputs ++ rest).length + altStack.length
      · rw [Nat.max_eq_right order]
        simp only [List.length_append]
        omega
      · rw [Nat.max_eq_left (Nat.le_of_not_ge order)]
        have extended := Int.add_le_add_right initialBound
          (Int.ofNat (rest.length + altStack.length))
        simpa [List.length_append, Int.natCast_add, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using extended
    · simp only [resources, tail,
        ExecutionResources.prepend_executedMultiSigKeys,
        ExecutionResources.initial_executedMultiSigKeys, Nat.add_zero]
      exact chargeBound rest

/-- Lift one exact single-instruction execution into a bounded resource frame.
    The three trace side-goals default to simp over the standard trace
    definitions, and the multisignature charge defaults to the zero-charge
    simp proof, so a one-opcode frame with a standard trace only needs its
    execution premise. -/
theorem of_eval
    {element : ScriptElement} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (executed : ExecutesStackFrame [element] inputs outputs flags ctx)
    (netBound : Int.ofNat inputs.length ≤
        Int.ofNat outputs.length + trace.netDiff := by
      simp [StackTraceBound.empty, StackTraceBound.push, StackTraceBound.hash,
        StackTraceBound.nop, StackTraceBound.branch, StackTraceBound.binary,
        StackTraceBound.dup, StackTraceBound.ifdupTrue,
        StackTraceBound.ifdupFalse, StackTraceBound.equalVerify,
        StackTraceBound.equal, StackTraceBound.size, StackTraceBound.checkSig,
        StackTraceBound.zeroNotEqual, StackTraceBound.verify])
    (initialBound : Int.ofNat inputs.length ≤
        Int.ofNat outputs.length + trace.exec := by
      simp [StackTraceBound.empty, StackTraceBound.push, StackTraceBound.hash,
        StackTraceBound.nop, StackTraceBound.branch, StackTraceBound.binary,
        StackTraceBound.dup, StackTraceBound.ifdupTrue,
        StackTraceBound.ifdupFalse, StackTraceBound.equalVerify,
        StackTraceBound.equal, StackTraceBound.size, StackTraceBound.checkSig,
        StackTraceBound.zeroNotEqual, StackTraceBound.verify])
    (finalBound : 0 ≤ trace.exec := by
      simp [StackTraceBound.empty, StackTraceBound.push, StackTraceBound.hash,
        StackTraceBound.nop, StackTraceBound.branch, StackTraceBound.binary,
        StackTraceBound.dup, StackTraceBound.ifdupTrue,
        StackTraceBound.ifdupFalse, StackTraceBound.equalVerify,
        StackTraceBound.equal, StackTraceBound.size, StackTraceBound.checkSig,
        StackTraceBound.zeroNotEqual, StackTraceBound.verify])
    (chargeBound : ∀ rest,
        executedMultiSigKeyCharge element (inputs ++ rest) flags ctx ≤
          dynamic := by
      simp [executedMultiSigKeyCharge]) :
    ExecutesResourceFrame [element] inputs outputs flags ctx trace dynamic :=
  single executed netBound initialBound finalBound chargeBound

/-- Pushing a Script number has the standard one-item stack-growth frame. -/
theorem pushNum (value : Int) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.pushNum value] [] [scriptNum value] flags ctx
      StackTraceBound.push 0 :=
  of_eval fun rest altStack =>
    Eval.pushNum value [] rest altStack flags ctx _ Eval.done

/-- Pushing raw data has the standard one-item stack-growth frame. -/
theorem pushData (data : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.pushData data] [] [data] flags ctx
      StackTraceBound.push 0 :=
  of_eval fun rest altStack =>
    Eval.pushData data [] rest altStack flags ctx _ Eval.done

/-- `OP_DUP` has the standard one-item stack-growth frame. -/
theorem dup (value : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_DUP] [value] [value, value] flags ctx
      StackTraceBound.dup 0 :=
  of_eval fun rest altStack =>
    Eval.dup value rest [] altStack flags ctx _ Eval.done

/-- `OP_SIZE` preserves its input below the pushed byte length. -/
theorem size (value : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [.op .OP_SIZE] [value]
      [scriptNat value.size, value] flags ctx StackTraceBound.size 0 :=
  of_eval fun rest altStack =>
    Eval.size value rest altStack [] flags ctx _ Eval.done

/-- `OP_0NOTEQUAL` consumes one decoded number and pushes its truth value. -/
theorem zeroNotEqual
    (operand : StackElement) (value : Int) (flags : ScriptFlags)
    (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .ok value) :
    ExecutesResourceFrame [.op .OP_0NOTEQUAL] [operand]
      [boolToElement (value != 0)] flags ctx StackTraceBound.zeroNotEqual 0 :=
  of_eval fun rest altStack =>
    Eval.zeroNotEqual operand value rest altStack [] flags ctx _ decoded
      Eval.done

/-- The empty script preserves an arbitrary resource frame. -/
theorem empty (frame : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame [] frame frame flags ctx StackTraceBound.empty 0 := by
  constructor
  · simp [StackTraceBound.empty]
  · intro rest altStack
    refine ⟨ExecutionResources.initial (frame ++ rest) altStack,
      EvalResources.empty _ _ _ _, ?_, ?_⟩
    · simp [ExecutionResources.initial, StackTraceBound.empty]
    · simp [ExecutionResources.initial]

/-- Increase any of the three resource bounds of a frame. -/
theorem mono
    {script : Script} {inputs outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace upper : StackTraceBound} {dynamic upperDynamic : Nat}
    (executed : ExecutesResourceFrame script inputs outputs flags ctx
      trace dynamic)
    (netDiff_le : trace.netDiff ≤ upper.netDiff)
    (exec_le : trace.exec ≤ upper.exec)
    (dynamic_le : dynamic ≤ upperDynamic) :
    ExecutesResourceFrame script inputs outputs flags ctx upper upperDynamic := by
  constructor
  · exact Int.le_trans executed.netDiff_le
      (Int.add_le_add_left netDiff_le _)
  · intro rest altStack
    obtain ⟨resources, observed, peak, charge⟩ := executed.run rest altStack
    exact ⟨resources, observed,
      Int.le_trans peak (Int.add_le_add_left exec_le _),
      Nat.le_trans charge dynamic_le⟩

/-- Resource execution frames compose in Script source order. -/
theorem append
    {left right : Script} {inputs middle outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {leftTrace rightTrace : StackTraceBound}
    {leftDynamic rightDynamic : Nat}
    (leftExec : ExecutesResourceFrame left inputs middle flags ctx
      leftTrace leftDynamic)
    (rightExec : ExecutesResourceFrame right middle outputs flags ctx
      rightTrace rightDynamic) :
    ExecutesResourceFrame (left ++ right) inputs outputs flags ctx
      (leftTrace.sequential rightTrace) (leftDynamic + rightDynamic) := by
  constructor
  · have leftNetDiff := leftExec.netDiff_le
    have rightNetDiff := rightExec.netDiff_le
    simp only [StackTraceBound.sequential]
    omega
  · intro rest altStack
    obtain ⟨leftResources, leftObserved, leftPeak, leftCharge⟩ :=
      leftExec.run rest altStack
    obtain ⟨rightResources, rightObserved, rightPeak, rightCharge⟩ :=
      rightExec.run rest altStack
    refine ⟨ExecutionResources.seq leftResources rightResources,
      EvalResources.append leftObserved rightObserved, ?_, ?_⟩
    · simp only [ExecutionResources.seq_peakStackItems,
        StackTraceBound.sequential]
      have middleLength :
          Int.ofNat ((middle ++ rest).length + altStack.length) ≤
            Int.ofNat ((outputs ++ rest).length + altStack.length) +
              rightTrace.netDiff := by
        have extended := Int.add_le_add_right rightExec.netDiff_le
          (Int.ofNat (rest.length + altStack.length))
        simpa [List.length_append, Int.natCast_add, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using extended
      have leftBound : Int.ofNat leftResources.peakStackItems ≤
          Int.ofNat ((outputs ++ rest).length + altStack.length) +
            (rightTrace.netDiff + leftTrace.exec) := by
        omega
      by_cases peakOrder :
          leftResources.peakStackItems ≤ rightResources.peakStackItems
      · rw [Nat.max_eq_right peakOrder]
        exact Int.le_trans rightPeak
          (Int.add_le_add_left (Int.le_max_left _ _) _)
      · rw [Nat.max_eq_left (Nat.le_of_not_ge peakOrder)]
        exact Int.le_trans leftBound
          (Int.add_le_add_left (Int.le_max_right _ _) _)
    · simp only [ExecutionResources.seq_executedMultiSigKeys]
      omega

/-- Extend both sides of a resource frame by the same protected main-stack
    suffix. -/
theorem withSuffix
    {script : Script} {inputs outputs suffix : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (executed : ExecutesResourceFrame script inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame script (inputs ++ suffix) (outputs ++ suffix)
      flags ctx trace dynamic := by
  constructor
  · have extended := Int.add_le_add_right executed.netDiff_le
      (Int.ofNat suffix.length)
    simpa [List.length_append, Int.natCast_add, Int.add_assoc,
      Int.add_left_comm, Int.add_comm] using extended
  · intro rest altStack
    obtain ⟨resources, observed, peak, charge⟩ :=
      executed.run (suffix ++ rest) altStack
    refine ⟨resources, ?_, ?_, charge⟩
    · simpa [List.append_assoc] using observed
    · simpa [List.append_assoc] using peak

/-- Lift a selected branch through an entry step that consumes its selector
    and preserves its dynamic multisignature charge. -/
private theorem prependSelector
    {script selectedScript : Script} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (selected : ExecutesResourceFrame selectedScript inputs outputs flags ctx
      trace dynamic)
    (enter : ∀ rest altStack resources,
      EvalResources selectedScript (inputs ++ rest) altStack flags ctx
        (outputs ++ rest) altStack resources →
      EvalResources script ((selector :: inputs) ++ rest) altStack flags ctx
        (outputs ++ rest) altStack
        (ExecutionResources.prepend ((selector :: inputs) ++ rest) altStack 0 resources)) :
    ExecutesResourceFrame script (selector :: inputs) outputs flags ctx
      (StackTraceBound.branch.sequential trace) dynamic := by
  constructor
  · have net := selected.netDiff_le
    simp only [List.length_cons, StackTraceBound.sequential, StackTraceBound.branch,
      Int.ofNat_eq_natCast, Int.natCast_add] at net ⊢
    omega
  · intro rest altStack
    obtain ⟨resources, observed, peak, charge⟩ := selected.run rest altStack
    refine ⟨_, enter rest altStack resources observed, ?_, ?_⟩
    · have net := selected.netDiff_le
      simp only [ExecutionResources.prepend_peakStackItems,
        List.length_append, List.length_cons, StackTraceBound.sequential,
        StackTraceBound.branch, Int.ofNat_eq_natCast, Int.natCast_add] at net peak ⊢
      omega
    · simpa using charge

/-- Entering the selected `OP_IF` branch adds the selector-pop trace before
    the selected branch trace. -/
theorem ifSelected
    {script : Script} {frame : ConditionalFrame} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (split : splitConditional script = some frame)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesResourceFrame
      (frame.select (castToBool selector)) inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame (.op .OP_IF :: script) (selector :: inputs)
      outputs flags ctx (StackTraceBound.branch.sequential trace) dynamic := by
  exact prependSelector selected fun _ _ _ observed =>
    EvalResources.if_execute split minimal observed

/-- Entering the selected `OP_NOTIF` branch adds the selector-pop trace before
    the selected branch trace. -/
theorem notifSelected
    {script : Script} {frame : ConditionalFrame} {selector : StackElement}
    {inputs outputs : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (split : splitConditional script = some frame)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (selected : ExecutesResourceFrame
      (frame.select (!castToBool selector)) inputs outputs flags ctx
      trace dynamic) :
    ExecutesResourceFrame (.op .OP_NOTIF :: script) (selector :: inputs)
      outputs flags ctx (StackTraceBound.branch.sequential trace) dynamic := by
  exact prependSelector selected fun _ _ _ observed =>
    EvalResources.notif_execute split minimal observed

end ExecutesResourceFrame

end LeanMiniscript.Properties
