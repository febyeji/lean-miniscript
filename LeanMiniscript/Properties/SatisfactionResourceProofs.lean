import LeanMiniscript.Miniscript.CompileVerifyResourceProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Properties.ExecutionResourceFrameProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Resource-aware generated satisfaction contracts

This layer keeps the exact generated execution facts together with a concrete
stack-path summary, a dynamic legacy-multisignature charge, and an observed
resource frame.  The selected stack and opcode summaries always describe the
same satisfaction or dissatisfaction path.
-/

/-- Select the public stack summary for one generated truth value. -/
def selectedStackSummary (fragment : CoreFragment) (expected : Bool) :
    StackTraceSet :=
  if expected then (stackPathBounds fragment).sat
  else (stackPathBounds fragment).dsat

/-- Select the public dynamic opcode summary for one generated truth value. -/
def selectedOpSummary (fragment : CoreFragment) (expected : Bool) :
    PathMaximum :=
  if expected then (opPathBounds fragment).sat
  else (opPathBounds fragment).dsat

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
  constructor
  · have extended := Int.add_le_add_right selected.netDiff_le 1
    simpa [StackTraceBound.sequential, StackTraceBound.branch,
      Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using extended
  · intro rest altStack
    obtain ⟨resources, observed, peak, charge⟩ := selected.run rest altStack
    refine ⟨_, EvalResources.if_execute split minimal observed, ?_, ?_⟩
    · simp only [ExecutionResources.prepend_peakStackItems]
      by_cases order :
          (selector :: List.append inputs rest).length + altStack.length ≤
            resources.peakStackItems
      · rw [Nat.max_eq_right order]
        have traceLe := Int.le_max_left trace.exec
          (trace.netDiff + StackTraceBound.branch.exec)
        simp only [StackTraceBound.branch] at traceLe
        simp [List.length_append, StackTraceBound.sequential,
          StackTraceBound.branch, Int.natCast_add, Int.add_assoc,
          Int.add_comm] at peak ⊢
        omega
      · rw [Nat.max_eq_left (Nat.le_of_not_ge order)]
        have net := selected.netDiff_le
        have traceLe := Int.le_max_right trace.exec
          (trace.netDiff + StackTraceBound.branch.exec)
        simp only [StackTraceBound.branch] at traceLe
        simp [List.length_cons, List.length_append,
          StackTraceBound.sequential, StackTraceBound.branch,
          Int.natCast_add, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] at net ⊢
        omega
    · simpa [executedMultiSigKeyCharge] using charge

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
  constructor
  · have extended := Int.add_le_add_right selected.netDiff_le 1
    simpa [StackTraceBound.sequential, StackTraceBound.branch,
      Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using extended
  · intro rest altStack
    obtain ⟨resources, observed, peak, charge⟩ := selected.run rest altStack
    refine ⟨_, EvalResources.notif_execute split minimal observed, ?_, ?_⟩
    · simp only [ExecutionResources.prepend_peakStackItems]
      by_cases order :
          (selector :: List.append inputs rest).length + altStack.length ≤
            resources.peakStackItems
      · rw [Nat.max_eq_right order]
        have traceLe := Int.le_max_left trace.exec
          (trace.netDiff + StackTraceBound.branch.exec)
        simp only [StackTraceBound.branch] at traceLe
        simp [List.length_append, StackTraceBound.sequential,
          StackTraceBound.branch, Int.natCast_add, Int.add_assoc,
          Int.add_comm] at peak ⊢
        omega
      · rw [Nat.max_eq_left (Nat.le_of_not_ge order)]
        have net := selected.netDiff_le
        have traceLe := Int.le_max_right trace.exec
          (trace.netDiff + StackTraceBound.branch.exec)
        simp only [StackTraceBound.branch] at traceLe
        simp [List.length_cons, List.length_append,
          StackTraceBound.sequential, StackTraceBound.branch,
          Int.natCast_add, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] at net ⊢
        omega
    · simpa [executedMultiSigKeyCharge] using charge

end ExecutesResourceFrame

private theorem verifyResourceFrame
    (operand : StackElement) (flags : ScriptFlags) (ctx : TxContext)
    (truth : castToBool operand = true) :
    ExecutesResourceFrame [.op .OP_VERIFY] [operand] [] flags ctx
      StackTraceBound.verify 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.verifyTrue truth Eval.done
  · simp [StackTraceBound.verify]
  · simp [StackTraceBound.verify]
  · simp [StackTraceBound.verify]
  · intro rest
    simp [executedMultiSigKeyCharge]

private theorem checkSigResourceFrame
    (key signature : StackElement) (valid : Bool)
    (flags : ScriptFlags) (ctx : TxContext)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok valid) :
    ExecutesResourceFrame [.op .OP_CHECKSIG] [key, signature]
      [boolToElement valid] flags ctx StackTraceBound.checkSig 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases valid with
    | false =>
        simpa [boolToElement] using
          (Eval.checksigFalse checked Eval.done)
    | true =>
        simpa [boolToElement] using
          (Eval.checksigTrue checked Eval.done)
  · simp [StackTraceBound.checkSig]
  · simp [StackTraceBound.checkSig]
  · simp [StackTraceBound.checkSig]
  · intro rest
    simp [executedMultiSigKeyCharge]

private theorem aResourceFrame
    {script : Script} {inputs : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (child : ExecutesResourceFrame script inputs [result] flags ctx
      trace dynamic) (saved : StackElement) :
    ExecutesResourceFrame
      ([.op .OP_TOALTSTACK] ++ script ++ [.op .OP_FROMALTSTACK])
      (saved :: inputs) [saved, result] flags ctx trace dynamic := by
  constructor
  · have extended := Int.add_le_add_right child.netDiff_le 1
    simpa [Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using extended
  · intro rest altStack
    obtain ⟨childResources, childObserved, childPeak, childCharge⟩ :=
      child.run rest (saved :: altStack)
    have move : Eval [.op .OP_TOALTSTACK] (saved :: inputs ++ rest) altStack
        flags ctx (.success (inputs ++ rest) (saved :: altStack)) := by
      exact Eval.toAltStackNext Eval.done
    have restore : Eval [.op .OP_FROMALTSTACK]
        (result :: rest) (saved :: altStack) flags ctx
        (.success (saved :: result :: rest) altStack) := by
      exact Eval.fromAltStackNext Eval.done
    have restoreObserved := EvalResources.step restore
      (EvalResources.empty (saved :: result :: rest) altStack flags ctx)
    have bodyObserved := EvalResources.append childObserved restoreObserved
    have complete := EvalResources.step move bodyObserved
    refine ⟨_, complete, ?_, ?_⟩
    · have initialChild := childObserved.initial_le_peak
      have finalChild := childObserved.final_le_peak
      have childPeak' :
          Int.ofNat childResources.peakStackItems ≤
            Int.ofNat (([saved, result] ++ rest).length + altStack.length) +
              trace.exec := by
        simpa [List.length_append, Int.natCast_add, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using childPeak
      apply Int.le_trans (b := Int.ofNat childResources.peakStackItems)
      · apply Int.ofNat_le.mpr
        simp only [ExecutionResources.prepend_peakStackItems,
          ExecutionResources.seq_peakStackItems,
          ExecutionResources.initial_peakStackItems]
        refine Nat.max_le.mpr ⟨?_, ?_⟩
        · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using initialChild
        · refine Nat.max_le.mpr ⟨Nat.le_refl _, ?_⟩
          refine Nat.max_le.mpr ⟨?_, ?_⟩ <;>
            simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using finalChild
      · exact childPeak'
    · simpa [executedMultiSigKeyCharge] using childCharge

private theorem sResourceFrame
    {script : Script} {argument result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    {trace : StackTraceBound} {dynamic : Nat}
    (child : ExecutesResourceFrame script [argument] [result] flags ctx
      trace dynamic) (saved : StackElement) :
    ExecutesResourceFrame ([.op .OP_SWAP] ++ script)
      [saved, argument] [result, saved] flags ctx trace dynamic := by
  constructor
  · have extended := Int.add_le_add_right child.netDiff_le 1
    simpa [Int.natCast_add, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using extended
  · intro rest altStack
    obtain ⟨childResources, childObserved, childPeak, childCharge⟩ :=
      child.run (saved :: rest) altStack
    have swap : Eval [.op .OP_SWAP] (saved :: argument :: rest) altStack
        flags ctx (.success (argument :: saved :: rest) altStack) := by
      exact Eval.swap saved argument rest altStack [] flags ctx _ Eval.done
    have complete := EvalResources.step swap childObserved
    refine ⟨_, complete, ?_, ?_⟩
    · have initialChild := childObserved.initial_le_peak
      simp only [ExecutionResources.prepend_peakStackItems]
      rw [Nat.max_eq_right (by simpa using initialChild)]
      simpa [List.length_append, Int.natCast_add, Int.add_assoc,
        Int.add_left_comm, Int.add_comm] using childPeak
    · simpa [executedMultiSigKeyCharge] using childCharge

/-- Strong generated execution together with one jointly selected resource
    path.  The four constructors expose the exact output frame associated with
    the Miniscript base type. -/
inductive GeneratedResourceContract (fragment : CoreFragment)
    (witness : Witness) (expected : Bool) (flags : ScriptFlags)
    (txCtx : TxContext) : MiniType → Prop where
  | b {mods : CorrectnessModifiers} {result : StackElement} {value : Int}
      {trace : StackTraceBound} {dynamic : Nat}
      (input : GeneratedInput witness expected mods)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : BExecution fragment witness.toInitialStack result flags txCtx)
      (resources : ExecutesResourceFrame (compile fragment)
        witness.toInitialStack [result] flags txCtx trace dynamic)
      (stackSelected : selectedStackSummary fragment expected = some trace)
      (opSelected : selectedOpSummary fragment expected = some dynamic) :
      GeneratedResourceContract fragment witness expected flags txCtx
        ⟨.B, mods⟩
  | v {mods : CorrectnessModifiers} {trace : StackTraceBound} {dynamic : Nat}
      (input : GeneratedInput witness expected mods)
      (expectedTrue : expected = true)
      (executed : VExecution fragment witness.toInitialStack flags txCtx)
      (resources : ExecutesResourceFrame (compile fragment)
        witness.toInitialStack [] flags txCtx trace dynamic)
      (stackSelected : selectedStackSummary fragment expected = some trace)
      (opSelected : selectedOpSummary fragment expected = some dynamic) :
      GeneratedResourceContract fragment witness expected flags txCtx
        ⟨.V, mods⟩
  | k {mods : CorrectnessModifiers} {trace : StackTraceBound} {dynamic : Nat}
      (input : GeneratedInput witness expected mods)
      (ownArgs : Stack) (key signature : StackElement)
      (stackShape : witness.toInitialStack = ownArgs ++ [signature])
      (executed : KExecution fragment ownArgs key flags txCtx)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
        signature key = .ok expected)
      (resources : ExecutesResourceFrame (compile fragment)
        witness.toInitialStack [key, signature] flags txCtx trace dynamic)
      (stackSelected : selectedStackSummary fragment expected = some trace)
      (opSelected : selectedOpSummary fragment expected = some dynamic) :
      GeneratedResourceContract fragment witness expected flags txCtx
        ⟨.K, mods⟩
  | w {mods : CorrectnessModifiers} {result : StackElement} {value : Int}
      {trace : StackTraceBound} {dynamic : Nat}
      (input : GeneratedInput witness expected mods)
      (order : WStackOrder)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : WExecution fragment witness.toInitialStack result order
        flags txCtx)
      (resources : ∀ saved, ExecutesResourceFrame (compile fragment)
        (saved :: witness.toInitialStack) (order.outputs saved result)
        flags txCtx trace dynamic)
      (stackSelected : selectedStackSummary fragment expected = some trace)
      (opSelected : selectedOpSummary fragment expected = some dynamic) :
      GeneratedResourceContract fragment witness expected flags txCtx
        ⟨.W, mods⟩

namespace GeneratedResourceContract

/-- Erasing resource evidence recovers the existing generated contract. -/
theorem toGeneratedContract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {ty : MiniType}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx ty) :
    GeneratedContract fragment witness expected flags txCtx ty := by
  cases contract with
  | b input facts executed => exact .b input facts executed
  | v input expectedTrue executed => exact .v input expectedTrue executed
  | k input ownArgs key signature stackShape executed checked =>
      exact .k input ownArgs key signature stackShape executed checked
  | w input order facts executed => exact .w input order facts executed

end GeneratedResourceContract

private theorem generatedResourceB_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {sourceResult : StackElement} {trace : StackTraceBound} {dynamic : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.B, mods⟩)
    (resources : ExecutesResourceFrame (compile fragment)
      witness.toInitialStack [sourceResult] flags txCtx trace dynamic)
    (stackSelected : selectedStackSummary fragment expected = some trace)
    (opSelected : selectedOpSummary fragment expected = some dynamic) :
    GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.B, mods⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b input facts executed (resources.alignOutputs executed)
        stackSelected opSelected

private theorem generatedResourceV_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {trace : StackTraceBound} {dynamic : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.V, mods⟩)
    (resources : ExecutesResourceFrame (compile fragment)
      witness.toInitialStack [] flags txCtx trace dynamic)
    (stackSelected : selectedStackSummary fragment expected = some trace)
    (opSelected : selectedOpSummary fragment expected = some dynamic) :
    GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.V, mods⟩ := by
  cases contract with
  | v input expectedTrue executed =>
      exact .v input expectedTrue executed resources stackSelected opSelected

private theorem generatedResourceK_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {sourceOutputs : Stack} {trace : StackTraceBound} {dynamic : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.K, mods⟩)
    (resources : ExecutesResourceFrame (compile fragment)
      witness.toInitialStack sourceOutputs flags txCtx trace dynamic)
    (stackSelected : selectedStackSummary fragment expected = some trace)
    (opSelected : selectedOpSummary fragment expected = some dynamic) :
    GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.K, mods⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      have target : ExecutesStackFrame (compile fragment)
          witness.toInitialStack [key, signature] flags txCtx := by
        rw [stackShape]
        simpa using executed.withSuffix (suffix := [signature])
      exact .k input ownArgs key signature stackShape executed checked
        (resources.alignOutputs target) stackSelected opSelected

private theorem generatedResourceW_of_contract
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {sourceOutputs : StackElement → Stack}
    {trace : StackTraceBound} {dynamic : Nat}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.W, mods⟩)
    (resources : ∀ saved, ExecutesResourceFrame (compile fragment)
      (saved :: witness.toInitialStack) (sourceOutputs saved)
      flags txCtx trace dynamic)
    (stackSelected : selectedStackSummary fragment expected = some trace)
    (opSelected : selectedOpSummary fragment expected = some dynamic) :
    GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.W, mods⟩ := by
  cases contract with
  | w input order facts executed =>
      exact .w input order facts executed
        (fun saved => (resources saved).alignOutputs (executed saved))
        stackSelected opSelected

namespace GeneratedResourceContract

/-- Resource-aware sequential composition for `and_v`. -/
theorem andV
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods : CorrectnessModifiers}
    {secondType : MiniType} {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedResourceContract first firstWitness true flags
      txCtx ⟨.V, firstMods⟩)
    (secondContract : GeneratedResourceContract second secondWitness expected
      flags txCtx secondType)
    (branch : branchBase secondType.base) :
    GeneratedResourceContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨secondType.base, {
        z := firstMods.z && secondType.mods.z
        o := (firstMods.z && secondType.mods.o) ||
          (firstMods.o && secondType.mods.z)
        n := firstMods.n || (firstMods.z && secondType.mods.n)
        u := secondType.mods.u }⟩ := by
  cases firstContract with
  | @v _ firstTrace firstDynamic firstInput firstTrue firstExecuted
      firstResources firstStack firstOps =>
    cases secondType with
    | mk secondBase secondMods =>
      cases secondBase with
      | B =>
        cases secondContract with
        | @b _ result value secondTrace secondDynamic secondInput secondFacts
            secondExecuted secondResources secondStack secondOps =>
          have frame :=
            (firstResources.withSuffix
              (suffix := secondWitness.toInitialStack)).append secondResources
          refine generatedResourceB_of_contract
            (sourceResult := result)
            (trace := firstTrace.sequential secondTrace)
            (dynamic := firstDynamic + secondDynamic)
            ((GeneratedContract.v firstInput firstTrue firstExecuted).andV_b
              (GeneratedContract.b secondInput secondFacts secondExecuted)) ?_ ?_ ?_
          · simpa [compile, compileWithKeyHash,
              Witness.toInitialStack_combine] using frame
          · cases expected <;>
              simp [selectedStackSummary] at firstStack secondStack ⊢ <;>
              simp [stackPathBounds, firstStack, secondStack,
                StackTraceSet.sequential]
          · cases expected <;>
              simp [selectedOpSummary] at firstOps secondOps ⊢ <;>
              simp [opPathBounds, firstOps, secondOps, PathMaximum.sequential]
      | V =>
        cases secondContract with
        | @v _ secondTrace secondDynamic secondInput secondTrue secondExecuted
            secondResources secondStack secondOps =>
          have frame :=
            (firstResources.withSuffix
              (suffix := secondWitness.toInitialStack)).append secondResources
          refine generatedResourceV_of_contract
            (trace := firstTrace.sequential secondTrace)
            (dynamic := firstDynamic + secondDynamic)
            ((GeneratedContract.v firstInput firstTrue firstExecuted).andV_v
              (GeneratedContract.v secondInput secondTrue secondExecuted)) ?_ ?_ ?_
          · simpa [compile, compileWithKeyHash,
              Witness.toInitialStack_combine] using frame
          · cases expected <;>
              simp [selectedStackSummary] at firstStack secondStack ⊢ <;>
              simp [stackPathBounds, firstStack, secondStack,
                StackTraceSet.sequential]
          · cases expected <;>
              simp [selectedOpSummary] at firstOps secondOps ⊢ <;>
              simp [opPathBounds, firstOps, secondOps, PathMaximum.sequential]
      | K =>
        cases secondContract with
        | @k _ secondTrace secondDynamic secondInput ownArgs key signature
            stackShape secondExecuted checked secondResources secondStack
            secondOps =>
          have frame :=
            (firstResources.withSuffix
              (suffix := secondWitness.toInitialStack)).append secondResources
          refine generatedResourceK_of_contract
            (sourceOutputs := [key, signature])
            (trace := firstTrace.sequential secondTrace)
            (dynamic := firstDynamic + secondDynamic)
            ((GeneratedContract.v firstInput firstTrue firstExecuted).andV_k
              (GeneratedContract.k secondInput ownArgs key signature stackShape
                secondExecuted checked)) ?_ ?_ ?_
          · simpa [compile, compileWithKeyHash,
              Witness.toInitialStack_combine] using frame
          · cases expected <;>
              simp [selectedStackSummary] at firstStack secondStack ⊢ <;>
              simp [stackPathBounds, firstStack, secondStack,
                StackTraceSet.sequential]
          · cases expected <;>
              simp [selectedOpSummary] at firstOps secondOps ⊢ <;>
              simp [opPathBounds, firstOps, secondOps, PathMaximum.sequential]
      | W => simp [branchBase] at branch

/-- Resource-aware normalization wrapper. -/
theorem n
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) :
    GeneratedResourceContract (.n fragment) witness expected flags txCtx
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    have suffix := ExecutesResourceFrame.zeroNotEqual result value flags txCtx
      facts.decoded
    have combined := resources.append suffix
    have bounded : ExecutesResourceFrame
        (compile fragment ++ [.op .OP_0NOTEQUAL]) witness.toInitialStack
        [boolToElement (value != 0)] flags txCtx trace dynamic := by
      apply combined.mono
      · simp [StackTraceBound.sequential, StackTraceBound.zeroNotEqual]
      · simp [StackTraceBound.sequential, StackTraceBound.zeroNotEqual,
          Int.max_eq_right resources.exec_nonneg]
      · simp
    have normalized : ExecutesResourceFrame (compile (.n fragment))
        witness.toInitialStack [boolToElement (value != 0)] flags txCtx
        trace dynamic := by
      simpa [compile, compileWithKeyHash] using bounded
    apply generatedResourceB_of_contract
      ((GeneratedContract.b input facts executed).n) normalized
    · cases expected <;>
        simpa [selectedStackSummary, stackPathBounds] using stackSelected
    · cases expected <;>
        simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware VERIFY wrapper for a satisfying B contract. -/
theorem verify
    {fragment : CoreFragment} {witness : Witness}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness true flags txCtx
      ⟨.B, mods⟩) :
    GeneratedResourceContract (.v fragment) witness true flags txCtx
      ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    have suffix := verifyResourceFrame result flags txCtx facts.truth
    have unfused := resources.append suffix
    have optimized := ExecutesResourceFrame.compileVerify
      (compile_balancedControlFlow fragment) unfused
    have normalized : ExecutesResourceFrame (compile (.v fragment))
        witness.toInitialStack [] flags txCtx
        (trace.sequential StackTraceBound.verify) dynamic := by
      simpa [compile, compileWithKeyHash] using optimized
    apply generatedResourceV_of_contract
      ((GeneratedContract.b input facts executed).verify) normalized
    · simpa [selectedStackSummary, stackPathBounds,
        StackTraceSet.sequential] using congrArg
        (fun summary => StackTraceSet.sequential summary
          (some StackTraceBound.verify)) stackSelected
    · simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware CHECKSIG wrapper. -/
theorem c
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.K, mods⟩) :
    GeneratedResourceContract (.c fragment) witness expected flags txCtx
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | @k _ trace dynamic input ownArgs key signature stackShape executed checked
      resources stackSelected opSelected =>
    have suffix := checkSigResourceFrame key signature expected flags txCtx checked
    have combined := resources.append suffix
    have normalized : ExecutesResourceFrame (compile (.c fragment))
        witness.toInitialStack [boolToElement expected] flags txCtx
        (trace.sequential StackTraceBound.checkSig) dynamic := by
      simpa [compile, compileWithKeyHash] using combined
    apply generatedResourceB_of_contract
      ((GeneratedContract.k input ownArgs key signature stackShape executed
        checked).c) normalized
    · cases expected <;>
        simpa [selectedStackSummary, stackPathBounds,
          StackTraceSet.sequential] using congrArg
            (fun summary => StackTraceSet.sequential summary
              (some StackTraceBound.checkSig)) stackSelected
    · cases expected <;>
        simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware alternate-stack wrapper. -/
theorem a
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) :
    GeneratedResourceContract (.a fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    have wrapped : ∀ saved, ExecutesResourceFrame (compile (.a fragment))
        (saved :: witness.toInitialStack) [saved, result] flags txCtx
        trace dynamic := by
      intro saved
      simpa [compile, compileWithKeyHash] using aResourceFrame resources saved
    apply generatedResourceW_of_contract
      ((GeneratedContract.b input facts executed).a) wrapped
    · cases expected <;>
        simpa [selectedStackSummary, stackPathBounds] using stackSelected
    · cases expected <;>
        simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware swap wrapper. -/
theorem s
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) (oneArg : mods.o = true) :
    GeneratedResourceContract (.s fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    obtain ⟨argument, shape⟩ := input.oneArg oneArg
    have child : ExecutesResourceFrame (compile fragment) [argument] [result]
        flags txCtx trace dynamic := by simpa [shape] using resources
    have wrapped : ∀ saved, ExecutesResourceFrame (compile (.s fragment))
        (saved :: witness.toInitialStack) [result, saved] flags txCtx
        trace dynamic := by
      intro saved
      simpa [compile, compileWithKeyHash, shape] using
        sResourceFrame child saved
    apply generatedResourceW_of_contract
      ((GeneratedContract.b input facts executed).s oneArg) wrapped
    · cases expected <;>
        simpa [selectedStackSummary, stackPathBounds] using stackSelected
    · cases expected <;>
        simpa [selectedOpSummary, opPathBounds] using opSelected

end GeneratedResourceContract

/-- Candidate-wide support for jointly selected generated resource paths. -/
structure CandidatePair.SupportsGeneratedResources (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports fun witness =>
    GeneratedResourceContract fragment witness true flags txCtx ty
  dsat : pair.dsat.Supports fun witness =>
    GeneratedResourceContract fragment witness false flags txCtx ty

/-- Resource-aware generated support aligned with source-order threshold
    children. -/
inductive SupportsGeneratedResourcesList (scriptCtx : ScriptContext)
    (flags : ScriptFlags) (txCtx : TxContext) :
    List CandidatePair → List CoreFragment → List MiniType → Prop where
  | nil : SupportsGeneratedResourcesList scriptCtx flags txCtx [] [] []
  | snoc {pairs : List CandidatePair} {fragments : List CoreFragment}
      {types : List MiniType} {pair : CandidatePair} {fragment : CoreFragment}
      {ty : MiniType}
      (prior : SupportsGeneratedResourcesList scriptCtx flags txCtx
        pairs fragments types)
      (child : CandidatePair.SupportsGeneratedResources pair scriptCtx fragment
        ty flags txCtx) :
      SupportsGeneratedResourcesList scriptCtx flags txCtx
        (pairs ++ [pair]) (fragments ++ [fragment]) (types ++ [ty])

namespace SupportsGeneratedResourcesList

/-- Empty candidate support has empty aligned fragment and type rows. -/
theorem nil_inv
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedResourcesList scriptCtx flags txCtx
      [] fragments types) : fragments = [] ∧ types = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at supported
  cases supported with
  | nil => exact ⟨rfl, rfl⟩
  | snoc prior child => simp at pairsEq

/-- Invert the final source child of aligned resource support. -/
theorem snoc_inv
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {pair : CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedResourcesList scriptCtx flags txCtx
      (pairs ++ [pair]) fragments types) :
    ∃ priorFragments priorTypes fragment ty,
      fragments = priorFragments ++ [fragment] ∧
      types = priorTypes ++ [ty] ∧
      SupportsGeneratedResourcesList scriptCtx flags txCtx
        pairs priorFragments priorTypes ∧
      CandidatePair.SupportsGeneratedResources pair scriptCtx fragment ty
        flags txCtx := by
  generalize pairsEq : pairs ++ [pair] = allPairs at supported
  cases supported with
  | nil => simp at pairsEq
  | @snoc otherPairs otherFragments otherTypes otherPair fragment ty prior child =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherFragments, otherTypes, fragment, ty, rfl, rfl, prior, child⟩

/-- Resource list support retains pointwise typing. -/
theorem typed
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType}
    (supported : SupportsGeneratedResourcesList scriptCtx flags txCtx
      pairs fragments types) : HasTypeList scriptCtx fragments types := by
  induction supported with
  | nil => exact .nil
  | snoc prior child ih => exact ih.snoc child.typed

/-- Prepend one resource-supported child. -/
theorem cons
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {pair : CandidatePair} {fragment : CoreFragment}
    {ty : MiniType}
    (child : CandidatePair.SupportsGeneratedResources pair scriptCtx fragment
      ty flags txCtx)
    (rest : SupportsGeneratedResourcesList scriptCtx flags txCtx
      pairs fragments types) :
    SupportsGeneratedResourcesList scriptCtx flags txCtx
      (pair :: pairs) (fragment :: fragments) (ty :: types) := by
  induction rest with
  | nil => exact .snoc .nil child
  | snoc prior last ih => exact .snoc ih last

end SupportsGeneratedResourcesList

namespace CandidatePair.SupportsGeneratedResources

/-- Erasing resource evidence recovers the existing candidate-wide generated
    contract. -/
theorem toSupportsGeneratedContract
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {ty : MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ty flags txCtx) :
    pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx :=
  ⟨supported.typed,
    fun witness selected => (supported.sat witness selected).toGeneratedContract,
    fun witness selected => (supported.dsat witness selected).toGeneratedContract⟩

/-- Project a resource-aware satisfaction contract through `satisfy`. -/
theorem satisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : satisfy fragment env = some witness) :
    GeneratedResourceContract fragment witness true flags env.txCtx ty :=
  supported.sat witness generated

/-- Project a resource-aware dissatisfaction contract through `dissatisfy`. -/
theorem dissatisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : dissatisfy fragment env = some witness) :
    GeneratedResourceContract fragment witness false flags env.txCtx ty :=
  supported.dsat witness generated

/-- Candidate-wide resource support for `and_v`. -/
theorem and_v
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods : CorrectnessModifiers}
    {secondType : MiniType} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.V, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second secondType flags txCtx)
    (branch : branchBase secondType.base) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.combine secondPair.sat
         dsat := (firstPair.sat.combine secondPair.dsat).markNonCanonical } :
        CandidatePair)
      scriptCtx (.and_v first second)
      ⟨secondType.base, {
        z := firstMods.z && secondType.mods.z
        o := (firstMods.z && secondType.mods.o) ||
          (firstMods.o && secondType.mods.z)
        n := firstMods.n || (firstMods.z && secondType.mods.n)
        u := secondType.mods.u }⟩ flags txCtx := by
  refine ⟨.and_v firstSupported.typed secondSupported.typed branch,
    ?_, ?_⟩
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    exact firstContract.andV secondContract branch
  · intro witness selected
    have combined := CandidateResult.markNonCanonical_usableWitness_iff.mp selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.dsat) witness combined
    exact firstContract.andV secondContract branch

/-- Candidate-wide resource support for `n`. -/
theorem n
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources pair scriptCtx (.n fragment)
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.n_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).n,
    fun witness selected => (supported.dsat witness selected).n⟩

/-- Candidate-wide resource support for `v`. -/
theorem v
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources ({ sat := pair.sat } : CandidatePair)
      scriptCtx (.v fragment) ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩
      flags txCtx :=
  ⟨.v_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).verify,
    CandidateResult.supports_impossible _⟩

/-- Candidate-wide resource support for `c`. -/
theorem c
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.K, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources pair scriptCtx (.c fragment)
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.c_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).c,
    fun witness selected => (supported.dsat witness selected).c⟩

/-- Candidate-wide resource support for `a`. -/
theorem a
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources pair scriptCtx (.a fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.a_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).a,
    fun witness selected => (supported.dsat witness selected).a⟩

/-- Candidate-wide resource support for `s`. -/
theorem s
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) (oneArg : mods.o = true) :
    CandidatePair.SupportsGeneratedResources pair scriptCtx (.s fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.s_wrap supported.typed oneArg,
    fun witness selected => (supported.sat witness selected).s oneArg,
    fun witness selected => (supported.dsat witness selected).s oneArg⟩

end CandidatePair.SupportsGeneratedResources

theorem generatedResources_zero (scriptCtx : ScriptContext)
    (env : SatEnv) (flags : ScriptFlags) :
    CandidatePair.SupportsGeneratedResources (satisfactionCandidates .zero env)
      scriptCtx .zero ⟨.B, { z := true, d := true, u := true }⟩ flags
      env.txCtx := by
  have supported := generatedContract_zero scriptCtx env flags
  refine ⟨supported.typed, CandidateResult.supports_impossible _, ?_⟩
  intro witness selected
  have contract := supported.dsat witness selected
  cases contract with
  | b input facts executed =>
      have witnessEmpty := input.zeroArgs (by rfl)
      have resultFalse := facts.falseCanonical rfl
      apply GeneratedResourceContract.b input facts executed
      · rw [witnessEmpty, resultFalse]
        simpa [compile, compileWithKeyHash, falseElement, scriptNum_zero] using
          ExecutesResourceFrame.pushNum 0 flags env.txCtx
      · rfl
      · rfl

theorem generatedResources_one (scriptCtx : ScriptContext)
    (env : SatEnv) (flags : ScriptFlags) :
    CandidatePair.SupportsGeneratedResources (satisfactionCandidates .one env)
      scriptCtx .one ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  have supported := generatedContract_one scriptCtx env flags
  refine ⟨supported.typed, ?_, CandidateResult.supports_impossible _⟩
  intro witness selected
  have contract := supported.sat witness selected
  cases contract with
  | b input facts executed =>
      have witnessEmpty := input.zeroArgs (by rfl)
      have resultTrue := facts.unitCanonical (by rfl) rfl
      apply GeneratedResourceContract.b input facts executed
      · rw [witnessEmpty, resultTrue]
        simpa [compile, compileWithKeyHash, trueElement, scriptNum_one] using
          ExecutesResourceFrame.pushNum 1 flags env.txCtx
      · rfl
      · rfl

theorem generatedResources_pk_k
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.pk_k key))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
      (satisfactionCandidates (.pk_k key) env) scriptCtx (.pk_k key)
      ⟨.K, { o := true, n := true, d := true, u := true }⟩ flags env.txCtx := by
  have supported := generatedContract_pk_k_of_modeled wellFormed version modeled
    sound encodings
  refine ⟨supported.typed, ?_, ?_⟩
  · intro witness selected
    have contract := supported.sat witness selected
    cases contract with
    | k input ownArgs resultKey signature stackShape executed checked =>
        have explicit : Eval [.pushData key.bytes] ownArgs [] flags env.txCtx
            (.success (key.bytes :: ownArgs) []) := by
          exact Eval.pushData key.bytes [] ownArgs [] flags env.txCtx _ Eval.done
        have sameResult := Eval.result_unique (by
          simpa [KExecution, ExecutesStackFrame, compile,
            compileWithKeyHash] using executed [] []) explicit
        have stackEq : ([resultKey] : Stack) = key.bytes :: ownArgs := by
          simpa using sameResult
        have ownArgsEmpty : ownArgs = [] := by
          cases ownArgs with
          | nil => rfl
          | cons head tail => simp at stackEq
        subst ownArgs
        have resultKeyEq : resultKey = key.bytes := by simpa using stackEq
        subst resultKey
        apply GeneratedResourceContract.k input [] key.bytes signature
          stackShape executed checked
        · have frame := (ExecutesResourceFrame.pushData key.bytes flags
              env.txCtx).withSuffix
            (suffix := [signature])
          simpa [compile, compileWithKeyHash, stackShape] using frame
        · rfl
        · rfl
  · intro witness selected
    have contract := supported.dsat witness selected
    cases contract with
    | k input ownArgs resultKey signature stackShape executed checked =>
        have explicit : Eval [.pushData key.bytes] ownArgs [] flags env.txCtx
            (.success (key.bytes :: ownArgs) []) := by
          exact Eval.pushData key.bytes [] ownArgs [] flags env.txCtx _ Eval.done
        have sameResult := Eval.result_unique (by
          simpa [KExecution, ExecutesStackFrame, compile,
            compileWithKeyHash] using executed [] []) explicit
        have stackEq : ([resultKey] : Stack) = key.bytes :: ownArgs := by
          simpa using sameResult
        have ownArgsEmpty : ownArgs = [] := by
          cases ownArgs with
          | nil => rfl
          | cons head tail => simp at stackEq
        subst ownArgs
        have resultKeyEq : resultKey = key.bytes := by simpa using stackEq
        subst resultKey
        apply GeneratedResourceContract.k input [] key.bytes signature
          stackShape executed checked
        · have frame := (ExecutesResourceFrame.pushData key.bytes flags
              env.txCtx).withSuffix
            (suffix := [signature])
          simpa [compile, compileWithKeyHash, stackShape] using frame
        · rfl
        · rfl

end LeanMiniscript.Properties
