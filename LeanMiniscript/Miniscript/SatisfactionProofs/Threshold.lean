import LeanMiniscript.Miniscript.SatisfactionProofs.Execution

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Threshold composition -/

/-- Execution evidence for the W-type tail of a threshold. The accumulator is
    represented by its canonical Script-number bytes. Each child result is an
    exact Boolean element, while `BinaryDecoded` keeps the four-byte numeric
    premise for its following `OP_ADD` explicit. Argument frames are listed in
    source execution order. -/
inductive ThresholdTailExecution (flags : ScriptFlags) (ctx : TxContext) :
    Nat → List CoreFragment → List Stack → Nat → Prop where
  | nil (count : Nat) : ThresholdTailExecution flags ctx count [] [] count
  | cons {count total : Nat} {fragment : CoreFragment}
      {fragments : List CoreFragment} {args : Stack}
      {argumentFrames : List Stack} {truth : Bool} {order : WStackOrder}
      (executed : WExecution fragment args (boolToElement truth) order flags ctx)
      (decoded : order.BinaryDecoded flags (scriptNat count)
        (boolToElement truth) (Int.ofNat count) (Int.ofNat truth.toNat))
      (tail : ThresholdTailExecution flags ctx (count + truth.toNat)
        fragments argumentFrames total) :
      ThresholdTailExecution flags ctx count (fragment :: fragments)
        (args :: argumentFrames) total

/-- The threshold tail executes every W child followed by `OP_ADD`, preserving
    arbitrary stack suffixes and the alternate stack. -/
theorem ThresholdTailExecution.executes
    {flags : ScriptFlags} {ctx : TxContext} {count total : Nat}
    {fragments : List CoreFragment} {argumentFrames : List Stack}
    (executed : ThresholdTailExecution flags ctx count fragments
      argumentFrames total) :
    ExecutesStackFrame (compileThreshTail fragments)
      (scriptNat count :: argumentFrames.flatten) [scriptNat total] flags ctx := by
  induction executed with
  | nil count =>
      intro rest altStack
      simpa [compileThreshTail, compileThreshTailWithKeyHash,
        ExecutesStackFrame] using
        (Eval.done (stack := scriptNat count :: rest) (altStack := altStack))
  | @cons count total fragment fragments args argumentFrames truth order
      childExec decoded tail ih =>
      have added :
          ExecutesStackFrame (compile fragment ++ [.op .OP_ADD])
            (scriptNat count :: args)
            [scriptNat (count + truth.toNat)] flags ctx := by
        simpa [scriptNat] using childExec.addToSaved decoded
      have prefixFrame := added.withSuffix (suffix := argumentFrames.flatten)
      have combined := ExecutesStackFrame.append prefixFrame ih
      simpa [compile, compileThreshTail, compileThreshTailWithKeyHash,
        List.append_assoc] using combined

/-- A threshold executes its first B child, accumulates every W child result,
    then compares the final canonical accumulator bytes with the literal
    threshold bytes using `OP_EQUAL`. No numeric injectivity assumption is
    needed for the final comparison. -/
theorem BExecution.thresh
    {threshold : Nat} {first : CoreFragment} {fragments : List CoreFragment}
    {firstArgs : Stack} {argumentFrames : List Stack} {firstTruth : Bool}
    {total : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs (boolToElement firstTruth) flags ctx)
    (tailExec : ThresholdTailExecution flags ctx firstTruth.toNat fragments
      argumentFrames total) :
    BExecution (.thresh threshold (first :: fragments))
      (firstArgs ++ argumentFrames.flatten)
      (boolToElement (decide (scriptNat threshold = scriptNat total)))
      flags ctx := by
  have normalizedFirst :
      BExecution first firstArgs (scriptNat firstTruth.toNat) flags ctx := by
    cases firstTruth <;> simpa [boolToElement, scriptNat, scriptNum_zero,
      scriptNum_one] using firstExec
  have firstFrame :=
    normalizedFirst.withSuffix (suffix := argumentFrames.flatten)
  have childrenFrame := ExecutesStackFrame.append firstFrame tailExec.executes
  have compareFrame :
      ExecutesStackFrame [.pushNum threshold, .op .OP_EQUAL]
        [scriptNat total]
        [boolToElement (decide (scriptNat threshold = scriptNat total))]
        flags ctx := by
    intro rest altStack
    by_cases equal : scriptNat threshold = scriptNat total
    · have equal' : scriptNum (Int.ofNat threshold) =
          scriptNum (Int.ofNat total) := by
        simpa [scriptNat] using equal
      simpa [equal, equal', boolToElement] using
        (Eval.pushNum (Int.ofNat threshold) [.op .OP_EQUAL]
          (scriptNat total :: rest) altStack flags ctx _
          (Eval.equal_true (scriptNat threshold) (scriptNat total) rest []
            altStack flags ctx _ equal Eval.done))
    · have equal' : scriptNum (Int.ofNat threshold) ≠
          scriptNum (Int.ofNat total) := by
        simpa [scriptNat] using equal
      simpa [equal, equal', boolToElement] using
        (Eval.pushNum (Int.ofNat threshold) [.op .OP_EQUAL]
          (scriptNat total :: rest) altStack flags ctx _
          (Eval.equal_false (scriptNat threshold) (scriptNat total) rest []
            altStack flags ctx _ equal Eval.done))
  have complete := ExecutesStackFrame.append childrenFrame compareFrame
  simpa [BExecution, compile, compileWithKeyHash, compileThresh,
    compileThreshTail, compileThreshWithKeyHash, List.append_assoc] using complete

/-- Expose the threshold's requested truth outcome while retaining byte-level
    equality as the final `OP_EQUAL` premise. -/
theorem BExecution.threshOutcome
    {threshold : Nat} {first : CoreFragment} {fragments : List CoreFragment}
    {firstArgs : Stack} {argumentFrames : List Stack}
    {firstTruth expected : Bool} {total : Nat}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs (boolToElement firstTruth) flags ctx)
    (tailExec : ThresholdTailExecution flags ctx firstTruth.toNat fragments
      argumentFrames total)
    (comparison : decide (scriptNat threshold = scriptNat total) = expected) :
    BExecutionOutcome (.thresh threshold (first :: fragments))
      (firstArgs ++ argumentFrames.flatten) expected flags ctx := by
  refine ⟨boolToElement (decide (scriptNat threshold = scriptNat total)),
    firstExec.thresh tailExec, ?_⟩
  exact (castToBool_boolToElement _).trans comparison

end LeanMiniscript.Miniscript
