import LeanMiniscript.Miniscript.SatisfactionProofs.Execution

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Guarded wrapper composition -/

/-- Wrapper `d` duplicates its canonical true selector, consumes one copy in
    `OP_IF`, and runs a zero-argument V child while retaining the other copy as
    its B result. Balanced child compilation identifies the exact IF body. -/
theorem VExecution.d
    {fragment : CoreFragment} {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution fragment [] flags ctx) :
    BExecution (.d fragment) [trueElement] trueElement flags ctx := by
  intro rest altStack
  have childExec := executed (trueElement :: rest) altStack
  have truth : castToBool trueElement = true := by decide
  have split := splitConditional_compile_ifThen fragment
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (trueElement :: trueElement :: rest) altStack flags ctx
        (.success (trueElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
        childExec
  simpa [BExecution, VExecution, ExecutesStackFrame, compile,
    compileWithKeyHash] using
    Eval.dup trueElement rest _ altStack flags ctx _ ifExec

/-- The canonical false selector skips the `d` child and remains as the exact
    false B result on every surrounding stack. -/
theorem d_dissatisfaction_execution
    (fragment : CoreFragment) (flags : ScriptFlags) (ctx : TxContext) :
    BExecution (.d fragment) [falseElement] falseElement flags ctx := by
  intro rest altStack
  have falsehood : castToBool falseElement = false := by decide
  have split := splitConditional_compile_ifThen fragment
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (falseElement :: falseElement :: rest) altStack flags ctx
        (.success (falseElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, falsehood] using
        (Eval.done (stack := falseElement :: rest) (altStack := altStack))
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    Eval.dup falseElement rest _ altStack flags ctx _ ifExec

/-- A nonempty first runtime item makes `j` execute its B child. The explicit
    decode premise exposes the four-byte Script-number boundary of the
    `OP_SIZE OP_0NOTEQUAL` guard. -/
theorem BExecution.j
    {fragment : CoreFragment} {top result : StackElement} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment (top :: args) result flags ctx)
    (nonempty : top.size ≠ 0)
    (decoded : decodeScriptNum (scriptNat top.size) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat top.size)) :
    BExecution (.j fragment) (top :: args) result flags ctx := by
  intro rest altStack
  have childExec := executed rest altStack
  have nonzero : (Int.ofNat top.size != 0) = true := by
    simp [nonempty]
  have branchTrue :
      boolToElement (Int.ofNat top.size != 0) = trueElement := by
    rw [nonzero]
    rfl
  have truth : castToBool trueElement = true := by decide
  have split := splitConditional_compile_ifThen fragment
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (trueElement :: top :: args ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, truth] using
        childExec
  have ifExec' :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (boolToElement (Int.ofNat top.size != 0) :: top :: args ++ rest)
        altStack flags ctx (.success (result :: rest) altStack) := by
    simpa only [branchTrue] using ifExec
  have nonzeroExec :
      Eval (.op .OP_0NOTEQUAL :: .op .OP_IF ::
          compile fragment ++ [.op .OP_ENDIF])
        (scriptNat top.size :: top :: args ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    exact Eval.zeroNotEqual (scriptNat top.size) (Int.ofNat top.size)
      (top :: args ++ rest) altStack _ flags ctx _ decoded ifExec'
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using
    Eval.size top (args ++ rest) altStack _ flags ctx _ nonzeroExec

/-- `j` preserves the child's requested truth outcome whenever its first
    runtime item is nonempty and its encoded size satisfies the numeric guard. -/
theorem BExecutionOutcome.j
    {fragment : CoreFragment} {top : StackElement} {args : Stack}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment (top :: args) expected flags ctx)
    (nonempty : top.size ≠ 0)
    (decoded : decodeScriptNum (scriptNat top.size) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat top.size)) :
    BExecutionOutcome (.j fragment) (top :: args) expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.j nonempty decoded, truth⟩

/-- The canonical empty item takes `j`'s skipped branch and remains as the
    exact false B result without requiring any child execution premise. -/
theorem j_dissatisfaction_execution
    (fragment : CoreFragment) (flags : ScriptFlags) (ctx : TxContext) :
    BExecution (.j fragment) [falseElement] falseElement flags ctx := by
  intro rest altStack
  have decoded :
      decodeScriptNum (scriptNat falseElement.size) flags.minimalData
        maxArithmeticScriptNumBytes = .ok (Int.ofNat falseElement.size) := by
    change decodeScriptNum falseElement flags.minimalData
      maxArithmeticScriptNumBytes = .ok 0
    cases h : flags.minimalData <;> rfl
  have zero : (Int.ofNat falseElement.size != 0) = false := by decide
  have branchFalse :
      boolToElement (Int.ofNat falseElement.size != 0) = falseElement := by
    rw [zero]
    rfl
  have falsehood : castToBool falseElement = false := by decide
  have split := splitConditional_compile_ifThen fragment
  have ifExec :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (falseElement :: falseElement :: rest) altStack flags ctx
        (.success (falseElement :: rest) altStack) := by
    apply Eval.if_execute (frame :=
      { branches := [compile fragment], after := [] })
    · exact split
    · exact minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg
    · simpa [ConditionalFrame.select, selectConditionalBranches, falsehood] using
        (Eval.done (stack := falseElement :: rest) (altStack := altStack))
  have ifExec' :
      Eval (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF])
        (boolToElement (Int.ofNat falseElement.size != 0) ::
          falseElement :: rest)
        altStack flags ctx (.success (falseElement :: rest) altStack) := by
    simpa only [branchFalse] using ifExec
  have nonzeroExec :
      Eval (.op .OP_0NOTEQUAL ::
          (.op .OP_IF :: compile fragment ++ [.op .OP_ENDIF]))
        (scriptNat falseElement.size :: falseElement :: rest)
        altStack flags ctx (.success (falseElement :: rest) altStack) := by
    exact Eval.zeroNotEqual (scriptNat falseElement.size)
      (Int.ofNat falseElement.size) (falseElement :: rest) altStack _ flags ctx _
      decoded ifExec'
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    Eval.size falseElement rest altStack _ flags ctx _ nonzeroExec

end LeanMiniscript.Miniscript
