import LeanMiniscript.Miniscript.SatisfactionProofs.Execution

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Straight-line connective composition -/

/-- `and_v` runs a V fragment before a B fragment, preserving the latter's
    exact result and every surrounding main/alternate-stack suffix. -/
theorem VExecution.and_v_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.and_v first second) (firstArgs ++ secondArgs) result flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, BExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append firstRun secondRun

/-- The K result of the second `and_v` child remains available to a following
    signature check. -/
theorem VExecution.and_v_k
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : KExecution second secondArgs key flags ctx) :
    KExecution (.and_v first second) (firstArgs ++ secondArgs) key flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, KExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append firstRun secondRun

/-- Two V fragments compose silently through `and_v`. -/
theorem VExecution.and_v_v
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.and_v first second) (firstArgs ++ secondArgs) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have secondRun := secondExec rest altStack
  simpa [VExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun secondRun

/-- A B truth outcome from the second child passes through `and_v`. -/
theorem VExecution.and_v_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {expected : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : VExecution first firstArgs flags ctx)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.and_v first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := secondExec
  exact ⟨result, firstExec.and_v_b frame, truth⟩

/-- `and_b` executes its B child, then its W child under that exact result, and
    finally decodes both operands for `OP_BOOLAND`. The returned boolean uses
    source-child order independently of the W wrapper's stack order. -/
theorem BExecution.and_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue) :
    BExecution (.and_b first second) (firstArgs ++ secondArgs)
      (boolToElement ((firstValue != 0) && (secondValue != 0))) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  cases order with
  | savedFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLAND] (firstResult :: secondResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) && (secondValue != 0)) :: rest)
              altStack) := by
        apply Eval.booland (a := firstValue) (b := secondValue)
        · exact decoded
        · exact Eval.done
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun
  | resultFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLAND] (secondResult :: firstResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) && (secondValue != 0)) :: rest)
              altStack) := by
        simpa [Bool.and_comm] using
          (Eval.booland secondResult firstResult secondValue firstValue rest []
            altStack flags ctx
            (.success
              (boolToElement ((secondValue != 0) && (firstValue != 0)) :: rest)
              altStack)
            decoded
            (Eval.done (stack :=
              boolToElement ((secondValue != 0) && (firstValue != 0)) :: rest)
              (altStack := altStack)))
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun

/-- `and_b`'s canonical result has the requested truth value once its decoded
    operands' nonzero tests establish that value. -/
theorem BExecution.and_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue)
    (truth : ((firstValue != 0) && (secondValue != 0)) = expected) :
    BExecutionOutcome (.and_b first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  refine ⟨boolToElement ((firstValue != 0) && (secondValue != 0)),
    firstExec.and_b secondExec decoded, ?_⟩
  exact (castToBool_boolToElement _).trans truth

/-- `or_b` has the same exact operand-order boundary as `and_b`, followed by
    `OP_BOOLOR`. -/
theorem BExecution.or_b
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue) :
    BExecution (.or_b first second) (firstArgs ++ secondArgs)
      (boolToElement ((firstValue != 0) || (secondValue != 0))) flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  cases order with
  | savedFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLOR] (firstResult :: secondResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) || (secondValue != 0)) :: rest)
              altStack) := by
        apply Eval.boolor (a := firstValue) (b := secondValue)
        · exact decoded
        · exact Eval.done
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun
  | resultFirst =>
      have secondRun := secondExec firstResult rest altStack
      have childrenRun := Eval.append firstRun secondRun
      have operatorRun :
          Eval [.op .OP_BOOLOR] (secondResult :: firstResult :: rest)
            altStack flags ctx
            (.success
              (boolToElement ((firstValue != 0) || (secondValue != 0)) :: rest)
              altStack) := by
        simpa [Bool.or_comm] using
          (Eval.boolor secondResult firstResult secondValue firstValue rest []
            altStack flags ctx
            (.success
              (boolToElement ((secondValue != 0) || (firstValue != 0)) :: rest)
              altStack)
            decoded
            (Eval.done (stack :=
              boolToElement ((secondValue != 0) || (firstValue != 0)) :: rest)
              (altStack := altStack)))
      simpa [BExecution, WExecution, WStackOrder.outputs,
        WStackOrder.BinaryDecoded, ExecutesStackFrame, compile,
        compileWithKeyHash, List.append_assoc] using
        Eval.append childrenRun operatorRun

/-- `or_b`'s normalized result has the requested truth value. -/
theorem BExecution.or_bOutcome
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {order : WStackOrder} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs firstResult flags ctx)
    (secondExec : WExecution second secondArgs secondResult order flags ctx)
    (decoded : order.BinaryDecoded flags firstResult secondResult
      firstValue secondValue)
    (truth : ((firstValue != 0) || (secondValue != 0)) = expected) :
    BExecutionOutcome (.or_b first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  refine ⟨boolToElement ((firstValue != 0) || (secondValue != 0)),
    firstExec.or_b secondExec decoded, ?_⟩
  exact (castToBool_boolToElement _).trans truth

/-! ## Conditional connective composition -/

/-- A satisfying first child makes `or_c` skip its V child. The child-produced
    selector keeps its explicit MINIMALIF and truthiness premises. -/
theorem BExecution.or_c_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    VExecution (.or_c first second) firstArgs flags ctx := by
  have tail := ExecutesStackFrame.notifThen_skip
    (body := compile second) (inputs := []) (ctx := ctx)
    (compile_balancedControlFlow second) minimal truth
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstExec tail

/-- A dissatisfied first child makes `or_c` execute its V child. -/
theorem BExecution.or_c_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.or_c first second) (firstArgs ++ secondArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifThen_execute
    (compile_balancedControlFlow second) minimal falsy secondExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

/-- On the direct `or_d` path, `OP_IFDUP` preserves the satisfying first-child
    selector as the connector's exact B result. -/
theorem BExecution.or_d_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    BExecution (.or_d first second) firstArgs selector flags ctx := by
  intro rest altStack
  have firstRun := firstExec rest altStack
  have conditionalFrame := ExecutesStackFrame.notifThen_skip
    (body := compile second) (inputs := [selector]) (ctx := ctx)
    (compile_balancedControlFlow second) minimal truth
  have tailRun :
      Eval (.op .OP_IFDUP :: .op .OP_NOTIF ::
          compile second ++ [.op .OP_ENDIF])
        (selector :: rest) altStack flags ctx
        (.success (selector :: rest) altStack) := by
    exact Eval.ifdup_true selector rest altStack _ flags ctx _ truth
      (conditionalFrame rest altStack)
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun tailRun

/-- On the alternate `or_d` path, a false first result is consumed and the
    second child's exact B result becomes the connector result. -/
theorem BExecution.or_d_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.or_d first second) (firstArgs ++ secondArgs) result flags ctx := by
  intro rest altStack
  have firstRun := firstExec (secondArgs ++ rest) altStack
  have conditionalFrame := ExecutesStackFrame.notifThen_execute
    (compile_balancedControlFlow second) minimal falsy secondExec
  have tailRun :
      Eval (.op .OP_IFDUP :: .op .OP_NOTIF ::
          compile second ++ [.op .OP_ENDIF])
        (selector :: secondArgs ++ rest) altStack flags ctx
        (.success (result :: rest) altStack) := by
    exact Eval.ifdup_false selector (secondArgs ++ rest) altStack _ flags ctx _
      falsy (conditionalFrame rest altStack)
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using Eval.append firstRun tailRun

theorem BExecutionOutcome.or_d_left
    {first second : CoreFragment} {firstArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true) :
    BExecutionOutcome (.or_d first second) firstArgs true flags ctx :=
  ⟨selector, firstExec.or_d_left minimal truth, truth⟩

theorem BExecutionOutcome.or_d_right
    {first second : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.or_d first second) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := secondExec
  exact ⟨result, firstExec.or_d_right minimal falsy frame, truth⟩

/-- The canonical true selector chooses the first B branch of `or_i` and
    satisfies MINIMALIF for every flag set. -/
theorem BExecution.or_i_left
    {first second : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution first args result flags ctx) :
    BExecution (.or_i first second) (trueElement :: args) result flags ctx := by
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by decide) executed

/-- The canonical false selector chooses the second B branch of `or_i`. -/
theorem BExecution.or_i_right
    {first second : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution second args result flags ctx) :
    BExecution (.or_i first second) (falseElement :: args) result flags ctx := by
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by decide) executed

theorem KExecution.or_i_left
    {first second : CoreFragment} {args : Stack} {key : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution first args key flags ctx) :
    KExecution (.or_i first second) (trueElement :: args) key flags ctx := by
  simpa [KExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by decide) executed

theorem KExecution.or_i_right
    {first second : CoreFragment} {args : Stack} {key : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution second args key flags ctx) :
    KExecution (.or_i first second) (falseElement :: args) key flags ctx := by
  simpa [KExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by decide) executed

theorem VExecution.or_i_left
    {first second : CoreFragment} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution first args flags ctx) :
    VExecution (.or_i first second) (trueElement :: args) flags ctx := by
  simpa [VExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_first
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) (by decide) executed

theorem VExecution.or_i_right
    {first second : CoreFragment} {args : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : VExecution second args flags ctx) :
    VExecution (.or_i first second) (falseElement :: args) flags ctx := by
  simpa [VExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.ifElse_second
      (compile_balancedControlFlow first) (compile_balancedControlFlow second)
      (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) (by decide) executed

theorem BExecutionOutcome.or_i_left
    {first second : CoreFragment} {args : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome first args expected flags ctx) :
    BExecutionOutcome (.or_i first second) (trueElement :: args)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.or_i_left, truth⟩

theorem BExecutionOutcome.or_i_right
    {first second : CoreFragment} {args : Stack} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome second args expected flags ctx) :
    BExecutionOutcome (.or_i first second) (falseElement :: args)
      expected flags ctx := by
  obtain ⟨result, frame, truth⟩ := executed
  exact ⟨result, frame.or_i_right, truth⟩

/-- A truthy first child selects Y, the second source child of `andor`. -/
theorem BExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : BExecution second secondArgs result flags ctx) :
    BExecution (.andor first second third) (firstArgs ++ secondArgs)
      result flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.append firstFrame tail

/-- A false first child selects Z, the third source child of `andor`. -/
theorem BExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector result : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : BExecution third thirdArgs result flags ctx) :
    BExecution (.andor first second third) (firstArgs ++ thirdArgs)
      result flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, compile, compileWithKeyHash, List.append_assoc] using
    ExecutesStackFrame.append firstFrame tail

theorem KExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : KExecution second secondArgs key flags ctx) :
    KExecution (.andor first second third) (firstArgs ++ secondArgs)
      key flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, KExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem KExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector key : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : KExecution third thirdArgs key flags ctx) :
    KExecution (.andor first second third) (firstArgs ++ thirdArgs)
      key flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, KExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem VExecution.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : VExecution second secondArgs flags ctx) :
    VExecution (.andor first second third) (firstArgs ++ secondArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := secondArgs)
  have tail := ExecutesStackFrame.notifElse_second
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal truth secondExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem VExecution.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : VExecution third thirdArgs flags ctx) :
    VExecution (.andor first second third) (firstArgs ++ thirdArgs) flags ctx := by
  have firstFrame := firstExec.withSuffix (suffix := thirdArgs)
  have tail := ExecutesStackFrame.notifElse_first
    (compile_balancedControlFlow third) (compile_balancedControlFlow second)
    minimal falsy thirdExec
  simpa [BExecution, VExecution, compile, compileWithKeyHash,
    List.append_assoc] using ExecutesStackFrame.append firstFrame tail

theorem BExecutionOutcome.andor_true
    {first second third : CoreFragment} {firstArgs secondArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (truth : castToBool selector = true)
    (secondExec : BExecutionOutcome second secondArgs expected flags ctx) :
    BExecutionOutcome (.andor first second third) (firstArgs ++ secondArgs)
      expected flags ctx := by
  obtain ⟨result, frame, resultTruth⟩ := secondExec
  exact ⟨result, firstExec.andor_true minimal truth frame, resultTruth⟩

theorem BExecutionOutcome.andor_false
    {first second third : CoreFragment} {firstArgs thirdArgs : Stack}
    {selector : StackElement} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (firstExec : BExecution first firstArgs selector flags ctx)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector)
    (falsy : castToBool selector = false)
    (thirdExec : BExecutionOutcome third thirdArgs expected flags ctx) :
    BExecutionOutcome (.andor first second third) (firstArgs ++ thirdArgs)
      expected flags ctx := by
  obtain ⟨result, frame, resultTruth⟩ := thirdExec
  exact ⟨result, firstExec.andor_false minimal falsy frame, resultTruth⟩

end LeanMiniscript.Miniscript
