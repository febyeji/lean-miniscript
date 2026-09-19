import LeanMiniscript.Script.StackGrowth
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-- A successful instruction increases combined stack size by at most one,
    before the combined-stack limit is checked. Open or inactive conditions
    are allowed, and no success premise for the remaining program is needed. -/
theorem executeRuntimeElement_stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    next.stack.length + next.altStack.length ≤ state.stack.length + state.altStack.length + 1 := by
  have opcodeBound (stack alt : Stack)
      (success : evaluate oracle [element] state.stack state.altStack flags ctx =
        .success stack alt) :
      stack.length + alt.length ≤ state.stack.length + state.altStack.length + 1 := by
    have evaluated := evaluate_sound agreement [element] state.stack state.altStack flags ctx
    rw [success] at evaluated
    simpa using evaluated.stackGrowth
  simp only [executeRuntimeElement, bind, Except.bind, pure, Except.pure] at executed
  repeat' (split at executed <;> try simp only [bind, Except.bind, pure, Except.pure] at executed)
  all_goals simp_all
  all_goals subst next
  all_goals simp_all only
  all_goals omega

private theorem eval_nil_iff
    {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult} :
    Eval [] stack alt flags ctx result ↔ result = .success stack alt := by
  constructor
  · intro evaluated
    cases evaluated
    rfl
  · intro resultEq
    subst result
    exact .empty stack alt flags ctx

private theorem finishUnclosedConditional_ne_success
    (result : ExecResult) (stack alt : Stack) :
    finishUnclosedConditional result ≠ .success stack alt := by
  cases result <;> simp [finishUnclosedConditional]

/-- A successful one-element evaluation grows the combined stacks by no more
    than that element's static allowance. -/
private theorem evaluate_single_stackGrowthAllowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {element : ScriptElement} {before altBefore after altAfter : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (success : evaluate oracle [element] before altBefore flags ctx =
      .success after altAfter) :
    after.length + altAfter.length ≤
      before.length + altBefore.length + element.stackGrowthAllowance := by
  by_cases costOne : element.stackGrowthAllowance = 1
  · have evaluated := evaluate_sound agreement [element] before altBefore flags ctx
    rw [success] at evaluated
    simpa [costOne] using evaluated.stackGrowth
  have costZero : element.stackGrowthAllowance = 0 := by
    cases element with
    | pushData data => simp [ScriptElement.stackGrowthAllowance] at costOne
    | pushNum value => simp [ScriptElement.stackGrowthAllowance] at costOne
    | op opcode => cases opcode <;> simp_all [ScriptElement.stackGrowthAllowance]
  rw [costZero]
  have evaluated := evaluate_sound agreement [element] before altBefore flags ctx
  rw [success] at evaluated
  generalize resultEq : ExecResult.success after altAfter = result at evaluated
  cases evaluated
  case if_unbalanced =>
    exact False.elim
      (finishUnclosedConditional_ne_success _ _ _ resultEq.symm)
  case notif_unbalanced =>
    exact False.elim
      (finishUnclosedConditional_ne_success _ _ _ resultEq.symm)
  case if_execute =>
    have emptySplit : splitConditional [] = none := rfl
    simp_all
  case notif_execute =>
    have emptySplit : splitConditional [] = none := rfl
    simp_all
  all_goals cases resultEq
  all_goals simp_all [ScriptElement.stackGrowthAllowance, eval_nil_iff]
  all_goals try omega

/-- A successful source-order instruction grows the combined stacks by no more
    than its static allowance. Inactive instructions have zero actual growth. -/
theorem executeRuntimeElement_stackGrowthAllowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    next.stack.length + next.altStack.length ≤
      state.stack.length + state.altStack.length + element.stackGrowthAllowance := by
  have opcodeBound (stack alt : Stack)
      (success : evaluate oracle [element] state.stack state.altStack flags ctx =
        .success stack alt) :
      stack.length + alt.length ≤ state.stack.length + state.altStack.length +
        element.stackGrowthAllowance :=
    evaluate_single_stackGrowthAllowance agreement success
  simp only [executeRuntimeElement, bind, Except.bind, pure, Except.pure] at executed
  repeat' (split at executed <;>
    try simp only [bind, Except.bind, pure, Except.pure] at executed)
  all_goals simp_all
  all_goals subst next
  all_goals simp_all only
  all_goals omega

/-- Source-order prefix execution before combined-stack checks. All other
    instruction checks remain in force. A prefix may leave conditionals open;
    no final-condition check or successful continuation is assumed. -/
inductive RuntimePrefix (oracle : CryptoOracle) (flags : ScriptFlags) (ctx : TxContext) :
    Script → RuntimeState → RuntimeState → Prop where
  | nil (state : RuntimeState) : RuntimePrefix oracle flags ctx [] state state
  | cons {element : ScriptElement} {rest : Script} {before middle after : RuntimeState}
      (executed : executeRuntimeElement oracle element before flags ctx = .ok middle)
      (tail : RuntimePrefix oracle flags ctx rest middle after) :
      RuntimePrefix oracle flags ctx (element :: rest) before after

/-- Every reachable prefix endpoint, including states before a later failure,
    satisfies the instruction-count growth bound. -/
theorem RuntimePrefix.stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited : Script} {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after) :
    after.stack.length + after.altStack.length ≤
      before.stack.length + before.altStack.length + visited.length := by
  induction reached with
  | nil => simp
  | cons executed tail ih =>
      have step := executeRuntimeElement_stackGrowth agreement executed
      simp only [List.length_cons]
      omega

/-- Every reachable prefix endpoint is bounded by the sum of allowances for
    the source elements visited so far. -/
theorem RuntimePrefix.stackGrowth_le_allowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited : Script} {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after) :
    after.stack.length + after.altStack.length ≤
      before.stack.length + before.altStack.length +
        LeanMiniscript.Script.stackGrowthAllowance visited := by
  induction reached with
  | nil => simp [LeanMiniscript.Script.stackGrowthAllowance]
  | cons executed tail ih =>
      have step := executeRuntimeElement_stackGrowthAllowance agreement executed
      simp only [LeanMiniscript.Script.stackGrowthAllowance]
      omega

/-- A static whole-program allowance bounds every reachable prefix endpoint. -/
theorem RuntimePrefix.stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length + program.length ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  have growth := reached.stackGrowth agreement
  obtain ⟨suffix, rfl⟩ := isPrefix
  simp only [List.length_append] at budget
  omega

/-- Under the static allowance, checking any prefix endpoint cannot reject it.
    Reachability uses the instruction function before this check. -/
theorem RuntimePrefix.checkStack_ok
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length + program.length ≤ maxStackSize) :
    checkRuntimeStack after = .ok after := by
  have bounded := reached.stackBound agreement isPrefix budget
  simp [checkRuntimeStack, Nat.not_lt_of_le bounded]

/-- The refined whole-program allowance bounds every reachable prefix
    endpoint. -/
theorem RuntimePrefix.stackBoundAllowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length +
      LeanMiniscript.Script.stackGrowthAllowance program ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  have growth := reached.stackGrowth_le_allowance agreement
  have prefixBound := stackGrowthAllowance_le_of_isPrefix isPrefix
  omega

/-- Under the refined allowance, checking any reachable prefix endpoint cannot
    reject it for combined-stack size. -/
theorem RuntimePrefix.checkStack_ok_of_allowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length +
      LeanMiniscript.Script.stackGrowthAllowance program ≤ maxStackSize) :
    checkRuntimeStack after = .ok after := by
  have bounded := reached.stackBoundAllowance agreement isPrefix budget
  simp [checkRuntimeStack, Nat.not_lt_of_le bounded]

/-- Proof-facing execution of a source prefix, omitting only combined-stack
    checks. The returned state retains open conditions and signature weight. -/
def runRuntimePrefix (oracle : CryptoOracle) : Script → RuntimeState →
    ScriptFlags → TxContext → Except ScriptError RuntimeState
  | [], state, _, _ => .ok state
  | element :: rest, state, flags, ctx => do
      let next ← executeRuntimeElement oracle element state flags ctx
      runRuntimePrefix oracle rest next flags ctx

/-- The prefix relation describes exactly the states returned by the prefix
    runner; it does not assert whole-script acceptance. -/
theorem runtimePrefix_iff
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {visited : Script} {before after : RuntimeState} :
    RuntimePrefix oracle flags ctx visited before after ↔
      runRuntimePrefix oracle visited before flags ctx = .ok after := by
  constructor
  · intro reached
    induction reached with
    | nil => rfl
    | cons executed tail ih => simp [runRuntimePrefix, executed, ih, bind, Except.bind]
  · intro executed
    induction visited generalizing before with
    | nil =>
        simp only [runRuntimePrefix, Except.ok.injEq] at executed
        subst after
        exact .nil _
    | cons element rest ih =>
        cases step : executeRuntimeElement oracle element before flags ctx with
        | error error => simp [runRuntimePrefix, step, bind, Except.bind] at executed
        | ok next =>
            apply RuntimePrefix.cons step
            apply ih
            simpa [runRuntimePrefix, step, bind, Except.bind] using executed

/-- The static allowance makes every combined-stack check redundant for the
    full evaluator. Equality covers both successes and failures: no successful
    whole-program execution is assumed. Push-size, opcode, signature-weight,
    and final-condition errors remain observable in their original order. -/
theorem evaluateRuntime_eq_runRuntimePrefix
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (budget : state.stack.length + state.altStack.length + script.length ≤ maxStackSize) :
    evaluateRuntime oracle script state flags ctx =
      match runRuntimePrefix oracle script state flags ctx with
      | .error error => .failure error
      | .ok after => finishRuntime after := by
  induction script generalizing state with
  | nil => rfl
  | cons element rest ih =>
      cases step : executeRuntimeElement oracle element state flags ctx with
      | error error =>
          simp [evaluateRuntime, runtimeStep, runRuntimePrefix, step, bind, Except.bind]
      | ok next =>
          have growth := executeRuntimeElement_stackGrowth agreement step
          have nextBudget : next.stack.length + next.altStack.length + rest.length ≤ maxStackSize := by
            simp only [List.length_cons] at budget
            omega
          have bounded : next.stack.length + next.altStack.length ≤ maxStackSize := by omega
          simpa [evaluateRuntime, runtimeStep, runRuntimePrefix, step,
            checkRuntimeStack, Nat.not_lt_of_le bounded, bind, Except.bind] using ih nextBudget

/-- The fragment-specific allowance also makes every combined-stack check
    redundant. As with the instruction-count theorem, other runtime failures
    remain observable in their original order. -/
theorem evaluateRuntime_eq_runRuntimePrefix_of_allowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (budget : state.stack.length + state.altStack.length +
      LeanMiniscript.Script.stackGrowthAllowance script ≤ maxStackSize) :
    evaluateRuntime oracle script state flags ctx =
      match runRuntimePrefix oracle script state flags ctx with
      | .error error => .failure error
      | .ok after => finishRuntime after := by
  induction script generalizing state with
  | nil => rfl
  | cons element rest ih =>
      cases step : executeRuntimeElement oracle element state flags ctx with
      | error error =>
          simp [evaluateRuntime, runtimeStep, runRuntimePrefix, step, bind, Except.bind]
      | ok next =>
          have growth := executeRuntimeElement_stackGrowthAllowance agreement step
          have nextBudget : next.stack.length + next.altStack.length +
              LeanMiniscript.Script.stackGrowthAllowance rest ≤ maxStackSize := by
            simp only [LeanMiniscript.Script.stackGrowthAllowance] at budget
            omega
          have bounded : next.stack.length + next.altStack.length ≤ maxStackSize := by
            omega
          simpa [evaluateRuntime, runtimeStep, runRuntimePrefix, step,
            checkRuntimeStack, Nat.not_lt_of_le bounded, bind, Except.bind] using ih nextBudget

end LeanMiniscript.Script
