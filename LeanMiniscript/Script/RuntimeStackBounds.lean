import LeanMiniscript.Script.StackGrowth
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

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
        element.stackGrowthAllowance := by
    have evaluated := evaluate_sound agreement [element] state.stack state.altStack flags ctx
    rw [success] at evaluated
    simpa [stackGrowthAllowance] using evaluated.stackGrowth_le_allowance
  simp only [executeRuntimeElement, bind, Except.bind, pure, Except.pure] at executed
  repeat' (split at executed <;>
    try simp only [bind, Except.bind, pure, Except.pure] at executed)
  all_goals simp_all
  all_goals subst next
  all_goals simp_all only
  all_goals omega

/-- A successful instruction with allowance at most one satisfies the
    instruction-count bound, before the combined-stack check. -/
theorem executeRuntimeElement_stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next)
    (oneItem : element.stackGrowthAllowance ≤ 1) :
    next.stack.length + next.altStack.length ≤ state.stack.length + state.altStack.length + 1 := by
  have growth := executeRuntimeElement_stackGrowthAllowance agreement executed
  omega

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

/-- A prefix whose elements have allowance at most one satisfies the
    instruction-count growth bound, including endpoints before later failures. -/
theorem RuntimePrefix.stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited : Script} {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (oneItem : OneItemGrowth visited) :
    after.stack.length + after.altStack.length ≤
      before.stack.length + before.altStack.length + visited.length := by
  have growth := reached.stackGrowth_le_allowance agreement
  have bound := stackGrowthAllowance_le_length visited oneItem
  omega

/-- A static whole-program allowance bounds every reachable prefix endpoint. -/
theorem RuntimePrefix.stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length + program.length ≤ maxStackSize)
    (oneItem : OneItemGrowth program) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  have growth := reached.stackGrowth_le_allowance agreement
  have prefixBound := stackGrowthAllowance_le_of_isPrefix isPrefix
  have bound := stackGrowthAllowance_le_length program oneItem
  omega

/-- Under the static allowance, checking any prefix endpoint cannot reject it.
    Reachability uses the instruction function before this check. -/
theorem RuntimePrefix.checkStack_ok
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {flags : ScriptFlags} {ctx : TxContext} {visited program : Script}
    {before after : RuntimeState}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix program)
    (budget : before.stack.length + before.altStack.length + program.length ≤ maxStackSize)
    (oneItem : OneItemGrowth program) :
    checkRuntimeStack after = .ok after := by
  have bounded := reached.stackBound agreement isPrefix budget oneItem
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

/-- The opcode-weighted allowance makes every combined-stack check redundant.
    Other runtime failures remain observable in their original order. -/
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

/-- The instruction-count budget suffices when every element has allowance
    at most one. Equality covers successes and failures with their original
    error order, without assuming whole-program success. -/
theorem evaluateRuntime_eq_runRuntimePrefix
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (budget : state.stack.length + state.altStack.length + script.length ≤ maxStackSize)
    (oneItem : OneItemGrowth script) :
    evaluateRuntime oracle script state flags ctx =
      match runRuntimePrefix oracle script state flags ctx with
      | .error error => .failure error
      | .ok after => finishRuntime after := by
  apply evaluateRuntime_eq_runRuntimePrefix_of_allowance agreement
  have bound := stackGrowthAllowance_le_length script oneItem
  omega

end LeanMiniscript.Script
