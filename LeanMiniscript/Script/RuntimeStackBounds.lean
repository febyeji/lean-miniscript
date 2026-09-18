import LeanMiniscript.Script.StackGrowth

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

end LeanMiniscript.Script
