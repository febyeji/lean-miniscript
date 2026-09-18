import LeanMiniscript.Script.ValidationWeightCore

namespace LeanMiniscript.Script

/-!
Runtime limits for the modeled opcode subset. Instructions are visited in source
order, including inactive branches: oversized pushes fail when encountered,
while signature debits and ordinary opcode execution only occur in active code.
The branch-projection evaluator remains available for budget-only reasoning.
-/

/-- Runtime state; the condition list is innermost-first. -/
structure RuntimeState where
  stack : Stack
  altStack : Stack
  conditions : List Bool := []
  weight : Nat
  deriving Repr

/-- Numeric pushes use the same byte representation as canonical serialization. -/
def ScriptElement.pushSize : ScriptElement → Nat
  | .pushData bytes => bytes.size
  | .pushNum number => (scriptNum number).size
  | .op _ => 0

/-- Core checks combined main/alt-stack depth after each visited instruction. -/
def checkRuntimeStack (state : RuntimeState) : Except ScriptError RuntimeState :=
  if state.stack.length + state.altStack.length > maxStackSize then .error .stackSize
  else .ok state

theorem checkRuntimeStack_ok {before after : RuntimeState}
    (checked : checkRuntimeStack before = .ok after) :
    after = before ∧ after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold checkRuntimeStack at checked
  split at checked
  · contradiction
  · cases checked
    exact ⟨rfl, by omega⟩

/-- One source instruction, before the combined stack check. Push size precedes
    control handling and execution, including in an inactive branch. -/
def executeRuntimeElement (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  if element.pushSize > maxScriptElementSize then throw .pushSize
  let active := state.conditions.all id
  match element with
  | .op .OP_IF | .op .OP_NOTIF =>
      if active then
        match state.stack with
        | [] => throw .stackUnderflow
        | top :: rest =>
            if minimalIfSatisfied flags top then
              return { state with
                stack := rest
                conditions := element.branchChoice top :: state.conditions }
            else throw .minimalIf
      else return { state with conditions := false :: state.conditions }
  | .op .OP_ELSE =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | first :: rest => return { state with conditions := (!first) :: rest }
  | .op .OP_ENDIF =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | _ :: rest => return { state with conditions := rest }
  | _ =>
      if active then
        let weight ← prepareValidationWeight element state.stack flags ctx state.weight
        match evaluate oracle [element] state.stack state.altStack flags ctx with
        | .failure error => throw error
        | .success stack alt => return { state with stack := stack, altStack := alt, weight := weight }
      else return state

/-- Shared step boundary: opcode errors precede the post-instruction stack limit. -/
def runtimeStep (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  let next ← executeRuntimeElement oracle element state flags ctx
  checkRuntimeStack next

theorem runtimeStep_stackBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold runtimeStep at stepped
  cases computed : executeRuntimeElement oracle element before flags ctx with
  | error error => simp [computed, bind, Except.bind] at stepped
  | ok next =>
      simp only [computed, bind, Except.bind] at stepped
      exact (checkRuntimeStack_ok stepped).2

/-- Every visited instruction, active or skipped, passes the push-size bound. -/
theorem runtimeStep_pushBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    element.pushSize ≤ maxScriptElementSize := by
  by_cases exceeded : element.pushSize > maxScriptElementSize
  · simp [runtimeStep, executeRuntimeElement, exceeded, bind, Except.bind] at stepped
  · exact Nat.le_of_not_gt exceeded

/-- Resource and control checks do not weaken the existing crypto boundary. -/
theorem runtimeStep_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle element state flags ctx =
      runtimeStep CryptoOracle.model element state flags ctx := by
  have opcode := evaluate_eq_of_eval agreement
    (evaluate_sound CryptoOracle.model_refines [element] state.stack state.altStack flags ctx)
  simp only [runtimeStep, executeRuntimeElement, opcode]

/-- EOF reports an unclosed conditional only after earlier runtime checks pass. -/
def finishRuntime (state : RuntimeState) : WeightedResult :=
  if state.conditions.isEmpty then .success state.stack state.altStack state.weight
  else .failure .unbalancedConditional

/-- Structural recursion over literal source order retains inactive push checks. -/
def evaluateRuntime (oracle : CryptoOracle) : Script → RuntimeState →
    ScriptFlags → TxContext → WeightedResult
  | [], state, _, _ => finishRuntime state
  | element :: rest, state, flags, ctx =>
      match runtimeStep oracle element state flags ctx with
      | .error error => .failure error
      | .ok next => evaluateRuntime oracle rest next flags ctx

/-- These resource guarantees hold for every oracle, without a cryptographic
    agreement premise. Successful execution visits every source instruction. -/
theorem evaluateRuntime_bounds
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    (script : Script) {state : RuntimeState} {stack alt : Stack} {weight : Nat}
    (initial : state.stack.length + state.altStack.length ≤ maxStackSize)
    (success : evaluateRuntime oracle script state flags ctx = .success stack alt weight) :
    stack.length + alt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  induction script generalizing state with
  | nil =>
      simp only [evaluateRuntime, finishRuntime] at success
      split at success
      · cases success; exact ⟨initial, by simp⟩
      · contradiction
  | cons element rest ih =>
      simp only [evaluateRuntime] at success
      cases stepped : runtimeStep oracle element state flags ctx with
      | error error => simp [stepped] at success
      | ok next =>
          simp only [stepped] at success
          obtain ⟨bounded, pushes⟩ := ih (runtimeStep_stackBound stepped) success
          refine ⟨bounded, ?_⟩
          intro item member
          rcases List.mem_cons.mp member with same | tail
          · subst item; exact runtimeStep_pushBound stepped
          · exact pushes item tail

/-- The modeled relation composes source-order steps and final condition checks.
    Its step function uses the abstract crypto oracle, whose active opcode
    behavior is supplied by the existing evaluator/`Eval` refinement theorem. -/
inductive RuntimeEval : Script → RuntimeState → ScriptFlags → TxContext → WeightedResult → Prop where
  | done (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
      RuntimeEval [] state flags ctx (finishRuntime state)
  | error {element : ScriptElement} {rest : Script} {state : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
      (failed : runtimeStep CryptoOracle.model element state flags ctx = .error error) :
      RuntimeEval (element :: rest) state flags ctx (.failure error)
  | step {element : ScriptElement} {rest : Script} {state next : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {result : WeightedResult}
      (stepped : runtimeStep CryptoOracle.model element state flags ctx = .ok next)
      (tail : RuntimeEval rest next flags ctx result) :
      RuntimeEval (element :: rest) state flags ctx result

theorem evaluateRuntime_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {result : WeightedResult} (evaluated : RuntimeEval script state flags ctx result) :
    evaluateRuntime oracle script state flags ctx = result := by
  induction evaluated with
  | done => rfl
  | error failed => simp [evaluateRuntime, runtimeStep_eq_model agreement, failed]
  | step stepped tail ih => simp [evaluateRuntime, runtimeStep_eq_model agreement, stepped, ih]

theorem evaluateRuntime_sound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    RuntimeEval script state flags ctx (evaluateRuntime oracle script state flags ctx) := by
  induction script generalizing state with
  | nil => exact .done state flags ctx
  | cons element rest ih =>
      simp only [evaluateRuntime, runtimeStep_eq_model agreement]
      cases stepped : runtimeStep CryptoOracle.model element state flags ctx with
      | error error => exact .error stepped
      | ok next => exact .step stepped (ih next)

theorem runtime_model_iff {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {result : WeightedResult} :
    RuntimeEval script state flags ctx result ↔
      evaluateRuntime CryptoOracle.model script state flags ctx = result := by
  constructor
  · exact evaluateRuntime_eq_of_eval CryptoOracle.model_refines
  · intro computed
    rw [← computed]
    exact evaluateRuntime_sound CryptoOracle.model_refines script state flags ctx

theorem RuntimeEval.deterministic {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {first second : WeightedResult}
    (a : RuntimeEval script state flags ctx first) (b : RuntimeEval script state flags ctx second) :
    first = second := by
  exact (runtime_model_iff.mp a).symm.trans (runtime_model_iff.mp b)

/-- A bounded initial state and successful execution imply a bounded final
    state; `runtimeStep_stackBound` covers every intermediate transition. -/
theorem RuntimeEval.stackBound {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (evaluated : RuntimeEval script state flags ctx (.success stack alt weight))
    (initial : state.stack.length + state.altStack.length ≤ maxStackSize) :
    stack.length + alt.length ≤ maxStackSize := by
  generalize resultEq : WeightedResult.success stack alt weight = result at evaluated
  induction evaluated with
  | done state flags ctx =>
      unfold finishRuntime at resultEq
      split at resultEq
      · cases resultEq; exact initial
      · contradiction
  | error => cases resultEq
  | step stepped tail ih => exact ih (runtimeStep_stackBound stepped) resultEq

/-- Runtime-limited execution starts with no open conditional. The caller
    checks initial witness bounds; the full-witness entry does so explicitly. -/
def evaluateWithRuntimeLimits (oracle : CryptoOracle) (script : Script)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) : WeightedResult :=
  evaluateRuntime oracle script { stack := stack, altStack := alt, weight := weight } flags ctx

theorem evaluateWithRuntimeLimits_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      evaluateWithRuntimeLimits CryptoOracle.model script stack alt flags ctx weight := by
  exact evaluateRuntime_eq_of_eval agreement
    (evaluateRuntime_sound CryptoOracle.model_refines script _ flags ctx)

theorem evaluateWithRuntimeLimits_bounds
    {oracle : CryptoOracle}
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (initial : stack.length + alt.length ≤ maxStackSize)
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    finalStack.length + finalAlt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  exact evaluateRuntime_bounds script initial success

end LeanMiniscript.Script
