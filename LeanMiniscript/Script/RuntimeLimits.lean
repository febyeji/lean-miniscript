import LeanMiniscript.Script.ValidationWeightCore

/-! Source-order execution with stack, push-size and signature-weight limits.
Bounds, refinement and opcode lemmas are in RuntimeLimitsProofs. -/

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
            if minimalIfSatisfied flags ctx.sigVersion top then
              return { state with
                stack := rest
                conditions := element.branchChoice top :: state.conditions }
            else throw (minimalIfError ctx.sigVersion)
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

/-- Runtime-limited execution starts with no open conditional. The caller
    checks initial witness bounds; the full-witness entry does so explicitly. -/
def evaluateWithRuntimeLimits (oracle : CryptoOracle) (script : Script)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) : WeightedResult :=
  evaluateRuntime oracle script { stack := stack, altStack := alt, weight := weight } flags ctx

end LeanMiniscript.Script
