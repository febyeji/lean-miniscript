/-
  LeanMiniscript.Script.SmallStep
  ============================
  Small-step operational semantics for Bitcoin Script.

  The model gives each active opcode a single state transition. Conditional
  opcodes select their active branch projection in one step, matching the
  existing big-step evaluator. Terminal failures are represented explicitly.

  References:
  - Bitcoin Core: src/script/interpreter.cpp, EvalScript()
  - KEVM (CSF 2018) uses a similar small-step approach for EVM
-/

import LeanMiniscript.Script.ValidationWeightCore

namespace LeanMiniscript.Script

/-- Running state for branch-projection execution. `pendingUnbalanced` records
    that an `IF`/`NOTIF` had no matching `ENDIF`; an active runtime error still
    takes precedence, while successful exhaustion becomes
    `unbalancedConditional`. -/
structure MachineState extends ExecState where
  pendingUnbalanced : Bool := false
  deriving Repr

/-- A small-step machine is either running or has produced its final result. -/
inductive Configuration where
  | running : MachineState → Configuration
  | halted : ExecResult → Configuration
  deriving Repr

/-- Canonical initial configuration for a Script invocation. -/
def initialConfiguration (script : Script) (stack altStack : Stack)
    (flags : ScriptFlags) (txCtx : TxContext) : Configuration :=
  .running {
    stack
    altStack
    script
    pc := 0
    condStack := []
    flags
    txCtx
    pendingUnbalanced := false }

/-- Apply the deferred missing-`ENDIF` error at successful exhaustion while
    preserving any earlier runtime failure. -/
def finishPending (pendingUnbalanced : Bool) (result : ExecResult) : ExecResult :=
  if pendingUnbalanced then finishUnclosedConditional result else result

/-- Update a running state after one active instruction. `pc` counts semantic
    machine transitions; conditional branch projection may skip several source
    elements in a single transition. -/
def MachineState.advance (state : MachineState)
    (script : Script) (stack altStack : Stack)
    (pendingUnbalanced : Bool := state.pendingUnbalanced) : MachineState :=
  { state with
    stack := stack
    altStack := altStack
    script := script
    pc := state.pc + 1
    pendingUnbalanced := pendingUnbalanced }

/-- Execute one semantic machine transition. Every non-conditional modeled
    opcode delegates to the authoritative single-instruction `Eval` relation
    through its executable model. `IF` and `NOTIF` select a strictly smaller
    active script. -/
def step? : Configuration → Option Configuration
  | .halted _ => none
  | .running state =>
      match state.script with
      | [] =>
          some (.halted (finishPending state.pendingUnbalanced
            (.success state.stack state.altStack)))
      | element :: rest =>
          if element.isBranch then
            match state.stack with
            | [] => some (.halted (.failure .stackUnderflow))
            | top :: stackRest =>
                if minimalIfSatisfied state.flags state.txCtx.sigVersion top then
                  match splitConditional rest with
                  | none =>
                      some (.running (state.advance
                        (selectUnclosedConditional rest
                          (element.branchChoice top))
                        stackRest state.altStack true))
                  | some frame =>
                      some (.running (state.advance
                        (frame.select (element.branchChoice top))
                        stackRest state.altStack))
                else
                  some (.halted
                    (.failure (minimalIfError state.txCtx.sigVersion)))
          else
            match evaluate CryptoOracle.model [element] state.stack
                state.altStack state.flags state.txCtx with
            | .failure error => some (.halted (.failure error))
            | .success nextStack nextAltStack =>
                some (.running
                  (state.advance rest nextStack nextAltStack))

/-- Relational view of the executable one-step function. -/
def Step (before after : Configuration) : Prop :=
  step? before = some after

/-- Reflexive transitive closure of the one-step relation. -/
inductive Steps : Configuration → Configuration → Prop where
  | refl (state : Configuration) : Steps state state
  | step {state next final : Configuration} :
      Step state next → Steps next final → Steps state final

/-- A halted result has no successor. -/
@[simp] theorem halted_noStep (result : ExecResult) (next : Configuration) :
    ¬ Step (.halted result) next := by
  simp [Step, step?]

/-- One-step execution is deterministic. -/
theorem Step.deterministic
    {state first second : Configuration}
    (firstStep : Step state first) (secondStep : Step state second) :
    first = second := by
  unfold Step at firstStep secondStep
  rw [firstStep] at secondStep
  exact Option.some.inj secondStep

/-- Remaining-work measure used for termination. Running configurations count
    their remaining script plus the final transition to a halted result. -/
def Configuration.remaining : Configuration → Nat
  | .halted _ => 0
  | .running state => state.script.length + 1

/-- Every semantic step strictly decreases the remaining-work measure. -/
theorem Step.decreases
    {before after : Configuration} (stepped : Step before after) :
    after.remaining < before.remaining := by
  unfold Step at stepped
  cases before with
  | halted result => simp [step?] at stepped
  | running state =>
      cases scriptEq : state.script with
      | nil =>
          simp [step?, scriptEq] at stepped
          subst after
          simp [Configuration.remaining]
      | cons element rest =>
          simp only [step?, scriptEq] at stepped
          split at stepped
          · rename_i branch
            cases stackEq : state.stack with
            | nil =>
                simp [stackEq] at stepped
                subst after
                simp [Configuration.remaining, scriptEq]
            | cons top stackRest =>
                simp only [stackEq] at stepped
                split at stepped
                · rename_i minimal
                  cases splitEq : splitConditional rest with
                  | none =>
                      simp [splitEq] at stepped
                      subst after
                      have selected := selectUnclosedConditional_length_le rest
                        (element.branchChoice top)
                      simp only [Configuration.remaining, MachineState.advance,
                        scriptEq, List.length_cons]
                      omega
                  | some frame =>
                      simp [splitEq] at stepped
                      subst after
                      have selected := frame.select_length_lt splitEq
                        (element.branchChoice top)
                      simp only [Configuration.remaining, MachineState.advance,
                        scriptEq, List.length_cons]
                      omega
                · simp at stepped
                  subst after
                  simp [Configuration.remaining, scriptEq]
          · rename_i ordinary
            cases opcodeResult : evaluate CryptoOracle.model [element]
                state.stack state.altStack state.flags state.txCtx with
            | failure error =>
                simp [opcodeResult] at stepped
                subst after
                simp [Configuration.remaining, scriptEq]
            | success nextStack nextAltStack =>
                simp [opcodeResult] at stepped
                subst after
                simp [Configuration.remaining, MachineState.advance, scriptEq]

/-- The inverse step relation is well-founded; hence the modeled Script subset
    admits no infinite small-step execution. -/
theorem step_wellFounded :
    WellFounded (fun next state => Step state next) := by
  apply WellFounded.intro
  intro state
  induction state using (measure Configuration.remaining).wf.induction with
  | h state ih =>
      apply Acc.intro
      intro next stepped
      exact ih next (stepped.decreases)

/-- Every starting configuration is accessible under the inverse step
    relation, the proposition-level termination statement. -/
theorem step_terminates (state : Configuration) :
    Acc (fun next current => Step current next) state :=
  step_wellFounded.apply state

end LeanMiniscript.Script
