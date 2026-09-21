import LeanMiniscript.Script.SmallStep
import LeanMiniscript.Script.BigStep
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Script

/-! # Small-step/big-step equivalence -/

/-- A terminating small-step execution reaches the requested halted result. -/
def RunsTo (initial : Configuration) (result : ExecResult) : Prop :=
  Steps initial (.halted result)

/-- Semantic result denoted by a machine configuration. The definition uses
    the existing executable characterization of `Eval`; it is used only as a
    proof invariant for adjacent small steps. -/
def Configuration.denote : Configuration → ExecResult
  | .halted result => result
  | .running state =>
      finishPending state.pendingUnbalanced
        (evaluate CryptoOracle.model state.script state.stack state.altStack
          state.flags state.txCtx)

/-- Deferred unbalanced-conditional handling is idempotent. -/
@[simp] theorem finishPending_true (result : ExecResult) :
    finishPending true result = finishUnclosedConditional result := by
  rfl

@[simp] theorem finishPending_false (result : ExecResult) :
    finishPending false result = result := by
  rfl

theorem finishPending_unclosed (pending : Bool) (result : ExecResult) :
    finishPending pending (finishUnclosedConditional result) =
      finishPending true result := by
  cases pending <;> cases result <;>
    rfl

@[simp] theorem finishPending_failure (pending : Bool) (error : ScriptError) :
    finishPending pending (.failure error) = .failure error := by
  cases pending <;> rfl

/-- Executing a non-conditional head instruction is exactly single-opcode
    evaluation followed by the literal tail on success. -/
theorem evaluate_cons_of_not_branch
    (element : ScriptElement) (rest : Script) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext)
    (ordinary : element.isBranch = false) :
    evaluate CryptoOracle.model (element :: rest) stack altStack flags ctx =
      match evaluate CryptoOracle.model [element] stack altStack flags ctx with
      | .failure error => .failure error
      | .success nextStack nextAltStack =>
          evaluate CryptoOracle.model rest nextStack nextAltStack flags ctx := by
  rw [evaluate.eq_def CryptoOracle.model (element :: rest) stack altStack flags ctx,
    evaluate.eq_def CryptoOracle.model [element] stack altStack flags ctx]
  cases element with
  | pushData data => simp only [evaluate.eq_1]
  | pushNum value => simp only [evaluate.eq_1]
  | op opcode =>
      cases opcode <;>
        simp_all [ScriptElement.isBranch, evaluate.eq_1]
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all
      all_goals (try split) <;> try simp_all

/-- The generic branch helpers used by `step?` reproduce the two concrete
    `OP_IF`/`OP_NOTIF` equations of the evaluator. -/
theorem evaluate_cons_of_branch
    (element : ScriptElement) (rest : Script) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext)
    (branch : element.isBranch = true) :
    evaluate CryptoOracle.model (element :: rest) stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if minimalIfSatisfied flags ctx.sigVersion top then
            match splitConditional rest with
            | none => finishUnclosedConditional
                (evaluate CryptoOracle.model
                  (selectUnclosedConditional rest (element.branchChoice top))
                  stackRest altStack flags ctx)
            | some frame =>
                evaluate CryptoOracle.model
                  (frame.select (element.branchChoice top))
                  stackRest altStack flags ctx
          else .failure (minimalIfError ctx.sigVersion) := by
  rw [evaluate.eq_def CryptoOracle.model (element :: rest) stack altStack flags ctx]
  cases element with
  | pushData => simp [ScriptElement.isBranch] at branch
  | pushNum => simp [ScriptElement.isBranch] at branch
  | op opcode =>
      cases opcode <;>
        simp_all [ScriptElement.isBranch, ScriptElement.branchChoice]
      case OP_IF | OP_NOTIF =>
        cases stack with
        | nil => rfl
        | cons top stackRest =>
            by_cases minimal : minimalIfSatisfied flags ctx.sigVersion top
            · simp only [minimal, ↓reduceIte]
              cases splitEq : splitConditional rest <;> simp
            · simp [minimal]

/-- One small step preserves the denoted big-step result. -/
theorem Step.preservesDenote
    {before after : Configuration} (stepped : Step before after) :
    before.denote = after.denote := by
  unfold Step at stepped
  cases before with
  | halted result => simp [step?] at stepped
  | running state =>
      cases scriptEq : state.script with
      | nil =>
          simp [step?, scriptEq] at stepped
          subst after
          simp [Configuration.denote, scriptEq, evaluate]
      | cons element rest =>
          simp only [step?, scriptEq] at stepped
          change finishPending state.pendingUnbalanced
            (evaluate CryptoOracle.model state.script state.stack state.altStack
              state.flags state.txCtx) = after.denote
          rw [scriptEq]
          split at stepped
          · rename_i branch
            rw [evaluate_cons_of_branch element rest state.stack state.altStack
              state.flags state.txCtx branch]
            cases stackEq : state.stack with
            | nil =>
                simp [stackEq] at stepped
                subst after
                simp [Configuration.denote]
            | cons top stackRest =>
                simp only [stackEq] at stepped
                split at stepped
                · rename_i minimal
                  simp only [minimal, ↓reduceIte]
                  cases splitEq : splitConditional rest with
                  | none =>
                      simp [splitEq] at stepped
                      subst after
                      simp only [Configuration.denote, MachineState.advance]
                      exact finishPending_unclosed state.pendingUnbalanced
                        (evaluate CryptoOracle.model
                          (selectUnclosedConditional rest
                            (element.branchChoice top))
                          stackRest state.altStack state.flags state.txCtx)
                  | some frame =>
                      simp [splitEq] at stepped
                      subst after
                      simp [Configuration.denote, MachineState.advance]
                · rename_i nonMinimal
                  simp at stepped
                  subst after
                  simp [Configuration.denote, nonMinimal]
          · rename_i ordinary
            have ordinaryEq : element.isBranch = false := by
              cases branchEq : element.isBranch <;> simp_all
            rw [evaluate_cons_of_not_branch element rest state.stack
              state.altStack state.flags state.txCtx ordinaryEq]
            cases opcodeResult : evaluate CryptoOracle.model [element]
                state.stack state.altStack state.flags state.txCtx with
            | failure error =>
                simp [opcodeResult] at stepped
                subst after
                simp [Configuration.denote]
            | success nextStack nextAltStack =>
                simp [opcodeResult] at stepped
                subst after
                rfl

/-- Multi-step execution preserves the denoted result. -/
theorem Steps.preservesDenote
    {before after : Configuration} (steps : Steps before after) :
    before.denote = after.denote := by
  induction steps with
  | refl => rfl
  | step head tail ih => exact head.preservesDenote.trans ih

/-- Every running configuration has exactly one next transition. -/
theorem running_has_step (state : MachineState) :
    ∃ next, Step (.running state) next := by
  unfold Step
  cases scriptEq : state.script with
  | nil =>
      refine ⟨.halted (finishPending state.pendingUnbalanced
        (.success state.stack state.altStack)), ?_⟩
      simp [step?, scriptEq]
  | cons element rest =>
      simp only [step?, scriptEq]
      split
      · cases stackEq : state.stack with
        | nil => simp
        | cons top stackRest =>
            by_cases minimal : minimalIfSatisfied state.flags
                state.txCtx.sigVersion top
            · simp only [minimal, ↓reduceIte]
              cases splitEq : splitConditional rest <;> simp
            · simp only [minimal, ↓reduceIte]
              refine ⟨.halted
                (.failure (minimalIfError state.txCtx.sigVersion)), ?_⟩
              rfl
      · cases opcodeResult : evaluate CryptoOracle.model [element]
          state.stack state.altStack state.flags state.txCtx <;>
          simp

/-- Well-founded descent of `step?` reaches a halted configuration from every
    starting configuration. -/
theorem reaches_halted (initial : Configuration) :
    ∃ result, RunsTo initial result := by
  induction initial using step_wellFounded.induction with
  | h initial ih =>
      cases initial with
      | halted result => exact ⟨result, .refl _⟩
      | running state =>
          obtain ⟨next, stepped⟩ := running_has_step state
          obtain ⟨result, tail⟩ := ih next stepped
          exact ⟨result, .step stepped tail⟩

/-- Every terminating small-step run induces the corresponding big-step
    evaluation. -/
theorem smallStep_to_bigStep
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (steps : RunsTo (initialConfiguration script stack altStack flags ctx)
      result) :
    Eval script stack altStack flags ctx result := by
  have preserved := steps.preservesDenote
  simp [Configuration.denote, initialConfiguration] at preserved
  exact evaluate_model_iff.mpr preserved

/-- Every big-step derivation has a terminating small-step run with the same
    result. -/
theorem bigStep_to_smallStep
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (evaluated : Eval script stack altStack flags ctx result) :
    RunsTo (initialConfiguration script stack altStack flags ctx) result := by
  obtain ⟨smallResult, steps⟩ :=
    reaches_halted (initialConfiguration script stack altStack flags ctx)
  have preserved := steps.preservesDenote
  have computed := evaluate_eq_of_eval CryptoOracle.model_refines evaluated
  simp [Configuration.denote, initialConfiguration, computed] at preserved
  cases preserved
  exact steps

/-- Small-step termination and relational big-step evaluation characterize the
    same result for every modeled Script. -/
theorem smallStep_bigStep_iff
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult} :
    RunsTo (initialConfiguration script stack altStack flags ctx) result ↔
      Eval script stack altStack flags ctx result :=
  ⟨smallStep_to_bigStep, bigStep_to_smallStep⟩

/-- Core compiler output inherits the generic semantic equivalence. -/
theorem compile_smallStep_bigStep_iff
    (fragment : Miniscript.CoreFragment) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    RunsTo
        (initialConfiguration (Miniscript.compile fragment) stack altStack
          flags ctx)
        result ↔
      Eval (Miniscript.compile fragment) stack altStack flags ctx result :=
  smallStep_bigStep_iff

/-- Surface compiler output uses the same theorem after its core desugaring
    boundary. -/
theorem compileSurface_smallStep_bigStep_iff
    (fragment : Miniscript.SurfaceFragment) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    RunsTo
        (initialConfiguration (Miniscript.compileSurface fragment) stack
          altStack flags ctx)
        result ↔
      Eval (Miniscript.compileSurface fragment) stack altStack flags ctx
        result :=
  smallStep_bigStep_iff

end LeanMiniscript.Script
