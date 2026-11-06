import LeanMiniscript.Script.RuntimeLimitsProofs
import LeanMiniscript.Script.ControlFlow

namespace LeanMiniscript.Script

/-!
Successful source-order execution preserves the existing branch-projection
semantics. The proof removes one open conditional at a time, then inducts over
the source program. Resource failures need not agree with the older evaluator.
-/

namespace RuntimeProjection

theorem runtime_success_cons
    {oracle : CryptoOracle} {element : ScriptElement} {rest : Script}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (success : evaluateRuntime oracle (element :: rest) state flags ctx =
      .success stack alt weight) :
    ∃ count next, chargeOperations element state flags ctx =
        .ok { state with operationCount := count } ∧ state.operationCount ≤ count ∧
      executeRuntimeElement oracle element { state with operationCount := count } flags ctx =
        .ok next ∧
      next.stack.length + next.altStack.length ≤ maxStackSize ∧
      evaluateRuntime oracle rest next flags ctx = .success stack alt weight := by
  simp only [evaluateRuntime] at success
  cases step : runtimeStep oracle element state flags ctx with
  | error error => simp [step] at success
  | ok next =>
      obtain ⟨count, charging, instruction⟩ := runtimeStep_ok step
      refine ⟨count, next, charging, by simpa using chargeOperations_le charging, ?_,
        runtimeStep_stackBound step, by simpa [step] using success⟩
      unfold runtimeInstruction at instruction
      cases executed : executeRuntimeElement oracle element
          { state with operationCount := count } flags ctx with
      | error error => simp [executed, bind, Except.bind] at instruction
      | ok after =>
          simp only [executed, bind, Except.bind] at instruction
          exact congrArg Except.ok (checkRuntimeStack_ok instruction).1.symm

theorem runtime_cons_success
    {oracle : CryptoOracle} {element : ScriptElement} {rest : Script}
    {state charged next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (charging : chargeOperations element state flags ctx = .ok charged)
    (executed : executeRuntimeElement oracle element charged flags ctx = .ok next)
    (bounded : next.stack.length + next.altStack.length ≤ maxStackSize)
    (tail : evaluateRuntime oracle rest next flags ctx = .success stack alt weight) :
    evaluateRuntime oracle (element :: rest) state flags ctx = .success stack alt weight := by
  simpa [evaluateRuntime, runtimeStep, runtimeInstruction, charging, executed, checkRuntimeStack,
    Nat.not_lt_of_le bounded, bind, Except.bind] using tail

/-- An element that succeeds is no `illegalOpcode` or `truncatedPush`. -/
theorem execute_legal {oracle : CryptoOracle} {element : ScriptElement}
    {state next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    element.isIllegalOpcode = false := by
  cases element with
  | illegalOpcode | truncatedPush =>
      simp [executeRuntimeElement, ScriptElement.pushSize, throw, throwThe,
        MonadExceptOf.throw] at executed
  | _ => rfl

theorem execute_ordinary (element : ScriptElement) (ordinary : NonConditional element)
    (legal : element.isIllegalOpcode = false)
    (oracle : CryptoOracle) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    executeRuntimeElement oracle element state flags ctx = (do
      if element.pushSize > maxScriptElementSize then throw .pushSize
      if state.conditions.all id then
        let weight ← prepareValidationWeight element state.stack flags ctx state.weight
        match evaluate oracle [element.underTimelockFlags flags] state.stack state.altStack
            flags ctx with
        | .failure error => throw error
        | .success stack alt => return { state with stack := stack, altStack := alt, weight := weight }
      else return state) := by
  cases element with
  | pushData => rfl
  | pushNum => rfl
  | badOpcode | nonminimalPush => rfl
  | illegalOpcode | truncatedPush => simp [ScriptElement.isIllegalOpcode] at legal
  | op opcode => cases opcode <;> first | contradiction | rfl

theorem select_ordinary (element : ScriptElement) (ordinary : NonConditional element)
    (depth : Nat) (selected : Bool) (rest : Script) :
    selectConditionalTail depth selected (element :: rest) =
      (selectConditionalTail depth selected rest).map
        (fun tail => if selected then element :: tail else tail) := by
  cases element with
  | pushData => rfl
  | pushNum => rfl
  | badOpcode => rfl
  | illegalOpcode => rfl
  | nonminimalPush => rfl
  | truncatedPush => rfl
  | op opcode => cases opcode <;> first | contradiction | rfl

private theorem execute_push_bound
    {oracle : CryptoOracle} {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    ¬ element.pushSize > maxScriptElementSize := by
  intro exceeded
  simp [executeRuntimeElement, exceeded, bind, Except.bind, pure, Except.pure] at executed

theorem ordinary_conditions
    {oracle : CryptoOracle} {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} (conditions : List Bool)
    (ordinary : NonConditional element)
    (active : conditions.all id = state.conditions.all id)
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    executeRuntimeElement oracle element { state with conditions := conditions } flags ctx =
      .ok { next with conditions := conditions } ∧ next.conditions = state.conditions := by
  have bounded := execute_push_bound executed
  have legal := execute_legal executed
  rw [execute_ordinary element ordinary legal] at executed ⊢
  simp only [bounded, ↓reduceIte, bind, Except.bind, pure, Except.pure] at executed ⊢
  simp only [active]
  split at executed
  · rename_i running
    simp only [running, ↓reduceIte]
    cases charged : prepareValidationWeight element state.stack flags ctx state.weight with
    | error error => simp [charged] at executed
    | ok weight =>
        cases opcode : evaluate oracle [element.underTimelockFlags flags] state.stack
            state.altStack flags ctx with
        | failure error => simp [charged, opcode] at executed
        | success stack alt =>
            simp [charged, opcode] at executed
            subst next
            simp
  · rename_i skipped
    simp only [skipped] at executed ⊢
    cases executed
    exact ⟨rfl, rfl⟩

theorem execute_branch (element : ScriptElement) (branch : element.isBranch = true)
    (oracle : CryptoOracle) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    executeRuntimeElement oracle element state flags ctx = (do
      if state.conditions.all id then
        match state.stack with
        | [] => throw .stackUnderflow
        | top :: rest =>
            if minimalIfSatisfied flags ctx.sigVersion top then
              return { state with
                stack := rest
                conditions := element.branchChoice top :: state.conditions }
            else throw (minimalIfError ctx.sigVersion)
      else return { state with conditions := false :: state.conditions }) := by
  cases element with
  | pushData => contradiction
  | pushNum => contradiction
  | badOpcode => contradiction
  | illegalOpcode => contradiction
  | nonminimalPush => contradiction
  | truncatedPush => contradiction
  | op opcode => cases opcode <;>
      simp_all [ScriptElement.isBranch, executeRuntimeElement, ScriptElement.pushSize,
        maxScriptElementSize, pure, Except.pure] <;> rfl

theorem select_branch (element : ScriptElement) (branch : element.isBranch = true)
    (depth : Nat) (selected : Bool) (rest : Script) :
    selectConditionalTail depth selected (element :: rest) =
      (selectConditionalTail (depth + 1) selected rest).map
        (fun tail => if selected then element :: tail else tail) := by
  cases element with
  | pushData => contradiction
  | pushNum => contradiction
  | badOpcode => contradiction
  | illegalOpcode => contradiction
  | nonminimalPush => contradiction
  | truncatedPush => contradiction
  | op opcode => cases opcode <;> first | contradiction | rfl

theorem branch_conditions
    {oracle : CryptoOracle} {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} (conditions : List Bool)
    (branch : element.isBranch = true)
    (active : conditions.all id = state.conditions.all id)
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    ∃ choice, next.conditions = choice :: state.conditions ∧
      executeRuntimeElement oracle element { state with conditions := conditions } flags ctx =
        .ok { next with conditions := choice :: conditions } := by
  rw [execute_branch element branch] at executed ⊢
  simp only [active]
  split at executed
  · rename_i running
    simp only [running, ↓reduceIte]
    cases stackEq : state.stack with
    | nil => simp [stackEq] at executed
    | cons top rest =>
        simp only [stackEq] at executed
        split at executed
        · rename_i minimal
          cases executed
          exact ⟨element.branchChoice top, rfl, by simp [minimal, pure, Except.pure]⟩
        · contradiction
  · rename_i skipped
    cases executed
    exact ⟨false, rfl, by simp [skipped, pure, Except.pure]⟩

/-- Remove one known open conditional from a successful runtime execution.
    `nested` contains the still-open inner conditions encountered by the scan.
    If the removed branch is inactive, its inner conditions are removed too. -/
private theorem runtime_select_success
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (script : Script) (state : RuntimeState) (nested outer : List Bool) (choice : Bool)
    (success : evaluateRuntime oracle script
      { state with conditions := nested ++ choice :: outer } flags ctx =
        .success stack alt weight) :
    ∃ selected, selectConditionalTail nested.length choice script = some selected ∧
      evaluateRuntime oracle selected
        { state with conditions := (if choice then nested else []) ++ outer } flags ctx =
          .success stack alt weight := by
  induction script generalizing state nested outer choice with
  | nil => simp [evaluateRuntime, finishRuntime] at success
  | cons element rest ih =>
      obtain ⟨count, next, charging, raised, executed, bounded, tail⟩ := runtime_success_cons success
      -- A selected program that skips this element has not charged it.
      have lowered : ∀ {selected : Script} {conditions : List Bool},
          evaluateRuntime oracle selected
            { state with operationCount := count, conditions := conditions } flags ctx =
              .success stack alt weight →
          evaluateRuntime oracle selected { state with conditions := conditions } flags ctx =
            .success stack alt weight :=
        fun result => evaluateRuntime_lower result raised
      by_cases ordinary : NonConditional element
      · cases choice with
        | false =>
            have pushBound := execute_push_bound executed
            rw [execute_ordinary element ordinary (execute_legal executed)] at executed
            simp [pushBound, List.all_append, pure, Except.pure] at executed
            subst next
            obtain ⟨selected, projected, result⟩ :=
              ih { state with operationCount := count } nested outer false tail
            exact ⟨selected, by simpa [select_ordinary element ordinary] using projected,
              lowered result⟩
        | true =>
            obtain ⟨moved, conditions⟩ := ordinary_conditions (nested ++ outer) ordinary
              (by simp [List.all_append]) executed
            have same : { next with conditions := nested ++ true :: outer } = next := by
              exact (congrArg (fun c => { next with conditions := c }) conditions).symm
            obtain ⟨selected, projected, result⟩ := ih next nested outer true (by rw [same]; exact tail)
            refine ⟨element :: selected, by simp [select_ordinary element ordinary, projected], ?_⟩
            exact runtime_cons_success
              (chargeOperations_conditions (state := { state with conditions := nested ++ true :: outer })
                (nested ++ outer) (by simp [List.all_append]) charging)
              moved bounded result
      · by_cases branch : element.isBranch = true
        · cases choice with
          | false =>
              rw [execute_branch element branch] at executed
              simp [List.all_append, pure, Except.pure] at executed
              subst next
              obtain ⟨selected, projected, result⟩ :=
                ih { state with operationCount := count } (false :: nested) outer false tail
              exact ⟨selected, by simpa [select_branch element branch] using projected,
                lowered result⟩
          | true =>
              obtain ⟨inner, conditions, moved⟩ := branch_conditions (nested ++ outer) branch
                (by simp [List.all_append]) executed
              have same : { next with conditions := (inner :: nested) ++ true :: outer } = next := by
                exact (congrArg (fun c => { next with conditions := c }) conditions).symm
              obtain ⟨selected, projected, result⟩ := ih next (inner :: nested) outer true
                (by rw [same]; exact tail)
              refine ⟨element :: selected, ?_, ?_⟩
              · simpa only [select_branch element branch, List.length_cons, ↓reduceIte,
                  Option.map_some] using (congrArg (Option.map (element :: ·)) projected)
              · exact runtime_cons_success
                  (chargeOperations_conditions
                    (state := { state with conditions := nested ++ true :: outer })
                    (nested ++ outer) (by simp [List.all_append]) charging)
                  moved bounded result
        · cases element with
          | pushData => exact False.elim (ordinary trivial)
          | pushNum => exact False.elim (ordinary trivial)
          | badOpcode => exact False.elim (ordinary trivial)
          | illegalOpcode => exact False.elim (ordinary trivial)
          | nonminimalPush => exact False.elim (ordinary trivial)
          | truncatedPush => exact False.elim (ordinary trivial)
          | op opcode =>
              cases opcode <;> simp only [NonConditional, ScriptElement.isBranch] at ordinary branch
              case OP_ELSE =>
                cases nested with
                | nil =>
                    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                      pure, Except.pure] at executed
                    subst next
                    obtain ⟨selected, projected, result⟩ :=
                      ih { state with operationCount := count } [] outer (!choice) tail
                    exact ⟨selected, projected, lowered (by simpa using result)⟩
                | cons inner nested =>
                    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                      pure, Except.pure] at executed
                    subst next
                    obtain ⟨selected, projected, result⟩ :=
                      ih { state with operationCount := count } ((!inner) :: nested) outer choice tail
                    cases choice with
                    | false =>
                        exact ⟨selected, by simpa [selectConditionalTail] using projected,
                          lowered result⟩
                    | true =>
                        refine ⟨.op .OP_ELSE :: selected, by simp [selectConditionalTail] at projected ⊢; exact projected, ?_⟩
                        apply runtime_cons_success
                          (chargeOperations_conditions
                            (state := { state with conditions := inner :: (nested ++ true :: outer) })
                            (inner :: (nested ++ outer)) (by simp [List.all_append]) charging)
                          (next := { state with
                            operationCount := count
                            conditions := (!inner) :: (nested ++ outer) })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact result
              case OP_ENDIF =>
                cases nested with
                | nil =>
                    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                      pure, Except.pure] at executed
                    subst next
                    exact ⟨rest, rfl, lowered (by simpa using tail)⟩
                | cons inner nested =>
                    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                      pure, Except.pure] at executed
                    subst next
                    obtain ⟨selected, projected, result⟩ :=
                      ih { state with operationCount := count } nested outer choice tail
                    cases choice with
                    | false =>
                        exact ⟨selected, by simpa [selectConditionalTail] using projected,
                          lowered result⟩
                    | true =>
                        refine ⟨.op .OP_ENDIF :: selected, by simp [selectConditionalTail, projected], ?_⟩
                        apply runtime_cons_success
                          (chargeOperations_conditions
                            (state := { state with conditions := inner :: (nested ++ true :: outer) })
                            (inner :: (nested ++ outer)) (by simp [List.all_append]) charging)
                          (next := { state with
                            operationCount := count
                            conditions := nested ++ outer })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact result
              all_goals contradiction

private theorem runtime_select_frame
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (script : Script) (state : RuntimeState) (choice : Bool)
    (success : evaluateRuntime oracle script
      { state with conditions := [choice] } flags ctx = .success stack alt weight) :
    ∃ frame, splitConditional script = some frame ∧
      evaluateRuntime oracle (frame.select choice)
        { state with conditions := [] } flags ctx = .success stack alt weight := by
  obtain ⟨selected, projected, result⟩ := runtime_select_success script state [] [] choice success
  simp only [List.length_nil, selectConditionalTail_eq] at projected
  cases split : splitConditional script with
  | none => simp [split] at projected
  | some frame =>
      simp only [split, Option.map_some, Option.some.injEq] at projected
      subst selected
      exact ⟨frame, rfl, by simpa using result⟩

end RuntimeProjection

open RuntimeProjection

/-- Adding source-order runtime limits cannot introduce a successful result.
    Every successful run has exactly the same stacks and remaining signature
    budget in the existing branch-projection evaluator, for every crypto oracle.
    No bound on script length or restriction on conditional nesting is assumed.
    The evaluator always checks timelocks, so both timelock flags are on. -/
theorem evaluateWithRuntimeLimits_erase_success
    {oracle : CryptoOracle} {script : Script}
    {stack alt finalStack finalAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight finalWeight : Nat}
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    evaluateWithValidationWeight oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight := by
  cases script with
  | nil => simpa [evaluateWithRuntimeLimits, evaluateRuntime, finishRuntime,
      evaluateWithValidationWeight] using success
  | cons element rest =>
      obtain ⟨count, next, _, _, executed, bounded, tail⟩ := runtime_success_cons success
      by_cases branch : element.isBranch = true
      · rw [execute_branch element branch] at executed
        simp only [List.all_nil, ↓reduceIte] at executed
        cases stack with
        | nil => contradiction
        | cons top stackRest =>
            simp only at executed
            split at executed
            · rename_i minimal
              cases executed
              obtain ⟨frame, frameSplit, selected⟩ := runtime_select_frame rest
                { stack := stackRest, altStack := alt, weight := weight, operationCount := count }
                (element.branchChoice top) tail
              have preserved := evaluateWithRuntimeLimits_erase_success locktime sequence
                (evaluateRuntime_lower (count := 0) selected (Nat.zero_le _))
              rw [evaluateWithValidationWeight.eq_def]
              simp only [branch, ↓reduceIte, minimal]
              rw [frameSplit]
              exact preserved
            · contradiction
      · by_cases ordinary : NonConditional element
        · have pushBound := execute_push_bound executed
          rw [execute_ordinary element ordinary (execute_legal executed),
            ScriptElement.underTimelockFlags_eq element locktime sequence] at executed
          simp only [pushBound, ↓reduceIte, List.all_nil, bind, Except.bind,
            pure, Except.pure] at executed
          cases charged : prepareValidationWeight element stack flags ctx weight with
          | error error => simp [charged] at executed
          | ok nextWeight =>
              cases opcode : evaluate oracle [element] stack alt flags ctx with
              | failure error => simp [charged, opcode] at executed
              | success nextStack nextAlt =>
                  simp [charged, opcode] at executed
                  subst next
                  have preserved := evaluateWithRuntimeLimits_erase_success locktime sequence
                    (evaluateRuntime_lower (count := 0) tail (Nat.zero_le _))
                  rw [evaluateWithValidationWeight.eq_def]
                  simpa [branch, charged, opcode] using preserved
        · cases element with
          | pushData => exact False.elim (ordinary trivial)
          | pushNum => exact False.elim (ordinary trivial)
          | badOpcode => exact False.elim (ordinary trivial)
          | illegalOpcode => exact False.elim (ordinary trivial)
          | nonminimalPush => exact False.elim (ordinary trivial)
          | truncatedPush => exact False.elim (ordinary trivial)
          | op opcode =>
              cases opcode <;>
                simp_all [NonConditional, ScriptElement.isBranch, executeRuntimeElement,
                  ScriptElement.pushSize, maxScriptElementSize, bind, Except.bind]
termination_by script.length
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [List.length_cons]
  all_goals first
    | omega
    | exact Nat.lt_trans (ConditionalFrame.select_length_lt (by assumption) _) (Nat.lt_succ_self _)

/-- Successful execution in the source-order model refines the existing
    budget-aware relation, including its unchanged remaining weight. -/
theorem RuntimeEval.toWeightedEval
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (evaluated : RuntimeEval script
      { stack := stack, altStack := alt, weight := weight } flags ctx
      (.success finalStack finalAlt finalWeight)) :
    WeightedEval script stack alt flags ctx weight (.success finalStack finalAlt finalWeight) := by
  exact weighted_model_iff.mpr
    (evaluateWithRuntimeLimits_erase_success locktime sequence (runtime_model_iff.mp evaluated))

/-- Resource checks introduce failures, never new successful opcode behavior. -/
theorem RuntimeEval.erase_success
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (evaluated : RuntimeEval script
      { stack := stack, altStack := alt, weight := weight } flags ctx
      (.success finalStack finalAlt finalWeight)) :
    Eval script stack alt flags ctx (.success finalStack finalAlt) := by
  exact (evaluated.toWeightedEval locktime sequence).erase_success

/-- Executable runtime success implies the old relational result whenever the
    supplied oracle agrees with the abstract cryptographic boundary. -/
theorem evaluateWithRuntimeLimits_eval_success
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true)
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    Eval script stack alt flags ctx (.success finalStack finalAlt) := by
  have preserved := evaluateWithRuntimeLimits_erase_success locktime sequence success
  have relational := evaluateWithValidationWeight_sound agreement script stack alt flags ctx weight
  rw [preserved] at relational
  exact relational.erase_success

end LeanMiniscript.Script
