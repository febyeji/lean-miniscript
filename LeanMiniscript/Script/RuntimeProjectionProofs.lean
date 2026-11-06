import LeanMiniscript.Script.RuntimeErasure

namespace LeanMiniscript.Script

open RuntimeProjection

/-- Conditional selection preserves source order and only removes elements. -/
theorem selectConditionalTail_sublist {script selected : Script} {depth : Nat} {choice : Bool}
    (projected : selectConditionalTail depth choice script = some selected) :
    selected.Sublist script := by
  induction script generalizing selected depth choice with
  | nil => simp [selectConditionalTail] at projected
  | cons element rest ih =>
      have recur (depth : Nat) (choice keep : Bool)
          (mapped : (selectConditionalTail depth choice rest).map
            (fun tail => if keep then element :: tail else tail) = some selected) :
          selected.Sublist (element :: rest) := by
        cases found : selectConditionalTail depth choice rest with
        | none => simp [found] at mapped
        | some tail =>
            have sub := ih found
            cases keep <;> simp [found] at mapped <;> subst selected
            · exact sub.cons element
            · exact sub.cons_cons element
      cases element with
      | pushData => exact recur depth choice choice projected
      | pushNum => exact recur depth choice choice projected
      | badOpcode => exact recur depth choice choice projected
      | illegalOpcode => exact recur depth choice choice projected
      | nonminimalPush => exact recur depth choice choice projected
      | truncatedPush => exact recur depth choice choice projected
      | op opcode =>
          cases opcode
          case OP_IF => exact recur (depth + 1) choice choice projected
          case OP_NOTIF => exact recur (depth + 1) choice choice projected
          case OP_ELSE =>
            cases depth with
            | zero => exact (ih projected).cons _
            | succ depth => exact recur (depth + 1) choice choice projected
          case OP_ENDIF =>
            cases depth with
            | zero => cases projected; exact (List.Sublist.refl _).cons _
            | succ depth => exact recur depth choice choice projected
          all_goals exact recur depth choice choice projected

private theorem map_cons_eq_some {source : Option Script} {element : ScriptElement}
    {selected : Script} (mapped : source.map (element :: ·) = some selected) :
    ∃ tail, source = some tail ∧ selected = element :: tail := by
  cases source with
  | none => simp at mapped
  | some tail => exact ⟨tail, rfl, (Option.some.inj mapped).symm⟩

/-- Restore one removed conditional to a successful projected execution.
Every source push must fit, including pushes in inactive segments, and no
source element may be an `illegalOpcode`, which fails there too. The initial
stack bound covers skipped instructions and same-depth delimiters that are
absent from the projection. Outside Tapscript the source operation bound must
fit, since skipped opcodes still count. Nested and repeated ELSE delimiters are
supported. -/
theorem runtime_restore_conditional
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (script selected : Script) (state : RuntimeState)
    (nested outer : List Bool) (choice : Bool)
    (projected : selectConditionalTail nested.length choice script = some selected)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (legal : ∀ element ∈ script, element.isIllegalOpcode = false)
    (bounded : state.stack.length + state.altStack.length ≤ maxStackSize)
    (fits : ctx.sigVersion = .tapscript ∨
      state.operationCount + staticOperationCount script ≤ maxOpsPerScript)
    (success : evaluateRuntime oracle selected
      { state with conditions := (if choice then nested else []) ++ outer } flags ctx =
        .success stack alt weight) :
    evaluateRuntime oracle script
      { state with conditions := nested ++ choice :: outer } flags ctx =
        .success stack alt weight := by
  induction script generalizing selected state nested outer choice with
  | nil => simp [selectConditionalTail] at projected
  | cons element rest ih =>
      have pushBound : ¬ element.pushSize > maxScriptElementSize :=
        Nat.not_lt.mpr (pushes element (by simp))
      have tailPushes : ∀ element ∈ rest, element.pushSize ≤ maxScriptElementSize :=
        fun element member => pushes element (by simp [member])
      have tailLegal : ∀ element ∈ rest, element.isIllegalOpcode = false :=
        fun element member => legal element (by simp [member])
      rw [staticOperationCount_cons] at fits
      have headFits : ∀ conditions : List Bool, ctx.sigVersion = .tapscript ∨
          ({ state with conditions := conditions } : RuntimeState).operationCount +
            element.operationBound ≤ maxOpsPerScript := by
        intro conditions
        rcases fits with version | fits
        · exact .inl version
        · exact .inr (by simp only; omega)
      have restFits : ∀ {count : Nat}, count ≤ state.operationCount + element.operationBound →
          ctx.sigVersion = .tapscript ∨
            ({ state with operationCount := count } : RuntimeState).operationCount +
              staticOperationCount rest ≤ maxOpsPerScript := by
        intro count below
        rcases fits with version | fits
        · exact .inl version
        · exact .inr (by simp only; omega)
      -- The projection skips this element, so it starts from the lower count.
      have raise : ∀ {selected : Script} {conditions : List Bool} {count : Nat},
          selected.Sublist rest → state.operationCount ≤ count →
          count ≤ state.operationCount + element.operationBound →
          evaluateRuntime oracle selected { state with conditions := conditions } flags ctx =
            .success stack alt weight →
          evaluateRuntime oracle selected
            { state with operationCount := count, conditions := conditions } flags ctx =
              .success stack alt weight := by
        intro selected conditions count sub higher below result
        apply evaluateRuntime_raise result higher
        rcases fits with version | fits
        · exact .inl version
        · have := staticOperationCount_sublist sub
          exact .inr (by omega)
      -- A kept element has the projection's charge in the restored conditions.
      have keepFits : ∀ {count : Nat} {conditions : List Bool},
          chargeOperations element { state with conditions := conditions } flags ctx =
            .ok { state with conditions := conditions, operationCount := count } →
          count ≤ state.operationCount + element.operationBound := by
        intro count conditions charging
        simpa using chargeOperations_bound charging
      by_cases ordinary : NonConditional element
      · cases choice with
        | false =>
            have tailProjected : selectConditionalTail nested.length false rest = some selected := by
              simpa [select_ordinary element ordinary] using projected
            obtain ⟨count, above, below, charging⟩ := chargeOperations_inactive
              (state := { state with conditions := nested ++ false :: outer })
              (by simp [List.all_append]) (headFits _)
            apply runtime_cons_success charging
              (next := { state with
                operationCount := count
                conditions := nested ++ false :: outer })
            · simp [execute_ordinary element ordinary (legal element (by simp)), pushBound,
                List.all_append, pure, Except.pure]
            · exact bounded
            · exact ih selected { state with operationCount := count } nested outer false
                tailProjected tailPushes tailLegal bounded (restFits below)
                (raise (selectConditionalTail_sublist tailProjected) above below success)
        | true =>
            obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
              (by simpa [select_ordinary element ordinary] using projected)
            obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
              runtime_success_cons success
            obtain ⟨moved, conditions⟩ := ordinary_conditions (nested ++ true :: outer) ordinary
              (by simp [List.all_append]) executed
            have same : { next with conditions := nested ++ outer } = next := by
              cases next
              simp only at conditions
              cases conditions
              rfl
            have counted := executeRuntimeElement_operationCount_eq executed
            apply runtime_cons_success
              (chargeOperations_conditions (state := { state with conditions := nested ++ outer })
                (nested ++ true :: outer) (by simp [List.all_append]) charging)
              moved nextBound
            apply ih selectedTail next nested outer true tailProjected tailPushes tailLegal
              nextBound
            · rcases restFits (keepFits charging) with version | fits
              · exact .inl version
              · exact .inr (by simp only at counted fits; omega)
            · simpa [same] using tail
      · by_cases branch : element.isBranch = true
        · cases choice with
          | false =>
              have tailProjected : selectConditionalTail (false :: nested).length false rest =
                  some selected := by
                simpa [select_branch element branch] using projected
              obtain ⟨count, above, below, charging⟩ := chargeOperations_inactive
                (state := { state with conditions := nested ++ false :: outer })
                (by simp [List.all_append]) (headFits _)
              apply runtime_cons_success charging
                (next := { state with
                  operationCount := count
                  conditions := false :: (nested ++ false :: outer) })
              · simp [execute_branch element branch, List.all_append, pure, Except.pure]
              · exact bounded
              · exact ih selected { state with operationCount := count } (false :: nested) outer false
                  tailProjected tailPushes tailLegal bounded (restFits below)
                  (raise (selectConditionalTail_sublist tailProjected) above below success)
          | true =>
              obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                (by simpa [select_branch element branch] using projected)
              obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                runtime_success_cons success
              obtain ⟨inner, conditions, moved⟩ := branch_conditions (nested ++ true :: outer) branch
                (by simp [List.all_append]) executed
              have same : { next with conditions := (inner :: nested) ++ outer } = next := by
                cases next
                simp only at conditions
                cases conditions
                rfl
              have counted := executeRuntimeElement_operationCount_eq executed
              apply runtime_cons_success
                (chargeOperations_conditions (state := { state with conditions := nested ++ outer })
                  (nested ++ true :: outer) (by simp [List.all_append]) charging)
                moved nextBound
              apply ih selectedTail next (inner :: nested) outer true
                (by simpa using tailProjected) tailPushes tailLegal nextBound
              · rcases restFits (keepFits charging) with version | fits
                · exact .inl version
                · exact .inr (by simp only at counted fits; omega)
              · exact (congrArg (fun s => evaluateRuntime oracle selectedTail s flags ctx) same).trans tail
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
                    have tailSub := selectConditionalTail_sublist (script := rest) (depth := 0)
                      (choice := !choice) projected
                    obtain ⟨count, above, below, charging⟩ := chargeOperations_quiet
                      (element := .op .OP_ELSE)
                      (state := { state with conditions := [] ++ choice :: outer })
                      (fun _ same => by cases same; rfl) (headFits _)
                    apply runtime_cons_success charging
                      (next := { state with
                        operationCount := count
                        conditions := (!choice) :: outer })
                    · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    · exact bounded
                    · apply ih selected { state with operationCount := count } [] outer (!choice)
                        projected tailPushes tailLegal bounded (restFits below)
                      apply raise tailSub above below
                      simpa using success
                | cons inner nested =>
                    cases choice with
                    | false =>
                        have tailProjected : selectConditionalTail ((!inner) :: nested).length false
                            rest = some selected := by
                          simpa [selectConditionalTail] using projected
                        obtain ⟨count, above, below, charging⟩ := chargeOperations_inactive
                          (state := { state with conditions := (inner :: nested) ++ false :: outer })
                          (by simp [List.all_append]) (headFits _)
                        apply runtime_cons_success charging
                          (next := { state with
                            operationCount := count
                            conditions := (!inner) :: (nested ++ false :: outer) })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact ih selected { state with operationCount := count }
                            ((!inner) :: nested) outer false tailProjected tailPushes tailLegal
                            bounded
                            (restFits below)
                            (raise (selectConditionalTail_sublist tailProjected) above below success)
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                          runtime_success_cons success
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        apply runtime_cons_success
                          (chargeOperations_conditions
                            (state := { state with conditions := inner :: (nested ++ outer) })
                            (inner :: (nested ++ true :: outer)) (by simp [List.all_append]) charging)
                          (next := { state with
                            operationCount := count
                            conditions := (!inner) :: (nested ++ true :: outer) })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · apply ih selectedTail { state with operationCount := count }
                            ((!inner) :: nested) outer true
                            (by simpa using tailProjected) tailPushes tailLegal bounded
                            (restFits (keepFits charging))
                          exact tail
              case OP_ENDIF =>
                cases nested with
                | nil =>
                    have selectedEq : selected = rest := (Option.some.inj projected).symm
                    subst selected
                    obtain ⟨count, above, below, charging⟩ := chargeOperations_quiet
                      (element := .op .OP_ENDIF)
                      (state := { state with conditions := [] ++ choice :: outer })
                      (fun _ same => by cases same; rfl) (headFits _)
                    apply runtime_cons_success charging
                      (next := { state with operationCount := count, conditions := outer })
                    · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    · exact bounded
                    · apply raise (List.Sublist.refl rest) above below
                      simpa using success
                | cons inner nested =>
                    cases choice with
                    | false =>
                        have tailProjected : selectConditionalTail nested.length false rest =
                            some selected := by
                          simpa [selectConditionalTail] using projected
                        obtain ⟨count, above, below, charging⟩ := chargeOperations_inactive
                          (state := { state with conditions := (inner :: nested) ++ false :: outer })
                          (by simp [List.all_append]) (headFits _)
                        apply runtime_cons_success charging
                          (next := { state with
                            operationCount := count
                            conditions := nested ++ false :: outer })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact ih selected { state with operationCount := count } nested outer false
                            tailProjected tailPushes tailLegal bounded (restFits below)
                            (raise (selectConditionalTail_sublist tailProjected) above below success)
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        obtain ⟨count, next, charging, _, executed, nextBound, tail⟩ :=
                          runtime_success_cons success
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        apply runtime_cons_success
                          (chargeOperations_conditions
                            (state := { state with conditions := inner :: (nested ++ outer) })
                            (inner :: (nested ++ true :: outer)) (by simp [List.all_append]) charging)
                          (next := { state with
                            operationCount := count
                            conditions := nested ++ true :: outer })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact ih selectedTail { state with operationCount := count } nested outer true
                            tailProjected tailPushes tailLegal bounded
                            (restFits (keepFits charging)) tail
              all_goals contradiction

end LeanMiniscript.Script
