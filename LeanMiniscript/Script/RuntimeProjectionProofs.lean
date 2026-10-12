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
Every source push must fit, including pushes in inactive segments. The initial
stack bound covers skipped instructions and same-depth delimiters that are
absent from the projection. Nested and repeated ELSE delimiters are supported. -/
theorem runtime_restore_conditional
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight : Nat}
    (script selected : Script) (state : RuntimeState)
    (nested outer : List Bool) (choice : Bool)
    (projected : selectConditionalTail nested.length choice script = some selected)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (bounded : state.stack.length + state.altStack.length ≤ maxStackSize)
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
      by_cases ordinary : NonConditional element
      · cases choice with
        | false =>
            have tailProjected : selectConditionalTail nested.length false rest = some selected := by
              simpa [select_ordinary element ordinary] using projected
            apply runtime_cons_success (next := { state with conditions := nested ++ false :: outer })
            · simp [execute_ordinary element ordinary, pushBound, List.all_append, pure, Except.pure]
            · exact bounded
            · exact ih selected state nested outer false tailProjected tailPushes bounded success
        | true =>
            obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
              (by simpa [select_ordinary element ordinary] using projected)
            obtain ⟨next, executed, nextBound, tail⟩ := runtime_success_cons success
            obtain ⟨moved, conditions⟩ := ordinary_conditions (nested ++ true :: outer) ordinary
              (by simp [List.all_append]) executed
            have same : { next with conditions := nested ++ outer } = next := by
              cases next
              simp only at conditions
              cases conditions
              rfl
            apply runtime_cons_success moved nextBound
            apply ih selectedTail next nested outer true tailProjected tailPushes nextBound
            simpa [same] using tail
      · by_cases branch : element.isBranch = true
        · cases choice with
          | false =>
              have tailProjected : selectConditionalTail (false :: nested).length false rest =
                  some selected := by
                simpa [select_branch element branch] using projected
              apply runtime_cons_success
                (next := { state with conditions := false :: (nested ++ false :: outer) })
              · simp [execute_branch element branch, List.all_append, pure, Except.pure]
              · exact bounded
              · exact ih selected state (false :: nested) outer false tailProjected tailPushes bounded success
          | true =>
              obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                (by simpa [select_branch element branch] using projected)
              obtain ⟨next, executed, nextBound, tail⟩ := runtime_success_cons success
              obtain ⟨inner, conditions, moved⟩ := branch_conditions (nested ++ true :: outer) branch
                (by simp [List.all_append]) executed
              have same : { next with conditions := (inner :: nested) ++ outer } = next := by
                cases next
                simp only at conditions
                cases conditions
                rfl
              apply runtime_cons_success moved nextBound
              apply ih selectedTail next (inner :: nested) outer true
                (by simpa using tailProjected) tailPushes nextBound
              exact (congrArg (fun s => evaluateRuntime oracle selectedTail s flags ctx) same).trans tail
        · cases element with
          | pushData => exact False.elim (ordinary trivial)
          | pushNum => exact False.elim (ordinary trivial)
          | op opcode =>
              cases opcode <;> simp only [NonConditional, ScriptElement.isBranch] at ordinary branch
              case OP_ELSE =>
                cases nested with
                | nil =>
                    apply runtime_cons_success (next := { state with conditions := (!choice) :: outer })
                    · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    · exact bounded
                    · apply ih selected state [] outer (!choice) projected tailPushes bounded
                      simpa using success
                | cons inner nested =>
                    cases choice with
                    | false =>
                        apply runtime_cons_success
                          (next := { state with conditions := (!inner) :: (nested ++ false :: outer) })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · apply ih selected state ((!inner) :: nested) outer false
                            (by simpa [selectConditionalTail] using projected) tailPushes bounded
                          exact success
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        obtain ⟨next, executed, nextBound, tail⟩ := runtime_success_cons success
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        apply runtime_cons_success
                          (next := { state with conditions := (!inner) :: (nested ++ true :: outer) })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · apply ih selectedTail state ((!inner) :: nested) outer true
                            (by simpa using tailProjected) tailPushes bounded
                          exact tail
              case OP_ENDIF =>
                cases nested with
                | nil =>
                    have selectedEq : selected = rest := (Option.some.inj projected).symm
                    subst selected
                    apply runtime_cons_success (next := { state with conditions := outer })
                    · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                        pure, Except.pure]
                    · exact bounded
                    · simpa using success
                | cons inner nested =>
                    cases choice with
                    | false =>
                        apply runtime_cons_success
                          (next := { state with conditions := nested ++ false :: outer })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · apply ih selected state nested outer false
                            (by simpa [selectConditionalTail] using projected) tailPushes bounded
                          exact success
                    | true =>
                        obtain ⟨selectedTail, tailProjected, rfl⟩ := map_cons_eq_some
                          (by simpa [selectConditionalTail] using projected)
                        obtain ⟨next, executed, nextBound, tail⟩ := runtime_success_cons success
                        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                          pure, Except.pure] at executed
                        subst next
                        apply runtime_cons_success
                          (next := { state with conditions := nested ++ true :: outer })
                        · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
                            pure, Except.pure]
                        · exact bounded
                        · exact ih selectedTail state nested outer true tailProjected tailPushes bounded tail
              all_goals contradiction

end LeanMiniscript.Script
