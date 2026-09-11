import LeanMiniscript.Script.BigStep
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Script

private def flags : ScriptFlags := {}
private def tx : TxContext := ⟨0, 0, ⟨#[]⟩⟩

/-- The nested ELSE/ENDIF belong to the inner NOTIF, not the outer IF. -/
private def nested : Script :=
  [.op .OP_IF, .pushNum 0, .op .OP_NOTIF, .pushNum 7,
   .op .OP_ELSE, .pushNum 8, .op .OP_ENDIF,
   .op .OP_ELSE, .op .OP_VERIFY, .op .OP_ENDIF, .pushNum 9]

example : splitConditional true nested.tail =
    ⟨[.pushNum 0, .op .OP_NOTIF, .pushNum 7, .op .OP_ELSE,
      .pushNum 8, .op .OP_ENDIF], [.pushNum 9], true⟩ := by rfl

example : Eval nested [trueElement] [] flags tx
    (.success [scriptNum 9, scriptNum 7] []) := by
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.pushNum
  apply Eval.notifNext _ (Or.inr (by native_decide)) rfl rfl
  exact Eval.pushNum _ _ _ _ _ _ _ (Eval.pushNum _ _ _ _ _ _ _ Eval.done)

/-- A skipped nested conditional consumes no selector and does not VERIFY. -/
example : Eval
    [.op .OP_IF, .op .OP_NOTIF, .op .OP_VERIFY, .op .OP_ENDIF,
      .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF]
    [falseElement] [] flags tx (.success [scriptNum 1] []) := by
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.pushNum
  exact Eval.done

/-- An ENDIF from a later conditional cannot close the first conditional. The
    old unconstrained false-branch rule also admitted an empty final stack. -/
private def adjacent : Script :=
  [.op .OP_IF, .pushNum 1, .op .OP_ENDIF, .pushNum 2,
   .op .OP_IF, .pushNum 3, .op .OP_ENDIF]

example : splitConditional false adjacent.tail =
    ⟨[], [.pushNum 2, .op .OP_IF, .pushNum 3, .op .OP_ENDIF], true⟩ := by rfl

-- Relaxed MINIMALIF permits the second selector (encoded 2).
example : Eval adjacent [falseElement] [] { flags with minimalIf := false } tx
    (.success [scriptNum 3] []) := by
  apply Eval.ifNext _ (Or.inl rfl) rfl rfl
  apply Eval.pushNum
  apply Eval.ifNext _ (Or.inl rfl) rfl rfl
  apply Eval.pushNum
  exact Eval.done

/-- The old rule could skip through the later ENDIF and return an empty stack.
    Inversion through the splitter now forces the expected result. -/
theorem adjacent_result {result : ExecResult}
    (evaluated : Eval adjacent [falseElement] []
      { flags with minimalIf := false } tx result) :
    result = .success [scriptNum 3] [] := by
  have first := (Eval.conditional_closed_iff (block := ⟨[],
    [.pushNum 2, .op .OP_IF, .pushNum 3, .op .OP_ENDIF], true⟩)
    (Or.inl rfl) (Or.inl rfl) rfl rfl).mp evaluated
  cases first
  rename_i second
  have last := (Eval.conditional_closed_iff
    (block := ⟨[.pushNum 3], [], true⟩)
    (Or.inl rfl) (Or.inl rfl) rfl rfl).mp second
  cases last
  rename_i done
  cases done
  rfl

/-- NOTIF's false branch is selected by a true argument. -/
example : Eval [.op .OP_NOTIF, .pushNum 1, .op .OP_ELSE,
    .pushNum 2, .op .OP_ENDIF] [trueElement] [] flags tx
    (.success [scriptNum 2] []) := by
  apply Eval.notifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.pushNum
  exact Eval.done

/-- Both empty branches are valid. -/
example : Eval [.op .OP_IF, .op .OP_ELSE, .op .OP_ENDIF]
    [trueElement] [] flags tx (.success [] []) := by
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  exact Eval.done

/-- Repeated ELSE toggles selection; it is not a malformed-control-flow error. -/
example : Eval [.op .OP_IF, .pushNum 1, .op .OP_ELSE, .pushNum 2,
    .op .OP_ELSE, .pushNum 3, .op .OP_ENDIF]
    [trueElement] [] flags tx (.success [scriptNum 3, scriptNum 1] []) := by
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.pushNum
  apply Eval.pushNum
  exact Eval.done

/-- Missing ENDIF is reported on reaching the end of selected code. -/
example : Eval [.op .OP_IF, .pushNum 1] [trueElement] [] flags tx
    (.failure .unbalancedConditional) := by
  apply Eval.conditional_unclosed .OP_IF _ _ _ _ _ _ (Or.inl rfl)
    (Or.inr (by native_decide)) _ rfl rfl [scriptNum 1] []
  apply Eval.pushNum
  exact Eval.done

/-- Missing nested ENDIF in skipped code is still a structural error. -/
example : Eval [.op .OP_IF, .op .OP_NOTIF, .op .OP_VERIFY]
    [falseElement] [] flags tx (.failure .unbalancedConditional) := by
  apply Eval.conditional_unclosed .OP_IF _ _ _ _ _ _ (Or.inl rfl)
    (Or.inr (by native_decide)) _ rfl rfl [] []
  exact Eval.done

/-- Earlier execution failure takes precedence over a missing ENDIF. -/
example : Eval [.op .OP_IF, .op .OP_VERIFY] [trueElement] [] flags tx
    (.failure .stackUnderflow) := by
  apply Eval.conditional_unclosed_error .OP_IF _ _ _ _ _ _ (Or.inl rfl)
    (Or.inr (by native_decide)) _ rfl rfl .stackUnderflow
  exact Eval.fixedArityStackUnderflow rfl (by decide)

/-- MINIMALIF is checked before malformed structure; both IF and NOTIF do so. -/
example : Eval [.op .OP_IF] [nonMinimalTruthyElement] [] flags tx
    (.failure .minimalIf) :=
  Eval.conditional_minimalif_failure _ _ _ _ _ _ _ (Or.inl rfl)
    rfl nonMinimalTruthyElement_not_minimalIfArg

example : Eval [.op .OP_NOTIF] [nonMinimalTruthyElement] [] flags tx
    (.failure .minimalIf) :=
  Eval.conditional_minimalif_failure _ _ _ _ _ _ _ (Or.inr rfl)
    rfl nonMinimalTruthyElement_not_minimalIfArg

/-- An absent selector fails before conditional structure is inspected. -/
example : Eval [.op .OP_IF] [] [] flags tx (.failure .stackUnderflow) :=
  Eval.fixedArityStackUnderflow rfl (by decide)

example : Eval [.op .OP_ELSE] [] [] flags tx (.failure .unbalancedConditional) :=
  Eval.unexpected_conditional _ _ _ _ _ _ (Or.inl rfl)

example : Eval [.op .OP_ENDIF] [] [] flags tx (.failure .unbalancedConditional) :=
  Eval.unexpected_conditional _ _ _ _ _ _ (Or.inr rfl)

/-- Compiler-generated nested or_i follows the same branch selection. -/
example : Eval
    (LeanMiniscript.Miniscript.compile (.or_i (.or_i .one .zero) .zero))
    [trueElement, trueElement] [] flags tx (.success [scriptNum 1] []) := by
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.ifNext _ (Or.inr (by native_decide)) rfl rfl
  apply Eval.pushNum
  exact Eval.done

end LeanMiniscript.Script
