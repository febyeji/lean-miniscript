import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-! # Conditional parsing and execution fixtures -/

private def fixtureFlags : ScriptFlags := {}

private def fixtureTxContext : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def innerTail : Script :=
  [.pushNum 7, .op .OP_ELSE, .pushNum 8, .op .OP_ENDIF]

private def innerFrame : ConditionalFrame where
  branches := [[.pushNum 7], [.pushNum 8]]
  after := []

private def outerTail : Script :=
  [.pushNum 0, .op .OP_NOTIF] ++ innerTail ++
    [.op .OP_ELSE, .pushNum 9, .op .OP_ENDIF]

private def outerFrame : ConditionalFrame where
  branches :=
    [[.pushNum 0, .op .OP_NOTIF] ++ innerTail, [.pushNum 9]]
  after := []

/-- The outer split ignores nested ELSE/ENDIF delimiters. -/
example : splitConditional outerTail = some outerFrame := by
  rfl

/-- The nested NOTIF is split independently after its branch is selected. -/
example : splitConditional innerTail = some innerFrame := by
  rfl

private def repeatedElseTail : Script :=
  [.pushNum 1, .op .OP_ELSE, .pushNum 2, .op .OP_ELSE, .pushNum 3,
    .op .OP_ENDIF, .pushNum 4]

private def repeatedElseFrame : ConditionalFrame where
  branches := [[.pushNum 1], [.pushNum 2], [.pushNum 3]]
  after := [.pushNum 4]

example : splitConditional repeatedElseTail = some repeatedElseFrame := by
  rfl

/-- Bitcoin Core toggles the execution flag at every same-depth ELSE. -/
example : repeatedElseFrame.select true =
    [.pushNum 1, .pushNum 3, .pushNum 4] := by
  rfl

example : repeatedElseFrame.select false = [.pushNum 2, .pushNum 4] := by
  rfl

/-- A selected outer branch can contain and execute its own conditional. -/
example : Eval (.op .OP_IF :: outerTail) [trueElement] []
    fixtureFlags fixtureTxContext (.success [scriptNum 7] []) := by
  apply Eval.if_execute (frame := outerFrame)
  · rfl
  · exact Or.inr trueElement_minimalIfArg
  · change Eval ([.pushNum 0, .op .OP_NOTIF] ++ innerTail) [] []
      fixtureFlags fixtureTxContext (.success [scriptNum 7] [])
    apply Eval.pushNum
    apply Eval.notif_execute (frame := innerFrame)
    · rfl
    · exact Or.inr (by simpa [scriptNum_zero] using falseElement_minimalIfArg)
    · change Eval [.pushNum 7] [] [] fixtureFlags fixtureTxContext
        (.success [scriptNum 7] [])
      apply Eval.pushNum
      exact Eval.empty [scriptNum 7] [] fixtureFlags fixtureTxContext

/-- A leading conditional with no matching ENDIF fails explicitly. -/
example : Eval [.op .OP_IF, .pushNum 1] [trueElement] []
    fixtureFlags fixtureTxContext (.failure .unbalancedConditional) := by
  apply Eval.if_unbalanced
  · rfl
  · exact Or.inr trueElement_minimalIfArg

example : ∀ result,
    Eval [.op .OP_IF, .pushNum 1] [trueElement] []
      fixtureFlags fixtureTxContext result →
    result = .failure .unbalancedConditional := by
  intro result evaluated
  exact Eval.ifUnbalanced_result rfl (Or.inr trueElement_minimalIfArg) evaluated

example : Eval [.op .OP_NOTIF, .pushNum 1] [falseElement] []
    fixtureFlags fixtureTxContext (.failure .unbalancedConditional) := by
  apply Eval.notif_unbalanced
  · rfl
  · exact Or.inr falseElement_minimalIfArg

/-- ELSE and ENDIF outside any conditional frame are unbalanced. -/
example : Eval [.op .OP_ELSE] [] [] fixtureFlags fixtureTxContext
    (.failure .unbalancedConditional) := by
  exact Eval.else_unbalanced [] [] [] fixtureFlags fixtureTxContext

example : Eval [.op .OP_ENDIF] [] [] fixtureFlags fixtureTxContext
    (.failure .unbalancedConditional) := by
  exact Eval.endif_unbalanced [] [] [] fixtureFlags fixtureTxContext

example : ∀ result,
    Eval [.op .OP_ELSE] [] [] fixtureFlags fixtureTxContext result →
    result = .failure .unbalancedConditional := by
  intro result evaluated
  exact Eval.elseUnbalanced_result evaluated

end LeanMiniscript.Script
