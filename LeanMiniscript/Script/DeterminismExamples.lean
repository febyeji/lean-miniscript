import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-! # Big-step result-determinism fixtures -/

private def fixtureFlags : ScriptFlags := {}

private def fixtureTxContext : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def conditionalTail : Script :=
  [.pushNum 1, .op .OP_ELSE, .pushNum 0, .op .OP_ENDIF]

private def conditionalFrame : ConditionalFrame where
  branches := [[.pushNum 1], [.pushNum 0]]
  after := []

private theorem conditionalSuccess :
    Eval (.op .OP_IF :: conditionalTail) [trueElement] []
      fixtureFlags fixtureTxContext (.success [scriptNum 1] []) := by
  apply Eval.if_execute (frame := conditionalFrame)
  · rfl
  · exact Or.inr trueElement_minimalIfArg
  · change Eval [.pushNum 1] [] [] fixtureFlags fixtureTxContext
      (.success [scriptNum 1] [])
    apply Eval.pushNum
    exact Eval.empty [scriptNum 1] [] fixtureFlags fixtureTxContext

/-- A conditional execution cannot produce a result different from its known
    successful result. -/
example {result : ExecResult}
    (evaluated : Eval (.op .OP_IF :: conditionalTail) [trueElement] []
      fixtureFlags fixtureTxContext result) :
    result = .success [scriptNum 1] [] :=
  Eval.result_unique evaluated conditionalSuccess

private theorem verifyFailure :
    Eval [.op .OP_VERIFY] [falseElement] [] fixtureFlags fixtureTxContext
      (.failure .verify) :=
  Eval.verify_failure falseElement [] [] [] fixtureFlags fixtureTxContext
    (by native_decide)

/-- Terminal failures are covered by the same global result-uniqueness
    theorem as successful executions. -/
example {result : ExecResult}
    (evaluated : Eval [.op .OP_VERIFY] [falseElement] []
      fixtureFlags fixtureTxContext result) :
    result = .failure .verify :=
  Eval.result_unique evaluated verifyFailure

end LeanMiniscript.Script
