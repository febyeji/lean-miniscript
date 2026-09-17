import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- The basic fragment cases whose witness algorithms need no numeric
    well-formedness premise. Timelocks have separate theorems below because
    their compiled Script-number must also satisfy the five-byte limit. -/
inductive BasicSatisfactionFragment : CoreFragment → Prop where
  | one : BasicSatisfactionFragment .one
  | cPkK (key : PubKey) : BasicSatisfactionFragment (.c (.pk_k key))

/-- Every witness returned for a supported basic fragment is accepted by its
    compiled script under the environment transaction and modeled flags. -/
theorem satisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfy m env = some witness) :
    Accepts ctx (compile m) witness flags env.txCtx := by
  constructor
  · exact modeled
  cases supported with
  | one =>
      simp [satisfy] at generated
      subst witness
      refine ⟨trueElement, [], ?_, by native_decide⟩
      simpa [compile, compileWithKeyHash, Executes, Witness.toInitialStack,
        scriptNum_one] using
        (Eval.pushNum 1 [] [] [] flags env.txCtx (.success [scriptNum 1] [])
          (Eval.empty [scriptNum 1] [] flags env.txCtx))
  | cPkK key =>
      simp [satisfy] at generated
      obtain ⟨signature, signatureFor, rfl⟩ := generated
      refine ⟨trueElement, [], ?_, by native_decide⟩
      have checked := sound.1 key signature signatureFor
      change Eval [ScriptElement.pushData key.bytes, .op .OP_CHECKSIG]
        [signature] [] flags env.txCtx (.success [trueElement] [])
      exact Eval.pushDataNext
        (Eval.checksigTrue checked Eval.done)

/-- A returned `older` witness is accepted whenever its compiler-produced
    numeric operand is valid and truthy. `WellFormed` supplies these numeric
    premises when this lemma is lifted into the general correctness theorem. -/
theorem satisfy_older_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    Accepts ctx (compile (.older n)) witness flags env.txCtx := by
  simp [satisfy] at generated
  rcases generated with ⟨satisfied, rfl⟩
  constructor
  · exact modeled
  refine ⟨scriptNum n, [], ?_, positive⟩
  simpa [compile, compileWithKeyHash, Executes, Witness.toInitialStack] using
    (Eval.pushNum n [.op .OP_CHECKSEQUENCEVERIFY] [] [] flags env.txCtx
      (.success [scriptNum n] [])
      (Eval.checksequenceverify_success (scriptNum n) n [] [] [] flags env.txCtx
        (.success [scriptNum n] []) decoded (by omega) satisfied
        (Eval.empty [scriptNum n] [] flags env.txCtx)))

/-- Absolute timelocks use the same transaction predicate and numeric boundary
    as relational Script execution. -/
theorem satisfy_after_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    Accepts ctx (compile (.after n)) witness flags env.txCtx := by
  simp [satisfy] at generated
  rcases generated with ⟨satisfied, rfl⟩
  constructor
  · exact modeled
  refine ⟨scriptNum n, [], ?_, positive⟩
  simpa [compile, compileWithKeyHash, Executes, Witness.toInitialStack] using
    (Eval.pushNum n [.op .OP_CHECKLOCKTIMEVERIFY] [] [] flags env.txCtx
      (.success [scriptNum n] [])
      (Eval.checklocktimeverify_success (scriptNum n) n [] [] [] flags env.txCtx
        (.success [scriptNum n] []) decoded (by omega) satisfied
        (Eval.empty [scriptNum n] [] flags env.txCtx)))

/-- Every witness returned for a supported basic dissatisfiable fragment
    executes successfully to a clean false result. -/
theorem dissatisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨ ∃ key, m = .c (.pk_k key))
    (sound : env.Sound)
    (modeled : ModeledContextFlags ctx flags)
    (generated : dissatisfy m env = some witness) :
    Dissatisfies ctx (compile m) witness flags env.txCtx := by
  constructor
  · exact modeled
  rcases supported with rfl | ⟨key, rfl⟩
  · simp [dissatisfy] at generated
    subst witness
    refine ⟨falseElement, [], ?_, by native_decide⟩
    simpa [compile, compileWithKeyHash, Executes, Witness.toInitialStack,
      scriptNum_zero] using
      (Eval.pushNum 0 [] [] [] flags env.txCtx (.success [scriptNum 0] [])
        (Eval.empty [scriptNum 0] [] flags env.txCtx))
  · simp [dissatisfy] at generated
    subst witness
    refine ⟨falseElement, [], ?_, by native_decide⟩
    have rejected := sound.2.1 key
    change Eval [ScriptElement.pushData key.bytes, .op .OP_CHECKSIG]
      [falseElement] [] flags env.txCtx (.success [falseElement] [])
    exact Eval.pushDataNext
      (Eval.checksigFalse rejected (falseElement_nullFailSatisfied flags) Eval.done)

end LeanMiniscript.Miniscript
