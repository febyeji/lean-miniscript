import LeanMiniscript.Script.ValidationWeight
import LeanMiniscript.Script.RuntimeLimitsProofs

/-! Initial and runtime bounds and oracle refinement for full-witness Tapscript execution. -/

namespace LeanMiniscript.Script

open LeanMiniscript.Bitcoin

/-- Successful full-witness execution certifies both initial argument limits. -/
theorem evaluateTapscript_initialStack
    {oracle : CryptoOracle} {script : Script} {witness : TapscriptWitness}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (success : evaluateTapscript oracle script witness flags ctx = .success stack alt weight) :
    witness.arguments.length ≤ maxStackSize ∧
      ∀ item ∈ witness.arguments, item.size ≤ maxScriptElementSize := by
  apply (checkTapscriptInitialStack_ok_iff witness.arguments).mp
  cases checked : checkTapscriptInitialStack witness.arguments with
  | ok value => cases value; rfl
  | error error =>
      simp only [evaluateTapscript, checked] at success
      repeat' first | contradiction | split at success

/-- Successful full-witness execution respects the final combined stack bound
    and every source push's size, independently of the cryptographic oracle. -/
theorem evaluateTapscript_runtimeBounds
    {oracle : CryptoOracle} {script : Script} {witness : TapscriptWitness}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (success : evaluateTapscript oracle script witness flags ctx = .success stack alt weight) :
    stack.length + alt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  have initial : witness.arguments.reverse.length + ([] : Stack).length ≤ maxStackSize := by
    simpa using (evaluateTapscript_initialStack success).1
  unfold evaluateTapscript at success
  repeat' first
    | contradiction
    | exact evaluateWithRuntimeLimits_bounds initial success
    | split at success
  all_goals dsimp only at success
  all_goals repeat' first
    | contradiction
    | exact evaluateWithRuntimeLimits_bounds initial success
    | split at success

/-- Full-witness metadata binding and transaction-derived hashing preserve
    oracle refinement at the Tapscript execution entry point. -/
theorem evaluateTapscript_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    evaluateTapscript oracle script witness flags ctx =
      evaluateTapscript CryptoOracle.model script witness flags ctx := by
  have compute (script : Script) (stack alt : Stack) (flags : ScriptFlags)
      (ctx : TxContext) (weight : Nat) :
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
        evaluateWithRuntimeLimits CryptoOracle.model script stack alt flags ctx weight :=
    evaluateWithRuntimeLimits_eq_model agreement script stack alt flags ctx weight
  unfold evaluateTapscript
  repeat' first | rfl | split
  all_goals try dsimp only
  all_goals repeat' first | rfl | split
  all_goals apply compute

end LeanMiniscript.Script
