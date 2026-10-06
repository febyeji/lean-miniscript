import LeanMiniscript.Script.ValidationWeightCore
import LeanMiniscript.Script.EvaluatorProofs

/-! Validation-weight bounds, refinement and erasure proofs. -/

namespace LeanMiniscript.Script

theorem debitValidationWeight_nonincreasing
    {signature : StackElement} {before after : Nat}
    (charged : debitValidationWeight signature before = .ok after) :
    after ≤ before := by
  unfold debitValidationWeight at charged
  split at charged
  · cases charged; omega
  · split at charged
    · contradiction
    · cases charged; omega


theorem WeightedResult.checkAcceptance_ok_iff (result : WeightedResult) (weight : Nat) :
    result.checkAcceptance = .ok weight ↔
      ∃ top alt, result = .success [top] alt weight ∧ castToBool top = true := by
  cases result with
  | failure => simp [checkAcceptance]
  | success stack alt remaining =>
      cases stack with
      | nil => simp [checkAcceptance]
      | cons top rest =>
          cases rest with
          | cons => simp [checkAcceptance]
          | nil =>
              cases truth : castToBool top <;> simp [checkAcceptance, truth, and_assoc]


theorem evaluateWithValidationWeight_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {result : WeightedResult}
    (evaluated : WeightedEval script stack alt flags ctx weight result) :
    evaluateWithValidationWeight oracle script stack alt flags ctx weight = result := by
  induction evaluated <;> rw [evaluateWithValidationWeight.eq_def]
  case step ordinary charged opcode next ih =>
    simp [ordinary, charged, evaluate_eq_of_eval agreement opcode, ih]
  case chargeError ordinary charged => simp [ordinary, charged]
  case opcodeError ordinary charged opcode =>
    simp [ordinary, charged, evaluate_eq_of_eval agreement opcode]
  case branchUnderflow branch => simp [branch]
  case branchMinimal branch minimal => simp [branch, minimal]
  case branch branch minimal split next ih =>
    simp only [branch, ↓reduceIte, minimal]
    rw [split]
    exact ih
  case unclosed branch minimal split next ih =>
    simp only [branch, ↓reduceIte, minimal]
    rw [split]
    simp only [ih]

theorem evaluateWithValidationWeight_sound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    WeightedEval script stack alt flags ctx weight
      (evaluateWithValidationWeight oracle script stack alt flags ctx weight) := by
  have general : ∀ n, ∀ (script : Script), script.length = n → ∀ stack alt weight,
      WeightedEval script stack alt flags ctx weight
        (evaluateWithValidationWeight oracle script stack alt flags ctx weight) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro script lengthEq stack alt weight
      have recurse := fun (smaller : Script) (lt : smaller.length < script.length) =>
        ih smaller.length (by omega) smaller rfl
      cases script with
      | nil => simpa only [evaluateWithValidationWeight.eq_1] using
          (WeightedEval.empty stack alt flags ctx weight)
      | cons element rest =>
          rw [evaluateWithValidationWeight.eq_def]
          cases hBranch : element.isBranch with
          | true =>
              simp only [hBranch, ↓reduceIte]
              cases stack with
              | nil => exact .branchUnderflow hBranch
              | cons top stackRest =>
                  by_cases minimal : minimalIfSatisfied flags ctx.sigVersion top
                  · simp only [minimal, ↓reduceIte]
                    cases split : splitConditional rest with
                    | none =>
                        exact .unclosed hBranch minimal split
                          (recurse _ (by
                            have smaller := selectUnclosedConditional_length_le rest (element.branchChoice top)
                            simp only [List.length_cons]; omega) stackRest alt weight)
                    | some frame =>
                        exact .branch hBranch minimal split
                          (recurse _ (by
                            have smaller := ConditionalFrame.select_length_lt split (element.branchChoice top)
                            simp only [List.length_cons]; omega) stackRest alt weight)
                  · simp only [minimal, ↓reduceIte]
                    exact .branchMinimal hBranch minimal
          | false =>
              simp only [hBranch, Bool.false_eq_true, ↓reduceIte]
              cases charged : prepareValidationWeight element stack flags ctx weight with
              | error error =>
                  exact .chargeError hBranch charged
              | ok nextWeight =>
                  have opcode := evaluate_sound agreement [element] stack alt flags ctx
                  cases computed : evaluate oracle [element] stack alt flags ctx with
                  | failure error =>
                      rw [computed] at opcode
                      exact .opcodeError hBranch charged opcode
                  | success nextStack nextAlt =>
                      rw [computed] at opcode
                      exact .step hBranch charged opcode
                        (recurse rest (by simp) nextStack nextAlt nextWeight)

  exact general script.length script rfl stack alt weight

theorem weighted_model_iff
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {result : WeightedResult} :
    WeightedEval script stack alt flags ctx weight result ↔
      evaluateWithValidationWeight CryptoOracle.model script stack alt flags ctx weight = result := by
  constructor
  · exact evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines
  · intro computed
    rw [← computed]
    exact evaluateWithValidationWeight_sound CryptoOracle.model_refines script stack alt flags ctx weight

theorem WeightedEval.deterministic
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {first second : WeightedResult}
    (a : WeightedEval script stack alt flags ctx weight first)
    (b : WeightedEval script stack alt flags ctx weight second) : first = second := by
  have ha := evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines a
  have hb := evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines b
  exact ha.symm.trans hb

/-- Successful budgeted execution preserves the resource-free opcode model.
    Budget exhaustion introduces an additional failure, never a new success. -/
theorem WeightedEval.erase_success
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (evaluated : WeightedEval script stack alt flags ctx weight
      (.success finalStack finalAlt finalWeight)) :
    Eval script stack alt flags ctx (.success finalStack finalAlt) := by
  generalize resultEq : WeightedResult.success finalStack finalAlt finalWeight = result at evaluated
  induction evaluated with
  | empty => cases resultEq; exact .empty _ _ _ _
  | step ordinary charged opcode next ih => exact Eval.append opcode (ih resultEq)
  | chargeError => cases resultEq
  | opcodeError => cases resultEq
  | branchUnderflow => cases resultEq
  | branchMinimal => cases resultEq
  | branch branch minimal split next ih =>
      rename_i element rest frame top stack alt flags ctx weight result
      have erased := ih resultEq
      cases element with
      | pushData => contradiction
      | pushNum => contradiction
      | op opcode =>
          cases opcode <;> simp only [ScriptElement.isBranch, Bool.false_eq_true] at branch
          · exact .if_execute top stack alt rest frame flags ctx _ split minimal erased
          · exact .notif_execute top stack alt rest frame flags ctx _ split minimal erased
  | unclosed =>
      rename_i result branch minimal split next ih
      cases result <;> simp [finishWeightedUnclosed] at resultEq

end LeanMiniscript.Script
