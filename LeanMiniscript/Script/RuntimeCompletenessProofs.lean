import LeanMiniscript.Script.RuntimeProjectionProofs
import LeanMiniscript.Script.ExecutionResources

namespace LeanMiniscript.Script

open RuntimeProjection

/-- Maximum BIP342 debit of one source instruction. Empty signatures and
inactive instructions consume less; CHECKSIGADD also validates its count. -/
def ScriptElement.signatureWeightBound : ScriptElement → Nat
  | .op .OP_CHECKSIG | .op .OP_CHECKSIGVERIFY | .op .OP_CHECKSIGADD => validationWeightPerSigop
  | _ => 0

/-- A conservative signature budget obtained solely from source instructions,
including all branches. It requires no witness execution or signature oracle. -/
def staticValidationWeight (script : Script) : Nat :=
  (script.map ScriptElement.signatureWeightBound).sum

theorem staticValidationWeight_sublist {selected script : Script}
    (sub : selected.Sublist script) :
    staticValidationWeight selected ≤ staticValidationWeight script := by
  induction sub <;> simp_all [staticValidationWeight] <;> omega

private theorem singleton_nonConditional
    {element : ScriptElement} {stack alt nextStack nextAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval [element] stack alt flags ctx (.success nextStack nextAlt)) :
    NonConditional element := by
  have noUnclosed (result : ExecResult) :
      finishUnclosedConditional result ≠ .success nextStack nextAlt := by
    cases result <;> simp [finishUnclosedConditional]
  have splitNil : splitConditional [] = none := rfl
  generalize resultEq : ExecResult.success nextStack nextAlt = result at evaluated
  cases element with
  | pushData => trivial
  | pushNum => trivial
  | op opcode =>
      cases opcode <;> try trivial
      all_goals cases evaluated <;> simp_all [Opcode.isUpgradeableNop]
      all_goals exact False.elim (noUnclosed _ rfl)

private theorem debitValidationWeight_complete (signature : StackElement) (weight : Nat)
    (enough : validationWeightPerSigop ≤ weight) :
    ∃ remaining, debitValidationWeight signature weight = .ok remaining ∧
      weight ≤ remaining + validationWeightPerSigop := by
  unfold debitValidationWeight
  split
  · exact ⟨weight, rfl, by omega⟩
  · simp only [Nat.not_lt.mpr enough, ↓reduceIte]
    exact ⟨weight - validationWeightPerSigop, rfl, by omega⟩

private theorem prepareValidationWeight_complete
    {element : ScriptElement} {stack alt nextStack nextAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
    (evaluated : Eval [element] stack alt flags ctx (.success nextStack nextAlt))
    (enough : element.signatureWeightBound ≤ weight) :
    ∃ remaining, prepareValidationWeight element stack flags ctx weight = .ok remaining ∧
      weight ≤ remaining + element.signatureWeightBound := by
  by_cases version : ctx.sigVersion = .tapscript
  · cases element with
    | pushData => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [ScriptElement.signatureWeightBound]⟩
    | pushNum => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [ScriptElement.signatureWeightBound]⟩
    | op opcode =>
        cases opcode
        case OP_CHECKSIG | OP_CHECKSIGVERIFY =>
          cases stack with
          | nil => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [ScriptElement.signatureWeightBound]⟩
          | cons key rest =>
              cases rest with
              | nil => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [ScriptElement.signatureWeightBound]⟩
              | cons signature rest => simpa [prepareValidationWeight, version, ScriptElement.signatureWeightBound] using
                  debitValidationWeight_complete signature weight enough
        case OP_CHECKSIGADD =>
          cases evaluated <;> try simp_all [Opcode.isUpgradeableNop]
          all_goals
            rename_i pubkey countBytes signature count rest decoded checked next
            obtain ⟨remaining, charged, bound⟩ := debitValidationWeight_complete signature weight enough
            exact ⟨remaining, by simp [prepareValidationWeight, version, decoded, charged,
              bind, Except.bind], bound⟩
        all_goals exact ⟨weight, by simp [prepareValidationWeight, version], by simp [ScriptElement.signatureWeightBound]⟩
  · exact ⟨weight, by simp [prepareValidationWeight, version], by omega⟩

/-- Resource-free execution completes in the source-order runtime when its
observed stack peak fits, every source push fits, and the initial weight covers
the static signature bound. This includes limits on skipped source pushes.
The unused weight is at least the initial weight minus that bound. -/
theorem EvalResources.runtime_complete
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (peak : resources.peakStackItems ≤ maxStackSize)
    (weight : Nat) (enough : staticValidationWeight script ≤ weight) :
    ∃ remaining,
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
        .success finalStack finalAlt remaining ∧
      weight ≤ remaining + staticValidationWeight script := by
  induction observed generalizing weight with
  | empty =>
      exact ⟨weight, rfl, by simp [staticValidationWeight]⟩
  | @step element rest stack alt nextStack nextAlt finalStack finalAlt flags ctx resources head tail ih =>
      have splitBudget : element.signatureWeightBound + staticValidationWeight rest ≤ weight := by
        simpa [staticValidationWeight] using enough
      obtain ⟨nextWeight, charged, debit⟩ := prepareValidationWeight_complete (weight := weight) head (by omega)
      have tailPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      obtain ⟨remaining, completed, spent⟩ := ih
        (fun element member => pushes element (by simp [member])) tailPeak
        nextWeight (by omega)
      refine ⟨remaining, ?_, ?_⟩
      · apply runtime_cons_success
          (next := { stack := nextStack, altStack := nextAlt, weight := nextWeight })
        · rw [execute_ordinary element (singleton_nonConditional head)]
          simp [Nat.not_lt.mpr (pushes element (by simp)), charged,
            evaluate_eq_of_eval agreement head, bind, Except.bind, pure, Except.pure]
        · exact Nat.le_trans tail.initial_le_peak tailPeak
        · exact completed
      · simp only [staticValidationWeight, List.map_cons, List.sum_cons] at ⊢ spent
        omega
  | @if_execute top stack alt script frame flags ctx finalStack finalAlt resources split minimal selected ih =>
      have projected : selectConditionalTail 0 (castToBool top) script =
          some (frame.select (castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have subset : ∀ element ∈ frame.select (castToBool top), element.pushSize ≤ maxScriptElementSize :=
        fun element member => pushes element (by simp [sub.subset member])
      have selectedPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      have budget : staticValidationWeight (frame.select (castToBool top)) ≤
          staticValidationWeight (.op .OP_IF :: script) := by
        simpa [staticValidationWeight, ScriptElement.signatureWeightBound] using
          staticValidationWeight_sublist sub
      obtain ⟨remaining, completed, spent⟩ := ih subset selectedPeak weight (by omega)
      refine ⟨remaining, ?_, by omega⟩
      have initial := Nat.le_trans selected.initial_le_peak selectedPeak
      apply runtime_cons_success
        (next := { stack := stack, altStack := alt, conditions := [castToBool top], weight := weight })
      · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          minimal, ScriptElement.branchChoice, pure, Except.pure]
      · exact initial
      · exact runtime_restore_conditional script _
          { stack := stack, altStack := alt, weight := weight } [] [] (castToBool top)
          projected (fun element member => pushes element (by simp [member])) initial
          (by simpa [evaluateWithRuntimeLimits] using completed)
  | @notif_execute top stack alt script frame flags ctx finalStack finalAlt resources split minimal selected ih =>
      have projected : selectConditionalTail 0 (!castToBool top) script =
          some (frame.select (!castToBool top)) := by
        simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have subset : ∀ element ∈ frame.select (!castToBool top), element.pushSize ≤ maxScriptElementSize :=
        fun element member => pushes element (by simp [sub.subset member])
      have selectedPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      have budget : staticValidationWeight (frame.select (!castToBool top)) ≤
          staticValidationWeight (.op .OP_NOTIF :: script) := by
        simpa [staticValidationWeight, ScriptElement.signatureWeightBound] using
          staticValidationWeight_sublist sub
      obtain ⟨remaining, completed, spent⟩ := ih subset selectedPeak weight (by omega)
      refine ⟨remaining, ?_, by omega⟩
      have initial := Nat.le_trans selected.initial_le_peak selectedPeak
      apply runtime_cons_success
        (next := { stack := stack, altStack := alt, conditions := [!castToBool top], weight := weight })
      · simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          minimal, ScriptElement.branchChoice, pure, Except.pure]
      · exact initial
      · exact runtime_restore_conditional script _
          { stack := stack, altStack := alt, weight := weight } [] [] (!castToBool top)
          projected (fun element member => pushes element (by simp [member])) initial
          (by simpa [evaluateWithRuntimeLimits] using completed)

end LeanMiniscript.Script
