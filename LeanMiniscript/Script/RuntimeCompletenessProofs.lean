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

/-- The active debit of one opcode is covered by its source bound. -/
theorem executedSignatureWeight_le (element : ScriptElement) (stack : Stack)
    (ctx : TxContext) :
    executedSignatureWeight element stack ctx ≤ element.signatureWeightBound := by
  unfold executedSignatureWeight
  split
  · exact Nat.zero_le _
  · cases element with
    | pushData => simp [ScriptElement.signatureWeightBound]
    | pushNum => simp [ScriptElement.signatureWeightBound]
    | op opcode =>
        cases opcode <;> try { simp [ScriptElement.signatureWeightBound]; done }
        all_goals
          cases stack with
          | nil => simp [ScriptElement.signatureWeightBound]
          | cons key rest =>
            cases rest with
            | nil => simp [ScriptElement.signatureWeightBound]
            | cons signature rest =>
              cases rest <;>
                simp [ScriptElement.signatureWeightBound, signatureValidationWeight] <;> split <;> omega

/-- The source-wide signature bound covers every successful active path. -/
theorem EvalResources.signatureWeight_le_static
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources) :
    resources.signatureWeight ≤ staticValidationWeight script := by
  induction observed with
  | empty => simp [staticValidationWeight]
  | step head tail ih =>
      simp only [ExecutionResources.prepend_signatureWeight, staticValidationWeight,
        List.map_cons, List.sum_cons] at *
      exact Nat.add_le_add (executedSignatureWeight_le _ _ _) ih
  | @if_execute top stack alt script frame flags ctx finalStack finalAlt resources split minimal selected ih =>
      have sub := selectConditionalTail_sublist
        (show selectConditionalTail 0 (castToBool top) script = some (frame.select (castToBool top)) by
          simp [selectConditionalTail_eq, split])
      have bound := staticValidationWeight_sublist sub
      simpa [staticValidationWeight, ScriptElement.signatureWeightBound] using
        Nat.le_trans ih bound
  | @notif_execute top stack alt script frame flags ctx finalStack finalAlt resources split minimal selected ih =>
      have sub := selectConditionalTail_sublist
        (show selectConditionalTail 0 (!castToBool top) script = some (frame.select (!castToBool top)) by
          simp [selectConditionalTail_eq, split])
      have bound := staticValidationWeight_sublist sub
      simpa [staticValidationWeight, ScriptElement.signatureWeightBound] using
        Nat.le_trans ih bound

private theorem debitValidationWeight_exact (signature : StackElement) (weight : Nat)
    (enough : signatureValidationWeight signature ≤ weight) :
    ∃ remaining, debitValidationWeight signature weight = .ok remaining ∧
      remaining + signatureValidationWeight signature = weight := by
  unfold debitValidationWeight signatureValidationWeight at *
  split
  · rename_i empty
    exact ⟨weight, rfl, by simp⟩
  · rename_i nonempty
    simp only [nonempty, ↓reduceIte] at enough ⊢
    exact ⟨weight - validationWeightPerSigop, by simp [Nat.not_lt.mpr enough], by omega⟩

private theorem prepareValidationWeight_exact
    {element : ScriptElement} {stack alt nextStack nextAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
    (evaluated : Eval [element] stack alt flags ctx (.success nextStack nextAlt))
    (enough : executedSignatureWeight element stack ctx ≤ weight) :
    ∃ remaining, prepareValidationWeight element stack flags ctx weight = .ok remaining ∧
      remaining + executedSignatureWeight element stack ctx = weight := by
  by_cases version : ctx.sigVersion = .tapscript
  · cases element with
    | pushData => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight]⟩
    | pushNum => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight]⟩
    | op opcode =>
        cases opcode
        case OP_CHECKSIG | OP_CHECKSIGVERIFY =>
          cases stack with
          | nil => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight]⟩
          | cons key rest =>
              cases rest with
              | nil => exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight]⟩
              | cons signature rest =>
                  simpa [prepareValidationWeight, executedSignatureWeight, version] using
                    debitValidationWeight_exact signature weight
                      (by simpa [executedSignatureWeight, version] using enough)
        case OP_CHECKSIGADD =>
          cases evaluated <;> try simp_all [Opcode.isUpgradeableNop]
          all_goals
            rename_i pubkey countBytes signature count rest decoded checked next
            obtain ⟨remaining, charged, bound⟩ := debitValidationWeight_exact signature weight
              (by simpa [executedSignatureWeight, version] using enough)
            exact ⟨remaining, by simp [prepareValidationWeight, version, decoded, charged,
              bind, Except.bind], by simpa [executedSignatureWeight, version] using bound⟩
        all_goals exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight]⟩
  · exact ⟨weight, by simp [prepareValidationWeight, version], by simp [executedSignatureWeight, version]⟩

/-- Runtime completion with the exact debit observed on the active path.
Skipped opcodes and empty signatures consume zero; source push bounds still
cover inactive branches. The final weight plus the observed debit equals the
initial budget. -/
theorem EvalResources.runtime_complete_exact
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {resources : ExecutionResources}
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (observed : EvalResources script stack alt flags ctx finalStack finalAlt resources)
    (pushes : ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize)
    (peak : resources.peakStackItems ≤ maxStackSize)
    (weight : Nat) (enough : resources.signatureWeight ≤ weight) :
    ∃ remaining,
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
        .success finalStack finalAlt remaining ∧
      remaining + resources.signatureWeight = weight := by
  induction observed generalizing weight with
  | empty => exact ⟨weight, rfl, by simp⟩
  | @step element rest stack alt nextStack nextAlt finalStack finalAlt flags ctx resources head tail ih =>
      simp only [ExecutionResources.prepend_signatureWeight] at enough ⊢
      obtain ⟨nextWeight, charged, debit⟩ := prepareValidationWeight_exact (weight := weight) head (by omega)
      have tailPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      obtain ⟨remaining, completed, spent⟩ := ih
        (fun element member => pushes element (by simp [member])) tailPeak nextWeight (by omega)
      refine ⟨remaining, ?_, by omega⟩
      apply runtime_cons_success
        (next := { stack := nextStack, altStack := nextAlt, weight := nextWeight })
      · rw [execute_ordinary element head.singleton_nonConditional]
        simp [Nat.not_lt.mpr (pushes element (by simp)), charged,
          evaluate_eq_of_eval agreement head, bind, Except.bind, pure, Except.pure]
      · exact Nat.le_trans tail.initial_le_peak tailPeak
      · exact completed
  | @if_execute top stack alt script frame flags ctx finalStack finalAlt resources split minimal selected ih =>
      have projected : selectConditionalTail 0 (castToBool top) script =
          some (frame.select (castToBool top)) := by simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have selectedPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      obtain ⟨remaining, completed, spent⟩ := ih
        (fun element member => pushes element (by simp [sub.subset member])) selectedPeak weight
        (by simpa using enough)
      refine ⟨remaining, ?_, by simpa using spent⟩
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
          some (frame.select (!castToBool top)) := by simp [selectConditionalTail_eq, split]
      have sub := selectConditionalTail_sublist projected
      have selectedPeak : resources.peakStackItems ≤ maxStackSize := by
        simp only [ExecutionResources.prepend_peakStackItems] at peak
        omega
      obtain ⟨remaining, completed, spent⟩ := ih
        (fun element member => pushes element (by simp [sub.subset member])) selectedPeak weight
        (by simpa using enough)
      refine ⟨remaining, ?_, by simpa using spent⟩
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
  have bound := observed.signatureWeight_le_static
  obtain ⟨remaining, completed, spent⟩ := observed.runtime_complete_exact agreement
    pushes peak weight (Nat.le_trans bound enough)
  exact ⟨remaining, completed, by omega⟩

end LeanMiniscript.Script
