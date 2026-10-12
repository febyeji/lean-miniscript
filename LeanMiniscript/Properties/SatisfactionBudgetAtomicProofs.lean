import LeanMiniscript.Properties.SatisfactionBudgetBasicProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

theorem generatedBudgets_of_zero
    {pair : CandidatePair} {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment ⟨.B, mods⟩ flags txCtx)
    (zero : staticValidationWeight (compile fragment) = 0) :
    CandidatePair.SupportsGeneratedBudgets pair scriptCtx fragment ⟨.B, mods⟩ flags txCtx := by
  refine ⟨supported.typed, ?_, ?_⟩
  all_goals
    intro witness selected
    first
    | have contract := supported.sat witness selected
    | have contract := supported.dsat witness selected
    cases contract with
    | b input facts executed =>
      exact .b input facts executed (.of_zero executed zero) (Nat.zero_le _)

theorem generatedBudgets_zero (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates .zero env)
      scriptCtx .zero ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx :=
  generatedBudgets_of_zero (generatedContract_zero scriptCtx env flags) rfl

theorem generatedBudgets_one (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates .one env)
      scriptCtx .one ⟨.B, { z := true, u := true }⟩ flags env.txCtx :=
  generatedBudgets_of_zero (generatedContract_one scriptCtx env flags) rfl

theorem generatedBudgets_older {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates (.older n) env)
      scriptCtx (.older n) ⟨.B, { z := true }⟩ flags env.txCtx :=
  generatedBudgets_of_zero (generatedContract_older valid) rfl

theorem generatedBudgets_after {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates (.after n) env)
      scriptCtx (.after n) ⟨.B, { z := true }⟩ flags env.txCtx :=
  generatedBudgets_of_zero (generatedContract_after valid) rfl

theorem generatedBudgets_hash {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates lock.fragment env)
      scriptCtx lock.fragment ⟨.B, { o := true, n := true, d := true, u := true }⟩ flags env.txCtx := by
  apply generatedBudgets_of_zero (generatedContract_hash sound)
  cases lock <;> rfl

private theorem keyBudget
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {txCtx : TxContext} {mods : CorrectnessModifiers}
    {signature : StackElement}
    (contract : GeneratedContract fragment witness expected flags txCtx ⟨.K, mods⟩)
    (zero : staticValidationWeight (compile fragment) = 0)
    (signatureShape : witness.toInitialStack.getLast? = some signature)
    (funded : signatureValidationWeight signature ≤ witnessPayload witness) :
    GeneratedBudgetContract fragment witness expected flags txCtx ⟨.K, mods⟩ := by
  cases contract with
  | k input ownArgs key actualSignature shape executed checked =>
      have same : actualSignature = signature := by
        simpa [shape] using signatureShape
      subst actualSignature
      have full : ExecutesStackFrame (compile fragment) witness.toInitialStack [key, signature] flags txCtx := by
        rw [shape]
        simpa using executed.withSuffix (suffix := [signature])
      exact .k input ownArgs key signature shape executed checked (.of_zero full zero) (by simpa using funded)

theorem generatedBudgets_pk_k {key : PubKey} {env : SatEnv} {flags : ScriptFlags}
    (valid : validResolvedPubKey .tapscript key)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates (.pk_k key) env)
      .tapscript (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩ flags env.txCtx := by
  have supported := generatedContract_pk_k_of_modeled valid version modeled sound encodings
  refine ⟨supported.typed, ?_, ?_⟩
  · intro witness selected
    cases chosen : env.signatureFor key with
    | none => simp [satisfactionCandidates, keyCandidates, chosen, CandidateResult.usableWitness?, CandidateResult.usable] at selected
    | some signature =>
        have shape : witness = [signature] := by
          simpa [satisfactionCandidates, keyCandidates, chosen, CandidateResult.usableWitness?, CandidateResult.usable] using selected.symm
        subst witness
        apply keyBudget (supported.sat _ selected) rfl (signature := signature)
        · rfl
        · simpa [witnessPayload] using selectedSignature_validationWeight_le_size valid version encodings chosen
  · intro witness selected
    have shape : witness = [falseElement] := by
      simpa [satisfactionCandidates, keyCandidates, CandidateResult.usableWitness?, CandidateResult.usable] using selected.symm
    subst witness
    apply keyBudget (supported.dsat _ selected) rfl (signature := falseElement)
    · rfl
    · exact Nat.zero_le _

theorem generatedBudgets_pk_h {key : PubKey} {env : SatEnv} {flags : ScriptFlags}
    (valid : validResolvedPubKey .tapscript key)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedBudgets (satisfactionCandidates (.pk_h key) env)
      .tapscript (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩ flags env.txCtx := by
  have supported := generatedContract_pk_h_of_modeled valid version modeled sound encodings
  refine ⟨supported.typed, ?_, ?_⟩
  · intro witness selected
    cases chosen : env.signatureFor key with
    | none => simp [satisfactionCandidates, keyCandidates, chosen, CandidateResult.usableWitness?, CandidateResult.usable] at selected
    | some signature =>
        have shape : witness = [signature, key.bytes] := by
          simpa [satisfactionCandidates, keyCandidates, chosen, CandidateResult.usableWitness?, CandidateResult.usable] using selected.symm
        subst witness
        apply keyBudget (supported.sat _ selected) rfl (signature := signature)
        · rfl
        · have bound := selectedSignature_validationWeight_le_size valid version encodings chosen
          simp [witnessPayload]
          omega
  · intro witness selected
    have shape : witness = [falseElement, key.bytes] := by
      simpa [satisfactionCandidates, keyCandidates, CandidateResult.usableWitness?, CandidateResult.usable] using selected.symm
    subst witness
    apply keyBudget (supported.dsat _ selected) rfl (signature := falseElement)
    · rfl
    · exact Nat.zero_le _

end LeanMiniscript.Properties
