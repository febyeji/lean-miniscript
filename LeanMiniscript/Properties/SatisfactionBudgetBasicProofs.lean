import LeanMiniscript.Properties.SatisfactionBudgetProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

namespace GeneratedBudgetContract

theorem andV
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods : CorrectnessModifiers} {secondType : MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedBudgetContract first firstWitness true flags txCtx ⟨.V, firstMods⟩)
    (secondContract : GeneratedBudgetContract second secondWitness expected flags txCtx secondType)
    (branch : branchBase secondType.base) :
    GeneratedBudgetContract (.and_v first second) (Witness.combine firstWitness secondWitness)
      expected flags txCtx ⟨secondType.base, {
        z := firstMods.z && secondType.mods.z
        o := (firstMods.z && secondType.mods.o) || (firstMods.o && secondType.mods.z)
        n := firstMods.n || (firstMods.z && secondType.mods.n)
        u := secondType.mods.u }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExecuted firstFrame firstFunded =>
    have firstCore := GeneratedContract.v firstInput firstTrue firstExecuted
    cases secondContract with
    | b input facts executed frame funded =>
        apply generatedBudgetB_of_contract (firstCore.andV_b (.b input facts executed))
        · simpa [compile, compileWithKeyHash] using
            (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append frame
        · simp only [witnessPayload_combine]
          omega
    | v input truth executed frame funded =>
        apply generatedBudgetV_of_contract (firstCore.andV_v (.v input truth executed))
        · simpa [compile, compileWithKeyHash] using
            (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append frame
        · simp only [witnessPayload_combine]
          omega
    | k input ownArgs key signature shape executed checked frame funded =>
        apply generatedBudgetK_of_contract (firstCore.andV_k (.k input ownArgs key signature shape executed checked))
        · simpa [compile, compileWithKeyHash] using
            (firstFrame.withSuffix (suffix := secondWitness.toInitialStack)).append frame
        · simp only [witnessPayload_combine]
          omega
    | w => simp [branchBase] at branch

theorem n {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness expected flags txCtx ⟨.B, mods⟩) :
    GeneratedBudgetContract (.n fragment) witness expected flags txCtx
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      have suffix : ExecutesBudgetFrame [.op .OP_0NOTEQUAL] [result]
          [boolToElement (value != 0)] flags txCtx 0 := by
        apply ExecutesBudgetFrame.of_zero
        · intro rest alt
          exact .zeroNotEqual _ _ _ _ [] _ _ _ facts.decoded Eval.done
        · rfl
      apply generatedBudgetB_of_contract ((GeneratedContract.b input facts executed).n)
      · simpa [compile, compileWithKeyHash] using frame.append suffix
      · exact funded

theorem verify {fragment : CoreFragment} {witness : Witness}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness true flags txCtx ⟨.B, mods⟩) :
    GeneratedBudgetContract (.v fragment) witness true flags txCtx
      ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      have suffix : ExecutesBudgetFrame [.op .OP_VERIFY] [result] [] flags txCtx 0 := by
        apply ExecutesBudgetFrame.of_zero
        · intro rest alt
          exact .verify_success _ _ [] _ _ _ _ facts.truth Eval.done
        · rfl
      apply generatedBudgetV_of_contract ((GeneratedContract.b input facts executed).verify)
      · simpa [compile, compileWithKeyHash] using
          (frame.append suffix).compileVerify (compile_balancedControlFlow fragment)
      · exact funded

theorem c {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness expected flags txCtx ⟨.K, mods⟩) :
    GeneratedBudgetContract (.c fragment) witness expected flags txCtx
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | k input ownArgs key signature shape executed checked frame funded =>
      have suffix : ExecutesBudgetFrame [.op .OP_CHECKSIG] [key, signature]
          [boolToElement expected] flags txCtx (signatureValidationWeight signature) := by
        apply ExecutesBudgetFrame.single
        · intro rest alt
          cases expected with
          | true => exact .checksig_success _ _ _ [] _ _ _ _ checked Eval.done
          | false => exact .checksig_failure _ _ _ [] _ _ _ _ checked Eval.done
        · intro rest
          simp only [List.cons_append, List.nil_append, executedSignatureWeight]
          split <;> simp
      apply generatedBudgetB_of_contract ((GeneratedContract.k input ownArgs key signature shape executed checked).c)
      · simpa [compile, compileWithKeyHash] using frame.append suffix
      · exact funded

theorem a {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness expected flags txCtx ⟨.B, mods⟩) :
    GeneratedBudgetContract (.a fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      apply generatedBudgetW_of_contract ((GeneratedContract.b input facts executed).a)
        (outputs := fun saved => [saved, result]) (budget := budget)
      · intro saved rest alt
        obtain ⟨resources, observed, bound⟩ := frame rest (saved :: alt)
        have move : Eval [.op .OP_TOALTSTACK] (saved :: witness.toInitialStack ++ rest) alt
            flags txCtx (.success (witness.toInitialStack ++ rest) (saved :: alt)) :=
          .toAltStackNext Eval.done
        have restore : Eval [.op .OP_FROMALTSTACK] (result :: rest) (saved :: alt)
            flags txCtx (.success (saved :: result :: rest) alt) :=
          .fromAltStackNext Eval.done
        have last := EvalResources.step restore (EvalResources.empty _ _ _ _)
        refine ⟨_, (by simpa [compile, compileWithKeyHash] using
          EvalResources.step move (observed.append last)), ?_⟩
        simpa [executedSignatureWeight] using bound
      · exact funded

theorem s {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedBudgetContract fragment witness expected flags txCtx ⟨.B, mods⟩)
    (oneArg : mods.o = true) :
    GeneratedBudgetContract (.s fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value budget input facts executed frame funded =>
      obtain ⟨argument, shape⟩ := input.oneArg oneArg
      apply generatedBudgetW_of_contract ((GeneratedContract.b input facts executed).s oneArg)
        (outputs := fun saved => [result, saved]) (budget := budget)
      · intro saved rest alt
        obtain ⟨resources, observed, bound⟩ := frame (saved :: rest) alt
        rw [shape] at observed
        have swapped : Eval [.op .OP_SWAP] (saved :: argument :: rest) alt flags txCtx
            (.success (argument :: saved :: rest) alt) :=
          .swap _ _ _ _ [] _ _ _ Eval.done
        refine ⟨_, (by simpa [compile, compileWithKeyHash, shape] using
          EvalResources.step swapped observed), ?_⟩
        simpa [executedSignatureWeight] using bound
      · exact funded

end GeneratedBudgetContract

structure CandidatePair.SupportsGeneratedBudgets (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports fun witness =>
    GeneratedBudgetContract fragment witness true flags txCtx ty
  dsat : pair.dsat.Supports fun witness =>
    GeneratedBudgetContract fragment witness false flags txCtx ty

/-- Budget-aware generated support aligned with source-order threshold
    children. -/
inductive SupportsGeneratedBudgetsList (scriptCtx : ScriptContext)
    (flags : ScriptFlags) (txCtx : TxContext) :
    List CandidatePair → List CoreFragment → List MiniType → Prop where
  | nil : SupportsGeneratedBudgetsList scriptCtx flags txCtx [] [] []
  | snoc {pairs : List CandidatePair} {fragments : List CoreFragment}
      {types : List MiniType} {pair : CandidatePair} {fragment : CoreFragment}
      {ty : MiniType}
      (prior : SupportsGeneratedBudgetsList scriptCtx flags txCtx
        pairs fragments types)
      (child : CandidatePair.SupportsGeneratedBudgets pair scriptCtx fragment
        ty flags txCtx) :
      SupportsGeneratedBudgetsList scriptCtx flags txCtx
        (pairs ++ [pair]) (fragments ++ [fragment]) (types ++ [ty])

namespace SupportsGeneratedBudgetsList

/-- Empty candidate support has empty aligned fragment and type rows. -/
theorem nil_inv
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      [] fragments types) : fragments = [] ∧ types = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at supported
  cases supported with
  | nil => exact ⟨rfl, rfl⟩
  | snoc prior child => simp at pairsEq

/-- Invert the final source child of aligned budget support. -/
theorem snoc_inv
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {pair : CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      (pairs ++ [pair]) fragments types) :
    ∃ priorFragments priorTypes fragment ty,
      fragments = priorFragments ++ [fragment] ∧
      types = priorTypes ++ [ty] ∧
      SupportsGeneratedBudgetsList scriptCtx flags txCtx
        pairs priorFragments priorTypes ∧
      CandidatePair.SupportsGeneratedBudgets pair scriptCtx fragment ty
        flags txCtx := by
  generalize pairsEq : pairs ++ [pair] = allPairs at supported
  cases supported with
  | nil => simp at pairsEq
  | @snoc otherPairs otherFragments otherTypes otherPair fragment ty prior child =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherFragments, otherTypes, fragment, ty, rfl, rfl, prior, child⟩

/-- Budget list support retains pointwise typing. -/
theorem typed
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType}
    (supported : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      pairs fragments types) : HasTypeList scriptCtx fragments types := by
  induction supported with
  | nil => exact .nil
  | snoc prior child ih => exact ih.snoc child.typed

/-- Prepend one budget-supported child. -/
theorem cons
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {pair : CandidatePair} {fragment : CoreFragment}
    {ty : MiniType}
    (child : CandidatePair.SupportsGeneratedBudgets pair scriptCtx fragment
      ty flags txCtx)
    (rest : SupportsGeneratedBudgetsList scriptCtx flags txCtx
      pairs fragments types) :
    SupportsGeneratedBudgetsList scriptCtx flags txCtx
      (pair :: pairs) (fragment :: fragments) (ty :: types) := by
  induction rest with
  | nil => exact .snoc .nil child
  | snoc prior last ih => exact .snoc ih last

end SupportsGeneratedBudgetsList

namespace CandidatePair.SupportsGeneratedBudgets

/-- Erasing budget evidence recovers the existing candidate-wide generated
    contract. -/
theorem toSupportsGeneratedContract
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {ty : MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ty flags txCtx) :
    pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx :=
  ⟨supported.typed,
    fun witness selected => (supported.sat witness selected).toGeneratedContract,
    fun witness selected => (supported.dsat witness selected).toGeneratedContract⟩

/-- Project a budget-aware satisfaction contract through `satisfy`. -/
theorem satisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedBudgets
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : satisfy fragment env = some witness) :
    GeneratedBudgetContract fragment witness true flags env.txCtx ty :=
  supported.sat witness generated

/-- Project a budget-aware dissatisfaction contract through `dissatisfy`. -/
theorem dissatisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedBudgets
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : dissatisfy fragment env = some witness) :
    GeneratedBudgetContract fragment witness false flags env.txCtx ty :=
  supported.dsat witness generated

/-- Candidate-wide budget support for `and_v`. -/
theorem and_v
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods : CorrectnessModifiers}
    {secondType : MiniType} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedBudgets firstPair
      scriptCtx first ⟨.V, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedBudgets secondPair
      scriptCtx second secondType flags txCtx)
    (branch : branchBase secondType.base) :
    CandidatePair.SupportsGeneratedBudgets
      ({ sat := firstPair.sat.combine secondPair.sat
         dsat := (firstPair.sat.combine secondPair.dsat).markNonCanonical } :
        CandidatePair)
      scriptCtx (.and_v first second)
      ⟨secondType.base, {
        z := firstMods.z && secondType.mods.z
        o := (firstMods.z && secondType.mods.o) ||
          (firstMods.o && secondType.mods.z)
        n := firstMods.n || (firstMods.z && secondType.mods.n)
        u := secondType.mods.u }⟩ flags txCtx := by
  refine ⟨.and_v firstSupported.typed secondSupported.typed branch,
    ?_, ?_⟩
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    exact firstContract.andV secondContract branch
  · intro witness selected
    have combined := CandidateResult.markNonCanonical_usableWitness_iff.mp selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.dsat) witness combined
    exact firstContract.andV secondContract branch

/-- Candidate-wide budget support for `n`. -/
theorem n
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets pair scriptCtx (.n fragment)
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.n_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).n,
    fun witness selected => (supported.dsat witness selected).n⟩

/-- Candidate-wide budget support for `v`. -/
theorem v
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets ({ sat := pair.sat } : CandidatePair)
      scriptCtx (.v fragment) ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩
      flags txCtx :=
  ⟨.v_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).verify,
    CandidateResult.supports_impossible _⟩

/-- Candidate-wide budget support for `c`. -/
theorem c
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.K, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets pair scriptCtx (.c fragment)
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.c_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).c,
    fun witness selected => (supported.dsat witness selected).c⟩

/-- Candidate-wide budget support for `a`. -/
theorem a
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedBudgets pair scriptCtx (.a fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.a_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).a,
    fun witness selected => (supported.dsat witness selected).a⟩

/-- Candidate-wide budget support for `s`. -/
theorem s
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedBudgets pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) (oneArg : mods.o = true) :
    CandidatePair.SupportsGeneratedBudgets pair scriptCtx (.s fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.s_wrap supported.typed oneArg,
    fun witness selected => (supported.sat witness selected).s oneArg,
    fun witness selected => (supported.dsat witness selected).s oneArg⟩

end CandidatePair.SupportsGeneratedBudgets

end LeanMiniscript.Properties
