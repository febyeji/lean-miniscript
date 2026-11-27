import LeanMiniscript.Extraction.TapscriptRecovery.AtomicFrames

/-! Decompose executed conditionals and track their consumed witness and checked signatures. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrI

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Active

def RawUnsigned (result : CandidateResult) : Prop :=
  ∃ candidate, result = .candidate candidate ∧ candidate.hasSig = false

theorem unsigned_withSelector {result : CandidateResult} {selector : StackElement}
    (unsigned : RawUnsigned result) : RawUnsigned (result.withSelector selector) := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  exact ⟨candidate.withSelector selector, rfl, h⟩

theorem unsigned_select_left {left right : CandidateResult} {witness : Witness}
    (unsigned : RawUnsigned left)
    (selected : (left.select right).usableWitness? = some witness) :
    left.usableWitness? = some witness := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases right with
  | impossible => exact selected
  | candidate other =>
    cases ho : other.hasSig
    · have unusable : (candidate.select other).status = .dontUse := by
        simp [SatisfactionCandidate.select, h, ho]
      simp [CandidateResult.select, CandidateResult.usableWitness?, unusable] at selected
    · simpa [CandidateResult.select, SatisfactionCandidate.select, h, ho] using selected

theorem unsigned_select_right {left right : CandidateResult} {witness : Witness}
    (unsigned : RawUnsigned right)
    (selected : (left.select right).usableWitness? = some witness) :
    right.usableWitness? = some witness := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases left with
  | impossible => exact selected
  | candidate other =>
    cases ho : other.hasSig
    · have unusable : (other.select candidate).status = .dontUse := by
        simp [SatisfactionCandidate.select, h, ho]
      simp [CandidateResult.select, CandidateResult.usableWitness?, unusable] at selected
    · simpa [CandidateResult.select, SatisfactionCandidate.select, h, ho] using selected

theorem appended_selector_injective {left right : Witness} {a b : StackElement}
    (eq : left ++ [a] = right ++ [b]) : a = b := by
  have reversed := congrArg List.reverse eq
  simpa using (List.cons.inj (by simpa using reversed)).1

theorem or_i_candidate_cases {X Y : CoreFragment} {env : SatEnv} {arguments : Witness}
    (canonical : satisfy (.or_i X Y) env = some arguments) :
    (∃ own, satisfy X env = some own ∧ arguments = own ++ [trueElement]) ∨
    (∃ own, satisfy Y env = some own ∧ arguments = own ++ [falseElement]) := by
  rcases CandidateResult.select_usableWitness_cases canonical with h | h
  · obtain ⟨own, h, eq⟩ := CandidateResult.withSelector_usableWitness_iff.mp h
    exact Or.inl ⟨own, h, eq⟩
  · obtain ⟨own, h, eq⟩ := CandidateResult.withSelector_usableWitness_iff.mp h
    exact Or.inr ⟨own, h, eq⟩

theorem or_i_left_excludes_unsigned_right {X Y : CoreFragment} {env : SatEnv}
    {own : Witness} (canonical : satisfy (.or_i X Y) env = some (own ++ [trueElement])) :
    ¬ RawUnsigned (satisfactionCandidates Y env).sat := by
  intro unsigned
  have chosen := unsigned_select_right (unsigned_withSelector unsigned) canonical
  obtain ⟨other, _, eq⟩ := CandidateResult.withSelector_usableWitness_iff.mp chosen
  have impossible : trueElement = falseElement := appended_selector_injective eq
  exact (by decide : trueElement ≠ falseElement) impossible

theorem or_i_right_excludes_unsigned_left {X Y : CoreFragment} {env : SatEnv}
    {own : Witness} (canonical : satisfy (.or_i X Y) env = some (own ++ [falseElement])) :
    ¬ RawUnsigned (satisfactionCandidates X env).sat := by
  intro unsigned
  have chosen := unsigned_select_left (unsigned_withSelector unsigned) canonical
  obtain ⟨other, _, eq⟩ := CandidateResult.withSelector_usableWitness_iff.mp chosen
  have impossible : falseElement = trueElement := appended_selector_injective eq
  exact (by decide : falseElement ≠ trueElement) impossible

theorem signed_excludes_unsigned {result : CandidateResult}
    (signed : result.Signed) : ¬ RawUnsigned result := by
  rintro ⟨candidate, hc, unsigned⟩
  have := signed candidate hc
  simp_all

def CheckedSignature (fragment : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (consumed : Witness) : Prop :=
  ∃ sig ∈ consumed, ∃ key ∈ fragment.keys,
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true

theorem or_i_run_cases {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {input out : Stack}
    (version : WitnessRules flags env.txCtx)
    (run : Eval (compile (.or_i X Y)) input [] flags env.txCtx (.success out [])) :
    (∃ stack, input = trueElement :: stack ∧
      Eval (compile X) stack [] flags env.txCtx (.success out [])) ∨
    (∃ stack, input = falseElement :: stack ∧
      Eval (compile Y) stack [] flags env.txCtx (.success out [])) := by
  have conditionalRun : Eval
      ([.op .OP_IF] ++ compile X ++ [.op .OP_ELSE] ++ compile Y ++ [.op .OP_ENDIF])
      input [] flags env.txCtx (.success out []) := by
    simpa [compile, compileWithKeyHash] using run
  cases input with
  | nil =>
    have failed := Eval.fixedArityStackUnderflow_result
      (opcode := .OP_IF) (required := 1) (arity := rfl)
      (underflow := by simp) conditionalRun
    contradiction
  | cons selector stack =>
    rcases ifElse_active_cases version (compile_balancedControlFlow X)
      (compile_balancedControlFlow Y) conditionalRun with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl ⟨stack, rfl, h⟩
    · exact Or.inr ⟨stack, rfl, h⟩

theorem typed_B_input_frame {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {input rest : Stack} {top : StackElement}
    (typed : HasType sc fragment ⟨.B, mods⟩) (wf : fragment.WellFormed sc)
    (run : Eval (compile fragment) input [] flags env.txCtx (.success (top :: rest) [])) :
    ∃ consumed : Witness, input = consumed.toInitialStack ++ rest := by
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf
    input [] flags env.txCtx (.success (top :: rest) []) run
  obtain ⟨args, tail, value, eq, outEq, _⟩ := effect.b_inv
  injection outEq with _ tailEq
  subst tail
  exact ⟨args.reverse, by simpa [Witness.toInitialStack] using eq⟩

theorem typed_V_input_frame {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {input rest : Stack}
    (typed : HasType sc fragment ⟨.V, mods⟩) (wf : fragment.WellFormed sc)
    (run : Eval (compile fragment) input [] flags env.txCtx (.success rest [])) :
    ∃ consumed : Witness, input = consumed.toInitialStack ++ rest := by
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf
    input [] flags env.txCtx (.success rest []) run
  obtain ⟨args, eq, _⟩ := effect.v_inv
  exact ⟨args.reverse, by simpa [Witness.toInitialStack] using eq⟩

theorem witness_selector_frame {other consumed : Witness} {selector : StackElement} {rest : Stack}
    (eq : other.toInitialStack ++ rest = selector :: (consumed.toInitialStack ++ rest)) :
    other = consumed ++ [selector] := by
  have cancel : other.toInitialStack = selector :: consumed.toInitialStack :=
    List.append_cancel_right eq
  simpa [Witness.toInitialStack] using congrArg List.reverse cancel

theorem or_i_run_B {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (version : WitnessRules flags env.txCtx)
    (run : Eval (compile (.or_i X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    (∃ consumed, other = consumed ++ [trueElement] ∧
      Eval (compile X) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) [])) ∨
    (∃ consumed, other = consumed ++ [falseElement] ∧
      Eval (compile Y) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) [])) := by
  rcases or_i_run_cases version run with ⟨stack, eq, childRun⟩ | ⟨stack, eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_B_input_frame typedX wfX childRun
    exact Or.inl ⟨consumed, witness_selector_frame eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_B_input_frame typedY wfY childRun
    exact Or.inr ⟨consumed, witness_selector_frame eq, childRun⟩

theorem or_i_run_V {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.V, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (version : WitnessRules flags env.txCtx)
    (run : Eval (compile (.or_i X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) :
    (∃ consumed, other = consumed ++ [trueElement] ∧
      Eval (compile X) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) ∨
    (∃ consumed, other = consumed ++ [falseElement] ∧
      Eval (compile Y) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) := by
  rcases or_i_run_cases version run with ⟨stack, eq, childRun⟩ | ⟨stack, eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_V_input_frame typedX wfX childRun
    exact Or.inl ⟨consumed, witness_selector_frame eq, childRun⟩
  · obtain ⟨consumed, rfl⟩ := typed_V_input_frame typedY wfY childRun
    exact Or.inr ⟨consumed, witness_selector_frame eq, childRun⟩

structure ExecutionContextIn (sc : ScriptContext) (parent child : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) : Prop where
  sound : env.Sound
  encoding : env.EncodingSound flags
  version : ModeledContextVersion sc env.txCtx
  modeled : ModeledContextFlags sc flags
  material : match sc with
    | .tapscript => ∀ key ∈ parent.keys, key.bytes.size = 32
    | .p2wsh => ∃ sane : SaneFragment .p2wsh, sane.checked.fragment = parent ∧
        LocalPreimageSignatureDisjoint parent env flags parentArgs
  recover : LocalHashSlotRecovery parent env parentArgs
  canonical : satisfy parent env = some parentArgs
  thirdParty : ThirdPartyWitness parent env.txCtx parentArgs parentOther
  childKeys : ∀ key ∈ child.keys, key ∈ parent.keys
  childLocks : ∀ lock ∈ child.hashLocks, lock ∈ parent.hashLocks
  consumedIn : ∀ item ∈ consumed, item ∈ parentOther

abbrev ExecutionContext := ExecutionContextIn .tapscript

theorem ExecutionContextIn.rules {parent child env flags pa po own}
    (context : ExecutionContextIn sc parent child env flags pa po own) :
    WitnessRules flags env.txCtx := witnessRules_of_modeled context.version context.modeled

theorem ExecutionContextIn.keySizes {parent child env flags pa po own}
    (context : ExecutionContext parent child env flags pa po own) :
    ∀ key ∈ parent.keys, key.bytes.size = 32 := context.material

theorem ExecutionContextIn.saneFrame {parent child env flags pa po own}
    (context : ExecutionContextIn .p2wsh parent child env flags pa po own) :
    ∃ sane : SaneFragment .p2wsh, sane.checked.fragment = parent ∧
      P2WSHRecovery.ExecutionContext sane child env flags pa po own := by
  obtain ⟨sane, rfl, disjoint⟩ := context.material
  exact ⟨sane, rfl, context.sound, context.version, context.modeled, context.canonical,
    context.thirdParty, ⟨context.recover, disjoint⟩, context.childKeys, context.childLocks, context.consumedIn⟩

def ExecutionEvidence (fragment : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (consumed : Witness) : Prop :=
  RawUnsigned (satisfactionCandidates fragment env).sat ∨ CheckedSignature fragment env flags consumed

def AmbientExecutionBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) []) → castToBool top = true →
    ExecutionEvidence fragment env flags consumed

abbrev AmbientExecutionB := AmbientExecutionBIn .tapscript

def AmbientExecutionVIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) →
    ExecutionEvidence fragment env flags consumed

abbrev AmbientExecutionV := AmbientExecutionVIn .tapscript

theorem signed_execution_consumes {fragment : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed : Witness} (signed : (satisfactionCandidates fragment env).sat.Signed)
    (evidence : ExecutionEvidence fragment env flags consumed) :
    CheckedSignature fragment env flags consumed := by
  rcases evidence with unsigned | checked
  · exact (signed_excludes_unsigned signed unsigned).elim
  · exact checked

theorem execution_without_checked_signature {fragment : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {consumed : Witness}
    (evidence : ExecutionEvidence fragment env flags consumed)
    (absent : ¬ CheckedSignature fragment env flags consumed) :
    RawUnsigned (satisfactionCandidates fragment env).sat := by
  exact evidence.resolve_right absent

theorem ambientExecution_c_pk_k (key : PubKey) : AmbientExecutionBIn sc (.c (.pk_k key)) := by
  intro parent env flags parentArgs parentOther consumed top rest _context _bounded run truth
  obtain ⟨sig, eq, checked⟩ := accepts_c_pk_k_inversion run truth
  have consumedEq : consumed = [sig] := witness_eq_singleton_of_toInitialStack
    (List.append_cancel_right eq)
  exact Or.inr ⟨sig, by simp [consumedEq], key, by simp [CoreFragment.keys], checked⟩

theorem ambientExecution_sha256 (hash : Hash256) : AmbientExecutionBIn sc (.sha256 hash) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  obtain ⟨p, eq, matched⟩ := accepts_sha256_inversion bounded run truth
  have consumedEq : consumed = [p] := witness_eq_singleton_of_toInitialStack
    (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [consumedEq]))
    (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  exact Or.inl ⟨{witness := [p], hasSig := false},
    by simp [satisfactionCandidates, hashCandidates, selected, CandidateResult.usable], rfl⟩

theorem ambientExecution_hash160 (hash : Hash160) : AmbientExecutionBIn sc (.hash160 hash) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  obtain ⟨p, eq, matched⟩ := accepts_hash160_inversion bounded run truth
  have consumedEq : consumed = [p] := witness_eq_singleton_of_toInitialStack
    (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [consumedEq]))
    (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  exact Or.inl ⟨{witness := [p], hasSig := false},
    by simp [satisfactionCandidates, hashCandidates, selected, CandidateResult.usable], rfl⟩

theorem bounded_without_selector {consumed : Witness} {selector : StackElement} {rest : Stack}
    (bounded : ∀ item ∈ (consumed ++ [selector]).toInitialStack ++ rest,
      item.size ≤ maxScriptElementSize) :
    ∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize := by
  intro item hi
  apply bounded item
  simpa [Witness.toInitialStack, List.reverse_append] using List.mem_cons_of_mem selector hi

theorem unsigned_select_left_raw {left right : CandidateResult}
    (unsigned : RawUnsigned left) : RawUnsigned (left.select right) := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases right with
  | impossible => exact ⟨candidate, rfl, h⟩
  | candidate other => exact ⟨candidate.select other, rfl, by simp [h]⟩

theorem unsigned_select_right_raw {left right : CandidateResult}
    (unsigned : RawUnsigned right) : RawUnsigned (left.select right) := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases left with
  | impossible => exact ⟨candidate, rfl, h⟩
  | candidate other => exact ⟨other.select candidate, rfl, by simp [h]⟩

theorem executionContext_restrict {parent child active : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {parentArgs parentOther consumed activeConsumed : Witness}
    (context : ExecutionContextIn sc parent child env flags parentArgs parentOther consumed)
    (keys : ∀ key ∈ active.keys, key ∈ child.keys)
    (locks : ∀ lock ∈ active.hashLocks, lock ∈ child.hashLocks)
    (consumedIn : ∀ item ∈ activeConsumed, item ∈ consumed) :
    ExecutionContextIn sc parent active env flags parentArgs parentOther activeConsumed :=
  ⟨context.sound, context.encoding, context.version, context.modeled, context.material,
    context.recover, context.canonical, context.thirdParty,
    fun k h => context.childKeys k (keys k h), fun l h => context.childLocks l (locks l h),
    fun item h => context.consumedIn item (consumedIn item h)⟩

theorem evidence_or_i_left {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed other : Witness} (consumedIn : ∀ item ∈ consumed, item ∈ other)
    (evidence : ExecutionEvidence X env flags consumed) : ExecutionEvidence (.or_i X Y) env flags other := by
  rcases evidence with unsigned | ⟨sig, hs, key, hk, checked⟩
  · exact Or.inl (unsigned_select_left_raw (unsigned_withSelector unsigned))
  · exact Or.inr ⟨sig, consumedIn sig hs, key, List.mem_append_left _ hk, checked⟩

theorem evidence_or_i_right {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed other : Witness} (consumedIn : ∀ item ∈ consumed, item ∈ other)
    (evidence : ExecutionEvidence Y env flags consumed) : ExecutionEvidence (.or_i X Y) env flags other := by
  rcases evidence with unsigned | ⟨sig, hs, key, hk, checked⟩
  · exact Or.inl (unsigned_select_right_raw (unsigned_withSelector unsigned))
  · exact Or.inr ⟨sig, consumedIn sig hs, key, List.mem_append_right _ hk, checked⟩

theorem ambientExecution_or_i_B {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionBIn sc Y) :
    AmbientExecutionBIn sc (.or_i X Y) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  rcases or_i_run_B typedX typedY wfX wfY context.rules run with
      ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [trueElement] :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) activeIn
    exact evidence_or_i_left activeIn (executeX parent env flags parentArgs parentOther active top
      rest childContext (bounded_without_selector bounded) childRun truth)
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [falseElement] :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h) activeIn
    exact evidence_or_i_right activeIn (executeY parent env flags parentArgs parentOther active top
      rest childContext (bounded_without_selector bounded) childRun truth)

theorem ambientExecution_or_i_V {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.V, modsX⟩)
    (typedY : HasType sc Y ⟨.V, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (executeX : AmbientExecutionVIn sc X) (executeY : AmbientExecutionVIn sc Y) :
    AmbientExecutionVIn sc (.or_i X Y) := by
  intro parent env flags parentArgs parentOther consumed rest context bounded run
  rcases or_i_run_V typedX typedY wfX wfY context.rules run with
      ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [trueElement] :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) activeIn
    exact evidence_or_i_left activeIn (executeX parent env flags parentArgs parentOther active
      rest childContext (bounded_without_selector bounded) childRun)
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [falseElement] :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h) activeIn
    exact evidence_or_i_right activeIn (executeY parent env flags parentArgs parentOther active
      rest childContext (bounded_without_selector bounded) childRun)

theorem ambientExecution_verify {fragment : CoreFragment} (execute : AmbientExecutionBIn sc fragment) :
    AmbientExecutionVIn sc (.v fragment) := by
  intro parent env flags parentArgs parentOther consumed rest context bounded run
  have childContext : ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed :=
    ⟨context.sound, context.encoding, context.version, context.modeled, context.material,
      context.recover, context.canonical, context.thirdParty, context.childKeys,
      context.childLocks, context.consumedIn⟩
  have unfused := LeanMiniscript.Miniscript.Eval.compileVerify_success_inverse
    (compile_balancedControlFlow fragment) run
  obtain ⟨mid, midAlt, runX, verifyRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow fragment) unfused
  cases verifyRun with
  | verify_success top rest' script alt flags ctx result truth final =>
    cases final with
    | empty stack alt flags ctx =>
      exact execute parent env flags parentArgs parentOther consumed top rest childContext bounded runX truth
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
    simp [Opcode.isUpgradeableNop] at upgradable

theorem signed_consumption_of_malleability {fragment : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {consumed : Witness} {ty : MiniType} {mods : MalleabilityModifiers}
    (wf : fragment.WellFormed sc) (typed : HasType sc fragment ty)
    (mal : HasMalleability sc fragment mods) (signed : mods.s = true)
    (evidence : ExecutionEvidence fragment env flags consumed) :
    CheckedSignature fragment env flags consumed :=
  signed_execution_consumes ((malleabilityCandidateSound env wf typed mal).signedSat signed) evidence

theorem ambientExecution_c_pk_h (key : PubKey) : AmbientExecutionBIn sc (.c (.pk_h key)) := by
  intro parent env flags parentArgs parentOther consumed top rest context _bounded run truth
  obtain ⟨sig, pubkey, eq, imageEq, checked⟩ := accepts_c_pk_h_inversion run truth
  have consumedEq : consumed = [sig, pubkey] := witness_eq_pair_of_toInitialStack
    (List.append_cancel_right eq)
  have pubkeyEq : pubkey = key.bytes := context.thirdParty.2.2.2 pubkey
    (context.consumedIn pubkey (by simp [consumedEq]))
    key (context.childKeys key (by simp [CoreFragment.keys])) imageEq
  rw [pubkeyEq] at checked
  exact Or.inr ⟨sig, by simp [consumedEq], key, by simp [CoreFragment.keys], checked⟩

theorem ambientExecution_multi {k : Nat} {keys : List PubKey}
    (wf : (CoreFragment.multi k keys).WellFormed .p2wsh) : AmbientExecutionBIn .p2wsh (.multi k keys) := by
  intro parent env flags pa po own top rest context _ run truth
  obtain ⟨_, _, frame⟩ := context.saneFrame
  exact Or.inr (P2WSHRecovery.multi_checked frame wf context.encoding run truth)

theorem ambientExecution_multi_a (k : Nat) (keys : List PubKey)
    (threshold : validThreshold k keys.length) (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A) :
    AmbientExecutionB (.multi_a k keys) := by
  intro parent env flags parentArgs parentOther consumed top rest context _bounded run truth
  obtain ⟨sigs, eq, lengthEq, slots, count⟩ := MultiA.acceptsMultiAFrameInversion
    k keys threshold keyCount flags env.txCtx context.version run truth
  have initialEq : consumed.toInitialStack = sigs := List.append_cancel_right eq
  have nonempty : (sigs.filter (· ≠ falseElement)) ≠ [] := by
    intro empty
    rw [empty] at count
    have positive := threshold.1
    simp only [List.length_nil] at count
    omega
  obtain ⟨sig, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have sigMem : sig ∈ sigs := (List.mem_filter.mp member).1
  have notEmpty : sig ≠ falseElement := by simpa using (List.mem_filter.mp member).2
  obtain ⟨i, hi, equal⟩ := List.getElem_of_mem sigMem
  have slot := slots _ (MultiA.mem_zip_getElem lengthEq hi)
  change sigs[i] = falseElement ∨
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sigs[i]
      (keys[i]'(by omega)).bytes = .ok true at slot
  rw [equal] at slot
  have checked := slot.resolve_left notEmpty
  have inConsumed : sig ∈ consumed := by
    apply List.mem_reverse.mp
    change sig ∈ consumed.toInitialStack
    rw [initialEq]
    exact sigMem
  exact Or.inr ⟨sig, inConsumed, keys[i]'(by omega), List.getElem_mem _, checked⟩

theorem unsigned_combine {left right : CandidateResult}
    (leftUnsigned : RawUnsigned left) (rightUnsigned : RawUnsigned right) :
    RawUnsigned (left.combine right) := by
  obtain ⟨a, rfl, ha⟩ := leftUnsigned
  obtain ⟨b, rfl, hb⟩ := rightUnsigned
  exact ⟨a.combine b, rfl, by simp [SatisfactionCandidate.combine, ha, hb]⟩

theorem ambientExecution_and_v {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (executeX : AmbientExecutionVIn sc X) (executeY : AmbientExecutionBIn sc Y) :
    AmbientExecutionBIn sc (.and_v X Y) := by
  intro parent env flags parentArgs parentOther consumed top rest context bounded run truth
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, runY⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  obtain ⟨argsX, inputEqX, _⟩ := effectX.v_inv
  cases altEqX
  obtain ⟨consumedY, inputEqY⟩ := typed_B_input_frame typedY wfY runY
  have inputEq : consumed.toInitialStack = argsX ++ consumedY.toInitialStack := by
    apply List.append_cancel_right
    simpa [inputEqY, List.append_assoc] using inputEqX
  have consumedEq : consumed = consumedY ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  have inX : ∀ item ∈ argsX.reverse, item ∈ consumed := by
    intro item hi; rw [consumedEq]; exact List.mem_append_right _ hi
  have inY : ∀ item ∈ consumedY, item ∈ consumed := by
    intro item hi; rw [consumedEq]; exact List.mem_append_left _ hi
  have contextX := executionContext_restrict context
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context
    (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h) inY
  have boundX : ∀ item ∈ Witness.toInitialStack argsX.reverse ++ (consumedY.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    rw [inputEq] at bounded
    simpa only [Witness.toInitialStack, List.reverse_reverse, List.append_assoc] using bounded
  have childRunX : Eval (compile X) (Witness.toInitialStack argsX.reverse ++ (consumedY.toInitialStack ++ rest))
      [] flags env.txCtx (.success (consumedY.toInitialStack ++ rest) []) := by
    rw [inputEqX, inputEqY] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  have childRunY : Eval (compile Y) (consumedY.toInitialStack ++ rest)
      [] flags env.txCtx (.success (top :: rest) []) := by rw [← inputEqY]; exact runY
  have ex := executeX parent env flags parentArgs parentOther argsX.reverse
    (consumedY.toInitialStack ++ rest) contextX boundX childRunX
  have ey := executeY parent env flags parentArgs parentOther consumedY top rest contextY
    (fun item hi => boundX item (List.mem_append_right _ hi)) childRunY truth
  rcases ex with unsignedX | ⟨sig, hs, key, hk, checked⟩
  · rcases ey with unsignedY | ⟨sig, hs, key, hk, checked⟩
    · exact Or.inl (unsigned_combine unsignedX unsignedY)
    · exact Or.inr ⟨sig, inY sig hs, key, List.mem_append_right _ hk, checked⟩
  · exact Or.inr ⟨sig, inX sig hs, key, List.mem_append_left _ hk, checked⟩

end LeanMiniscript.Extraction.TapscriptRecovery.OrI

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrDC

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames OrI

def shortCircuit (keep : Bool) (X Y : CoreFragment) : CoreFragment :=
  if keep then .or_d X Y else .or_c X Y

def shortCircuitTail (keep : Bool) (body : Script) : Script :=
  (if keep then [.op .OP_IFDUP] else []) ++ [.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF]

theorem shortCircuit_keys (keep : Bool) (X Y : CoreFragment) :
    (shortCircuit keep X Y).keys = X.keys ++ Y.keys := by cases keep <;> rfl

theorem shortCircuit_locks (keep : Bool) (X Y : CoreFragment) :
    (shortCircuit keep X Y).hashLocks = X.hashLocks ++ Y.hashLocks := by cases keep <;> rfl

theorem shortCircuit_sat (keep : Bool) (X Y : CoreFragment) (env : SatEnv) :
    (satisfactionCandidates (shortCircuit keep X Y) env).sat =
      (satisfactionCandidates X env).sat.select
        ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat) := by
  cases keep <;> rfl

theorem rawUnsigned_candidate_iff (candidate : SatisfactionCandidate) :
    RawUnsigned (.candidate candidate) ↔ candidate.hasSig = false := by
  simp [RawUnsigned]

theorem select_usable_rows {left right : CandidateResult} {arguments : Witness}
    (selected : (left.select right).usableWitness? = some arguments) :
    (left.usableWitness? = some arguments ∧ ¬ RawUnsigned right) ∨
    (right.usableWitness? = some arguments ∧ ¬ RawUnsigned left) := by
  cases left with
  | impossible => exact Or.inr ⟨selected, by simp [RawUnsigned]⟩
  | candidate a =>
    cases right with
    | impossible => exact Or.inl ⟨selected, by simp [RawUnsigned]⟩
    | candidate b =>
      cases ha : a.hasSig <;> cases hb : b.hasSig
      · have unusable : (a.select b).status = .dontUse := by
          simp [SatisfactionCandidate.select, ha, hb]
        simp [CandidateResult.select, CandidateResult.usableWitness?, unusable] at selected
      · exact Or.inl ⟨by simpa [CandidateResult.select, SatisfactionCandidate.select, ha, hb] using selected,
          by simp [rawUnsigned_candidate_iff, hb]⟩
      · exact Or.inr ⟨by simpa [CandidateResult.select, SatisfactionCandidate.select, ha, hb] using selected,
          by simp [rawUnsigned_candidate_iff, ha]⟩
      · rcases CandidateResult.select_usableWitness_cases selected with h | h
        · exact Or.inl ⟨h, by simp [rawUnsigned_candidate_iff, hb]⟩
        · exact Or.inr ⟨h, by simp [rawUnsigned_candidate_iff, ha]⟩

theorem shortCircuit_candidate_cases {X Y : CoreFragment} {env : SatEnv} {arguments : Witness}
    (keep : Bool) (canonical : satisfy (shortCircuit keep X Y) env = some arguments) :
    (satisfy X env = some arguments ∧
      ¬ RawUnsigned ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)) ∨
    (∃ dsatX satY, arguments = satY ++ dsatX ∧ dissatisfy X env = some dsatX ∧
      satisfy Y env = some satY ∧ ¬ RawUnsigned (satisfactionCandidates X env).sat) := by
  unfold satisfy at canonical
  rw [shortCircuit_sat] at canonical
  rcases select_usable_rows canonical with left | ⟨right, excluded⟩
  · exact Or.inl left
  · obtain ⟨dsatX, satY, hx, hy, eq⟩ := CandidateResult.combine_usableWitness_iff.mp right
    exact Or.inr ⟨dsatX, satY, eq, hx, hy, excluded⟩

theorem shortCircuit_tail_cases {keep : Bool} {body : Script} {selector : StackElement}
    {rest alt out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval (shortCircuitTail keep body) (selector :: rest) alt flags ctx (.success out outAlt)) :
    (castToBool selector = true ∧ out = (if keep then selector :: rest else rest) ∧ outAlt = alt) ∨
    (castToBool selector = false ∧ Eval body rest alt flags ctx (.success out outAlt)) := by
  cases keep with
  | false => exact LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced run
  | true =>
    have combined : Eval ([.op .OP_IFDUP] ++ ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF]))
        (selector :: rest) alt flags ctx (.success out outAlt) := by
      simpa [shortCircuitTail, List.append_assoc] using run
    obtain ⟨mid, midAlt, dupRun, conditionalRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
        (.atom (by simp [NonConditional])) combined
    cases truth : castToBool selector with
    | false =>
      have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest) alt flags ctx
          (.success (selector :: rest) alt) :=
        Eval.ifdup_false selector rest alt [] flags ctx _ truth Eval.done
      have eq := Eval.result_unique dupRun canonicalDup
      cases eq
      rcases LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced conditionalRun with
          ⟨h, _, _⟩ | ⟨_, childRun⟩
      · simp [truth] at h
      · exact Or.inr ⟨rfl, childRun⟩
    | true =>
      have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest) alt flags ctx
          (.success (selector :: selector :: rest) alt) :=
        Eval.ifdup_true selector rest alt [] flags ctx _ truth Eval.done
      have eq := Eval.result_unique dupRun canonicalDup
      cases eq
      rcases LeanMiniscript.Miniscript.Eval.notifThen_success_cases balanced conditionalRun with
          ⟨_, outEq, altEq⟩ | ⟨h, _⟩
      · exact Or.inl ⟨rfl, outEq, altEq⟩
      · simp [truth] at h

theorem shortCircuit_run_cases {X Y : CoreFragment} {modsX : CorrectnessModifiers}
    {keep : Bool} {env : SatEnv} {flags : ScriptFlags} {input out : Stack}
    (typedX : HasType sc X ⟨.B, modsX⟩) (wfX : X.WellFormed sc)
    (run : Eval (compile (shortCircuit keep X Y)) input [] flags env.txCtx (.success out [])) :
    (∃ args rest top, input = args ++ rest ∧
      Eval (compile X) (args ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = true ∧ out = (if keep then top :: rest else rest)) ∨
    (∃ args rest top, input = args ++ rest ∧
      Eval (compile X) (args ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = false ∧ Eval (compile Y) rest [] flags env.txCtx (.success out [])) := by
  have combined : Eval (compile X ++ shortCircuitTail keep (compile Y)) input [] flags env.txCtx
      (.success out []) := by
    cases keep <;> simpa [shortCircuit, shortCircuitTail, compile, compileWithKeyHash,
      List.append_assoc] using run
  obtain ⟨mid, midAlt, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX input [] flags env.txCtx
    (.success mid midAlt) runX
  cases altEq
  obtain ⟨args, rest, top, inputEq, outputEq, _⟩ := effect.b_inv
  rw [outputEq] at tailRun runX
  rw [inputEq] at runX
  rcases shortCircuit_tail_cases (compile_balancedControlFlow Y) tailRun with
      ⟨truth, outEq, _⟩ | ⟨falsehood, runY⟩
  · exact Or.inl ⟨args, rest, top, inputEq, runX, truth, outEq⟩
  · exact Or.inr ⟨args, rest, top, inputEq, runX, falsehood, runY⟩

def modeBase (keep : Bool) : BaseType := if keep then .B else .V

def modeOutput (keep : Bool) (top : StackElement) (rest : Stack) : Stack :=
  if keep then top :: rest else rest

def modeAccept (keep : Bool) (top : StackElement) : Prop := keep = true → castToBool top = true

def ModeExecutionIn (sc : ScriptContext) (keep : Bool) (fragment : CoreFragment) : Prop :=
  if keep then AmbientExecutionBIn sc fragment else AmbientExecutionVIn sc fragment

abbrev ModeExecution := ModeExecutionIn .tapscript

theorem mode_input_frame {keep : Bool} {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {input rest : Stack} {top : StackElement}
    (typed : HasType sc fragment ⟨modeBase keep, mods⟩) (wf : fragment.WellFormed sc)
    (run : Eval (compile fragment) input [] flags env.txCtx (.success (modeOutput keep top rest) [])) :
    ∃ consumed : Witness, input = consumed.toInitialStack ++ rest := by
  cases keep
  · exact typed_V_input_frame typed wf run
  · exact typed_B_input_frame typed wf run

theorem shortCircuit_run_frame {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {keep : Bool} {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨modeBase keep, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (run : Eval (compile (shortCircuit keep X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (modeOutput keep top rest) [])) :
    (∃ value, Eval (compile X) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (value :: rest) []) ∧ castToBool value = true) ∨
    (∃ otherX otherY value, other = otherY ++ otherX ∧
      Eval (compile X) (otherX.toInitialStack ++ (otherY.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (value :: (otherY.toInitialStack ++ rest)) []) ∧
      castToBool value = false ∧
      Eval (compile Y) (otherY.toInitialStack ++ rest) [] flags env.txCtx
        (.success (modeOutput keep top rest) [])) := by
  rcases shortCircuit_run_cases typedX wfX run with
      ⟨args, tail, value, inputEq, runX, truth, outputEq⟩ |
      ⟨args, tail, value, inputEq, runX, falsehood, runY⟩
  · have tailEq : tail = rest := by
      cases keep
      · exact outputEq.symm
      · exact (List.cons.inj outputEq).2.symm
    subst tail
    exact Or.inl ⟨value, by rw [inputEq]; exact runX, truth⟩
  · obtain ⟨otherY, tailEq⟩ := mode_input_frame typedY wfY runY
    have stackEq : other.toInitialStack = args ++ otherY.toInitialStack := by
      apply List.append_cancel_right
      simpa [tailEq, List.append_assoc] using inputEq
    have otherEq : other = otherY ++ args.reverse := by
      simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
    refine Or.inr ⟨args.reverse, otherY, value, otherEq, ?_, falsehood, ?_⟩
    · rw [tailEq] at runX
      simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
    · rw [← tailEq]; exact runY

theorem expressive_rawUnsigned {fragment : CoreFragment} {ty : MiniType} {mods : MalleabilityModifiers}
    (wf : fragment.WellFormed sc) (typed : HasType sc fragment ty)
    (mal : HasMalleability sc fragment mods) (nm : mods.nonMalleable = true) (expressive : mods.e = true)
    (env : SatEnv) : RawUnsigned (satisfactionCandidates fragment env).dsat := by
  obtain ⟨candidate, eq, unsigned, _⟩ := (malleabilityCandidateSound env wf typed mal).expressiveDsat nm expressive
  exact ⟨candidate, eq, unsigned⟩

theorem shortCircuit_malleability_children {keep : Bool} {X Y : CoreFragment} {mods : MalleabilityModifiers}
    (mal : HasMalleability sc (shortCircuit keep X Y) mods) (nm : mods.nonMalleable = true) :
    ∃ mx my, HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.e = true ∧ (mx.s = true ∨ my.s = true) := by
  cases keep
  · cases mal with
    | or_c hx hy =>
      obtain ⟨nx, ny, ex, sig⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      exact ⟨_, _, hx, hy, nx, ny, ex, Bool.or_eq_true_iff.mp sig⟩
  · cases mal with
    | or_d hx hy =>
      obtain ⟨nx, ny, ex, sig⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      exact ⟨_, _, hx, hy, nx, ny, ex, Bool.or_eq_true_iff.mp sig⟩

def AmbientDsatCompleteIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed → fragment.keys.Nodup →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = false → ¬ CheckedSignature fragment env flags consumed →
    dissatisfy fragment env = some consumed

abbrev AmbientDsatComplete := AmbientDsatCompleteIn .tapscript

def UniformExecutionIn (sc : ScriptContext) (keep : Bool) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (modeOutput keep top rest) []) → modeAccept keep top →
    ExecutionEvidence fragment env flags consumed

abbrev UniformExecution := UniformExecutionIn .tapscript

theorem mode_execution_iff {keep : Bool} {fragment : CoreFragment} :
    ModeExecutionIn sc keep fragment ↔ UniformExecutionIn sc keep fragment := by
  cases keep
  · constructor
    · intro h parent env flags pa po other top rest context bound run _accept
      exact h parent env flags pa po other rest context bound run
    · intro h parent env flags pa po other rest context bound run
      exact h parent env flags pa po other falseElement rest context bound run (by intro impossible; cases impossible)
  · constructor
    · intro h parent env flags pa po other top rest context bound run accept
      exact h parent env flags pa po other top rest context bound run (accept rfl)
    · intro h parent env flags pa po other top rest context bound run truth
      exact h parent env flags pa po other top rest context bound run (fun _ => truth)

theorem evidence_shortCircuit_left {keep : Bool} {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed other : Witness} (consumedIn : ∀ item ∈ consumed, item ∈ other)
    (evidence : ExecutionEvidence X env flags consumed) :
    ExecutionEvidence (shortCircuit keep X Y) env flags other := by
  rcases evidence with unsigned | ⟨sig, hs, key, hk, checked⟩
  · apply Or.inl
    rw [shortCircuit_sat]
    exact unsigned_select_left_raw unsigned
  · exact Or.inr ⟨sig, consumedIn sig hs, key, by simp [shortCircuit_keys, hk], checked⟩

theorem evidence_shortCircuit_right {keep : Bool} {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed other : Witness} (consumedIn : ∀ item ∈ consumed, item ∈ other)
    (unsignedX : RawUnsigned (satisfactionCandidates X env).dsat)
    (evidence : ExecutionEvidence Y env flags consumed) :
    ExecutionEvidence (shortCircuit keep X Y) env flags other := by
  rcases evidence with unsigned | ⟨sig, hs, key, hk, checked⟩
  · apply Or.inl
    rw [shortCircuit_sat]
    exact unsigned_select_right_raw (unsigned_combine unsignedX unsigned)
  · exact Or.inr ⟨sig, consumedIn sig hs, key, by simp [shortCircuit_keys, hk], checked⟩

theorem ambientExecution_shortCircuit {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers} {keep : Bool}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨modeBase keep, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (executeX : AmbientExecutionBIn sc X) (executeY : ModeExecutionIn sc keep Y)
    (unsignedX : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat) :
    ModeExecutionIn sc keep (shortCircuit keep X Y) := by
  apply mode_execution_iff.mpr
  intro parent env flags parentArgs parentOther other top rest context bounded run accept
  rcases shortCircuit_run_frame typedX typedY wfX wfY run with
      ⟨value, runX, truth⟩ | ⟨otherX, otherY, value, otherEq, runX, falsehood, runY⟩
  · have contextX := executionContext_restrict context
      (active := X) (fun k hk => by simp [shortCircuit_keys, hk])
      (fun l hl => by simp [shortCircuit_locks, hl]) (fun _ h => h)
    exact evidence_shortCircuit_left (fun _ h => h)
      (executeX parent env flags parentArgs parentOther other value rest contextX bounded runX truth)
  · subst other
    have inY : ∀ item ∈ otherY, item ∈ otherY ++ otherX := fun _ h => List.mem_append_left _ h
    have contextY := executionContext_restrict context
      (active := Y) (fun k hk => by simp [shortCircuit_keys, hk])
      (fun l hl => by simp [shortCircuit_locks, hl]) inY
    have boundAll : ∀ item ∈ otherX.toInitialStack ++ (otherY.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    exact evidence_shortCircuit_right inY (unsignedX env)
      ((mode_execution_iff.mp executeY) parent env flags parentArgs parentOther otherY top rest contextY
        (fun item hi => boundAll item (List.mem_append_right _ hi)) runY accept)

theorem false_c_pk_k_inversion {flags : ScriptFlags} {ctx : TxContext} {key : PubKey}
    {input rest : Stack} {top : StackElement}
    (version : Active.WitnessRules flags ctx)
    (run : Eval (compile (.c (.pk_k key))) input [] flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) : input = falseElement :: rest := by
  change Eval [.pushData key.bytes, .op .OP_CHECKSIG] input [] flags ctx (.success (top :: rest) []) at run
  cases run with
  | pushData data script stack alt flags ctx result inner =>
    cases inner with
    | checksig_success pubkey sig tail script alt flags ctx result checked final =>
      cases final with
      | empty stack alt flags ctx => simp [castToBool, trueElement] at falsehood
    | checksig_failure pubkey sig tail script alt flags ctx result checked final =>
      cases final with
      | empty stack alt flags ctx =>
        rw [Active.false_signature_empty version checked]
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem ambientDsatComplete_c_pk_k (key : PubKey) : AmbientDsatCompleteIn sc (.c (.pk_k key)) := by
  intro parent env flags parentArgs parentOther consumed top rest context _noDup _bounded run falsehood _noChecked
  have stackEq := false_c_pk_k_inversion context.rules run falsehood
  have eq : consumed = [falseElement] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right stackEq)
  rw [eq]
  rfl

theorem false_c_pk_h_inversion {flags : ScriptFlags} {ctx : TxContext} {key : PubKey}
    {input rest : Stack} {top : StackElement}
    (version : Active.WitnessRules flags ctx)
    (run : Eval (compile (.c (.pk_h key))) input [] flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ pubkey, input = pubkey :: falseElement :: rest ∧
      LeanMiniscript.Script.hash160 pubkey = LeanMiniscript.Script.hash160 key.bytes := by
  change Eval [.op .OP_DUP, .op .OP_HASH160, .pushData (LeanMiniscript.Script.hash160 key.bytes),
    .op .OP_EQUALVERIFY, .op .OP_CHECKSIG] input [] flags ctx (.success (top :: rest) []) at run
  cases run with
  | dup x tail script alt flags ctx result inner =>
    cases inner with
    | op_hash160 x' tail script alt flags ctx result inner =>
      cases inner with
      | pushData data script stack alt flags ctx result inner =>
        cases inner with
        | equalverify_success a b tail script alt flags ctx result imageEq inner =>
          cases inner with
          | checksig_success pubkey sig tail script alt flags ctx result checked final =>
            cases final with
            | empty stack alt flags ctx => simp [castToBool, trueElement] at falsehood
          | checksig_failure pubkey sig tail script alt flags ctx result checked final =>
            cases final with
            | empty stack alt flags ctx =>
              exact ⟨x, by rw [Active.false_signature_empty version checked],
                imageEq.symm⟩
          | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
        | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem ambientDsatComplete_c_pk_h (key : PubKey) : AmbientDsatCompleteIn sc (.c (.pk_h key)) := by
  intro parent env flags parentArgs parentOther consumed top rest context _noDup _bounded run falsehood _noChecked
  obtain ⟨pubkey, stackEq, imageEq⟩ := false_c_pk_h_inversion context.rules run falsehood
  have consumedEq : consumed = [falseElement, pubkey] :=
    witness_eq_pair_of_toInitialStack (List.append_cancel_right stackEq)
  have pubkeyEq : pubkey = key.bytes := context.thirdParty.2.2.2 pubkey
    (context.consumedIn pubkey (by simp [consumedEq]))
    key (context.childKeys key (by simp [CoreFragment.keys])) imageEq
  rw [consumedEq, pubkeyEq]
  rfl

end LeanMiniscript.Extraction.TapscriptRecovery.OrDC
