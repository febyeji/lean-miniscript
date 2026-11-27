import LeanMiniscript.Extraction.TapscriptRecovery.BranchExecution

/-! Relate dissatisfaction candidates and forced or signed executions of and_v. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.Dsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC

theorem rawUnsigned_select_signed_eq {left right : CandidateResult}
    (unsigned : RawUnsigned left) (signed : right.Signed) : left.select right = left := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases right with
  | impossible => rfl
  | candidate other => simp [CandidateResult.select, SatisfactionCandidate.select, h, signed other rfl]

theorem signed_select_rawUnsigned_eq {left right : CandidateResult}
    (signed : left.Signed) (unsigned : RawUnsigned right) : left.select right = right := by
  obtain ⟨candidate, rfl, h⟩ := unsigned
  cases left with
  | impossible => rfl
  | candidate other => simp [CandidateResult.select, SatisfactionCandidate.select, h, signed other rfl]

theorem dsat_or_i_left_eq {X Y : CoreFragment} {env : SatEnv}
    (unsigned : RawUnsigned (satisfactionCandidates X env).dsat)
    (forced : (satisfactionCandidates Y env).dsat.Signed) :
    (satisfactionCandidates (.or_i X Y) env).dsat =
      (satisfactionCandidates X env).dsat.withSelector trueElement :=
  rawUnsigned_select_signed_eq (unsigned_withSelector unsigned) (forced.withSelector _)

theorem dsat_or_i_right_eq {X Y : CoreFragment} {env : SatEnv}
    (forced : (satisfactionCandidates X env).dsat.Signed)
    (unsigned : RawUnsigned (satisfactionCandidates Y env).dsat) :
    (satisfactionCandidates (.or_i X Y) env).dsat =
      (satisfactionCandidates Y env).dsat.withSelector falseElement :=
  signed_select_rawUnsigned_eq (forced.withSelector _) (unsigned_withSelector unsigned)

theorem or_i_expressive_children {X Y : CoreFragment} {mods : MalleabilityModifiers}
    (mal : HasMalleability sc (.or_i X Y) mods)
    (nm : mods.nonMalleable = true) (expressive : mods.e = true) :
    ∃ mx my, HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      ((mx.e = true ∧ my.f = true) ∨ (my.e = true ∧ mx.f = true)) := by
  cases mal with
  | or_i hx hy =>
    have both := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp nm).1)
    refine ⟨_, _, hx, hy, both.1, both.2, ?_⟩
    rcases Bool.or_eq_true_iff.mp expressive with left | right
    · exact Or.inl (Bool.and_eq_true_iff.mp left)
    · exact Or.inr (Bool.and_eq_true_iff.mp right)

def AmbientFalseEvidenceIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = false →
    RawUnsigned (satisfactionCandidates fragment env).dsat ∨ CheckedSignature fragment env flags consumed

abbrev AmbientFalseEvidence := AmbientFalseEvidenceIn .tapscript

def AmbientForcedFalseIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed → fragment.keys.Nodup →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = false → CheckedSignature fragment env flags consumed

abbrev AmbientForcedFalse := AmbientForcedFalseIn .tapscript

theorem forcedFalse_of_evidence {fragment : CoreFragment}
    (forced : ∀ env, (satisfactionCandidates fragment env).dsat.Signed)
    (evidence : AmbientFalseEvidenceIn sc fragment) : AmbientForcedFalseIn sc fragment := by
  intro parent env flags pa po consumed top rest context _nodup bound run falsehood
  rcases evidence parent env flags pa po consumed top rest context bound run falsehood with unsigned | checked
  · exact (signed_excludes_unsigned (forced env) unsigned).elim
  · exact checked

theorem checkedSignature_mono {child parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {consumed other : Witness} (keys : ∀ key ∈ child.keys, key ∈ parent.keys)
    (items : ∀ item ∈ consumed, item ∈ other)
    (checked : CheckedSignature child env flags consumed) : CheckedSignature parent env flags other := by
  obtain ⟨sig, hs, key, hk, check⟩ := checked
  exact ⟨sig, items sig hs, key, keys key hk, check⟩

theorem ambientDsatComplete_or_i_left {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (unsignedX : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat)
    (forcedY : ∀ env, (satisfactionCandidates Y env).dsat.Signed)
    (completeX : AmbientDsatCompleteIn sc X) (runtimeY : AmbientForcedFalseIn sc Y) :
    AmbientDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po consumed top rest context nodup bounded run falsehood absent
  rcases or_i_run_B typedX typedY wfX wfY context.rules run with
      ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [trueElement] :=
      fun _ h => List.mem_append_left _ h
    have childKeys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context childKeys
      (fun _ h => List.mem_append_left _ h) activeIn
    have childAbsent : ¬ CheckedSignature X env flags active :=
      fun checked => absent (checkedSignature_mono childKeys activeIn checked)
    have canonical := completeX parent env flags pa po active top rest childContext
      (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) childRun falsehood childAbsent
    change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = some (active ++ [trueElement])
    rw [dsat_or_i_left_eq (unsignedX env) (forcedY env)]
    apply CandidateResult.withSelector_usableWitness_iff.mpr
    exact ⟨active, canonical, rfl⟩
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [falseElement] :=
      fun _ h => List.mem_append_left _ h
    have childKeys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_right _ h
    have childContext := executionContext_restrict context childKeys
      (fun _ h => List.mem_append_right _ h) activeIn
    have checked := runtimeY parent env flags pa po active top rest childContext
      (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) childRun falsehood
    exact (absent (checkedSignature_mono childKeys activeIn checked)).elim

theorem ambientDsatComplete_or_i_right {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (unsignedY : ∀ env, RawUnsigned (satisfactionCandidates Y env).dsat)
    (forcedX : ∀ env, (satisfactionCandidates X env).dsat.Signed)
    (completeY : AmbientDsatCompleteIn sc Y) (runtimeX : AmbientForcedFalseIn sc X) :
    AmbientDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po consumed top rest context nodup bounded run falsehood absent
  rcases or_i_run_B typedX typedY wfX wfY context.rules run with
      ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [trueElement] :=
      fun _ h => List.mem_append_left _ h
    have childKeys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_left _ h
    have childContext := executionContext_restrict context childKeys
      (fun _ h => List.mem_append_left _ h) activeIn
    have checked := runtimeX parent env flags pa po active top rest childContext
      (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) childRun falsehood
    exact (absent (checkedSignature_mono childKeys activeIn checked)).elim
  · subst consumed
    have activeIn : ∀ item ∈ active, item ∈ active ++ [falseElement] :=
      fun _ h => List.mem_append_left _ h
    have childKeys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_right _ h
    have childContext := executionContext_restrict context childKeys
      (fun _ h => List.mem_append_right _ h) activeIn
    have childAbsent : ¬ CheckedSignature Y env flags active :=
      fun checked => absent (checkedSignature_mono childKeys activeIn checked)
    have canonical := completeY parent env flags pa po active top rest childContext
      (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) childRun falsehood childAbsent
    change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = some (active ++ [falseElement])
    rw [dsat_or_i_right_eq (forcedX env) (unsignedY env)]
    apply CandidateResult.withSelector_usableWitness_iff.mpr
    exact ⟨active, canonical, rfl⟩

theorem or_d_false_run_frame {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (run : Eval (compile (.or_d X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ otherX otherY value, other = otherY ++ otherX ∧
      Eval (compile X) (otherX.toInitialStack ++ (otherY.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (value :: (otherY.toInitialStack ++ rest)) []) ∧ castToBool value = false ∧
      Eval (compile Y) (otherY.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
  rcases shortCircuit_run_cases (keep := true) typedX wfX run with
      ⟨args, tail, value, inputEq, runX, truth, outputEq⟩ |
      ⟨args, tail, value, inputEq, runX, falseX, runY⟩
  · have valueEq : top = value := (List.cons.inj outputEq).1
    rw [valueEq, truth] at falsehood
    cases falsehood
  · obtain ⟨otherY, tailEq⟩ := typed_B_input_frame typedY wfY runY
    have stackEq : other.toInitialStack = args ++ otherY.toInitialStack := by
      apply List.append_cancel_right
      simpa [tailEq, List.append_assoc] using inputEq
    have otherEq : other = otherY ++ args.reverse := by
      simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
    refine ⟨args.reverse, otherY, value, otherEq, ?_, falseX, ?_⟩
    · rw [tailEq] at runX
      simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
    · rw [← tailEq]; exact runY

theorem ambientDsatComplete_or_d {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (completeX : AmbientDsatCompleteIn sc X) (completeY : AmbientDsatCompleteIn sc Y) :
    AmbientDsatCompleteIn sc (.or_d X Y) := by
  intro parent env flags pa po consumed top rest context nodup bounded run falsehood absent
  obtain ⟨otherX, otherY, value, eq, runX, falseX, runY⟩ :=
    or_d_false_run_frame typedX typedY wfX wfY run falsehood
  subst consumed
  have inX : ∀ item ∈ otherX, item ∈ otherY ++ otherX := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ otherY, item ∈ otherY ++ otherX := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_right _ h
  have contextX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have boundAll : ∀ item ∈ otherX.toInitialStack ++ (otherY.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have dsatX := completeX parent env flags pa po otherX value (otherY.toInitialStack ++ rest)
    contextX (List.pairwise_append.mp nodup).1 boundAll runX falseX
    (fun checked => absent (checkedSignature_mono keysX inX checked))
  have dsatY := completeY parent env flags pa po otherY top rest contextY (List.pairwise_append.mp nodup).2.1
    (fun item hi => boundAll item (List.mem_append_right _ hi)) runY falsehood
    (fun checked => absent (checkedSignature_mono keysY inY checked))
  apply CandidateResult.combine_usableWitness_iff.mpr
  exact ⟨otherX, otherY, dsatX, dsatY, rfl⟩

theorem and_v_run_B_frame {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack} {top : StackElement}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (run : Eval (compile (.and_v X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    ∃ otherX otherY, other = otherY ++ otherX ∧
      Eval (compile X) (otherX.toInitialStack ++ (otherY.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (otherY.toInitialStack ++ rest) []) ∧
      Eval (compile Y) (otherY.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, runY⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  obtain ⟨argsX, inputEqX, _⟩ := effectX.v_inv
  cases altEqX
  obtain ⟨otherY, inputEqY⟩ := typed_B_input_frame typedY wfY runY
  have inputEq : other.toInitialStack = argsX ++ otherY.toInitialStack := by
    apply List.append_cancel_right
    simpa [inputEqY, List.append_assoc] using inputEqX
  have otherEq : other = otherY ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, otherY, otherEq, ?_, ?_⟩
  · rw [inputEqX, inputEqY] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← inputEqY]; exact runY

theorem ambientFalseEvidence_one : AmbientFalseEvidenceIn sc .one := by
  intro parent env flags pa po consumed top rest _context _bounded run falsehood
  have canonical : Eval (compile .one) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (scriptNum 1 :: (consumed.toInitialStack ++ rest)) []) := by
    apply Eval.pushNum
    exact Eval.done
  have eq := Eval.result_unique run canonical
  have topEq : top = scriptNum 1 := (List.cons.inj (ExecResult.success.inj eq).1).1
  rw [topEq] at falsehood
  change true = false at falsehood
  cases falsehood

theorem ambientForcedFalse_one : AmbientForcedFalseIn sc .one :=
  forcedFalse_of_evidence (fun _ => CandidateResult.signed_impossible) ambientFalseEvidence_one

end LeanMiniscript.Extraction.TapscriptRecovery.Dsat

namespace LeanMiniscript.Extraction.TapscriptRecovery.ForcedAndV

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat

def AmbientSignedVIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (parentArgs parentOther consumed : Witness) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags parentArgs parentOther consumed → fragment.keys.Nodup →
    (∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) →
    CheckedSignature fragment env flags consumed

abbrev AmbientSignedV := AmbientSignedVIn .tapscript

theorem signedV_of_execution {fragment : CoreFragment}
    (signed : ∀ env, (satisfactionCandidates fragment env).sat.Signed)
    (execute : AmbientExecutionVIn sc fragment) : AmbientSignedVIn sc fragment := by
  intro parent env flags pa po consumed rest context _nodup bounded run
  exact signed_execution_consumes (signed env)
    (execute parent env flags pa po consumed rest context bounded run)

theorem signedV_of_malleability {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (signed : malMods.s = true)
    (execute : AmbientExecutionVIn sc fragment) : AmbientSignedVIn sc fragment :=
  signedV_of_execution (fun env => (malleabilityCandidateSound env wf typed mal).signedSat signed) execute

theorem and_v_B_typed_children {X Y : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc (.and_v X Y) ⟨.B, mods⟩) :
    ∃ modsX modsY, HasType sc X ⟨.V, modsX⟩ ∧ HasType sc Y ⟨.B, modsY⟩ := by
  generalize typeEq : (⟨.B, mods⟩ : MiniType) = parentType at typed
  cases typed with
  | @and_v first second firstMods secondType typedX typedY _branch =>
    have baseEq : secondType.base = .B := (congrArg MiniType.base typeEq).symm
    refine ⟨firstMods, secondType.mods, typedX, ?_⟩
    cases secondType with
    | mk base modsY =>
      change base = .B at baseEq
      subst base
      exact typedY

theorem and_v_false_contexts {parent X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po left right : Witness} {rest : Stack}
    (context : ExecutionContextIn sc parent (.and_v X Y) env flags pa po (right ++ left))
    (nodup : (CoreFragment.and_v X Y).keys.Nodup)
    (bounded : ∀ item ∈ (right ++ left).toInitialStack ++ rest, item.size ≤ maxScriptElementSize) :
    ExecutionContextIn sc parent X env flags pa po left ∧ ExecutionContextIn sc parent Y env flags pa po right ∧
    X.keys.Nodup ∧ Y.keys.Nodup ∧
    (∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) ∧
    (∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) := by
  have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  exact ⟨executionContext_restrict context (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h),
    executionContext_restrict context (fun _ h => List.mem_append_right _ h)
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_left _ h),
    (List.pairwise_append.mp nodup).1, (List.pairwise_append.mp nodup).2.1,
    boundAll, fun item hi => boundAll item (List.mem_append_right _ hi)⟩

theorem forced_and_v_of_signed_prefix {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (signedPrefix : AmbientSignedVIn sc X) : AmbientForcedFalseIn sc (.and_v X Y) := by
  intro parent env flags pa po consumed top rest context nodup bounded run _falsehood
  obtain ⟨left, right, eq, runX, _runY⟩ := and_v_run_B_frame typedX typedY wfX wfY run
  subst consumed
  obtain ⟨contextX, _contextY, nodupX, _nodupY, boundX, _boundY⟩ := and_v_false_contexts context nodup bounded
  have checked := signedPrefix parent env flags pa po left (right.toInitialStack ++ rest) contextX nodupX boundX runX
  exact checkedSignature_mono (fun _ h => List.mem_append_left _ h)
    (fun _ h => List.mem_append_right _ h) checked

theorem forced_and_v_of_forced_child {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.B, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (child : AmbientForcedFalseIn sc Y) : AmbientForcedFalseIn sc (.and_v X Y) := by
  intro parent env flags pa po consumed top rest context nodup bounded run falsehood
  obtain ⟨left, right, eq, _runX, runY⟩ := and_v_run_B_frame typedX typedY wfX wfY run
  subst consumed
  obtain ⟨_contextX, contextY, _nodupX, nodupY, _boundX, boundY⟩ := and_v_false_contexts context nodup bounded
  have checked := child parent env flags pa po right top rest contextY nodupY boundY runY falsehood
  exact checkedSignature_mono (fun _ h => List.mem_append_right _ h)
    (fun _ h => List.mem_append_left _ h) checked

theorem and_v_run_V_frame {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.V, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (run : Eval (compile (.and_v X Y)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) :
    ∃ left right, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (right.toInitialStack ++ rest) []) ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) := by
  change Eval (compile X ++ compile Y) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, runY⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  obtain ⟨argsX, inputEqX, _⟩ := effect.v_inv
  cases altEq
  obtain ⟨right, inputEqY⟩ := typed_V_input_frame typedY wfY runY
  have stackEq : other.toInitialStack = argsX ++ right.toInitialStack := by
    apply List.append_cancel_right
    simpa [inputEqY, List.append_assoc] using inputEqX
  have otherEq : other = right ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  refine ⟨argsX.reverse, right, otherEq, ?_, ?_⟩
  · rw [inputEqX, inputEqY] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← inputEqY]; exact runY

theorem ambientExecutionV_and_v {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.V, modsX⟩) (typedY : HasType sc Y ⟨.V, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (executeX : AmbientExecutionVIn sc X) (executeY : AmbientExecutionVIn sc Y) :
    AmbientExecutionVIn sc (.and_v X Y) := by
  intro parent env flags pa po consumed rest context bounded run
  obtain ⟨left, right, eq, runX, runY⟩ := and_v_run_V_frame typedX typedY wfX wfY run
  subst consumed
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_right _ h
  have contextX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have ex := executeX parent env flags pa po left (right.toInitialStack ++ rest) contextX boundAll runX
  have ey := executeY parent env flags pa po right rest contextY
    (fun item hi => boundAll item (List.mem_append_right _ hi)) runY
  rcases ex with unsignedX | checkedX
  · rcases ey with unsignedY | checkedY
    · exact Or.inl (unsigned_combine unsignedX unsignedY)
    · exact Or.inr (checkedSignature_mono keysY inY checkedY)
  · exact Or.inr (checkedSignature_mono keysX inX checkedX)

theorem ambientExecutionV_or_c_from_children {X Y : CoreFragment} {modsX modsY : CorrectnessModifiers}
    {mods : MalleabilityModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩) (typedY : HasType sc Y ⟨.V, modsY⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc)
    (mal : HasMalleability sc (.or_c X Y) mods) (nm : mods.nonMalleable = true)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionVIn sc Y) : AmbientExecutionVIn sc (.or_c X Y) := by
  obtain ⟨mx, my, hx, _hy, nx, _ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
  exact ambientExecution_shortCircuit (keep := false) typedX typedY wfX wfY executeX executeY
    (expressive_rawUnsigned wfX typedX hx nx ex)

end LeanMiniscript.Extraction.TapscriptRecovery.ForcedAndV

namespace LeanMiniscript.Extraction.TapscriptRecovery.SignedV

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI OrDC Dsat ForcedAndV

inductive VShapeIn (sc : ScriptContext) : CoreFragment → Prop where
  | verify {X : CoreFragment} {mx : CorrectnessModifiers}
      (typed : HasType sc X ⟨.B, mx⟩) : VShapeIn sc (.v X)
  | and_v {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.V, mx⟩)
      (typedY : HasType sc Y ⟨.V, my⟩) : VShapeIn sc (.and_v X Y)
  | or_c {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩) (d : mx.d = true) (u : mx.u = true)
      (typedY : HasType sc Y ⟨.V, my⟩) : VShapeIn sc (.or_c X Y)
  | or_i {X Y : CoreFragment} {mx my : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.V, mx⟩)
      (typedY : HasType sc Y ⟨.V, my⟩) : VShapeIn sc (.or_i X Y)
  | andor {X Y Z : CoreFragment} {mx my mz : CorrectnessModifiers}
      (typedX : HasType sc X ⟨.B, mx⟩) (d : mx.d = true) (u : mx.u = true)
      (typedY : HasType sc Y ⟨.V, my⟩)
      (typedZ : HasType sc Z ⟨.V, mz⟩) : VShapeIn sc (.andor X Y Z)

abbrev VShape := VShapeIn .tapscript

theorem typed_V_shape {fragment : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.V, mods⟩) : VShapeIn sc fragment := by
  generalize typeEq : (⟨.V, mods⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case and_v typedX typedY _branch =>
    rename_i tyY
    cases tyY with
    | mk base modsY =>
      change BaseType.V = base at baseEq
      subst base
      exact .and_v typedX typedY
  case or_c typedX d u typedY => exact .or_c typedX d u typedY
  case or_i typedX typedY _branch sameBase =>
    rename_i tyX tyY
    cases tyX with
    | mk baseX modsX =>
      change BaseType.V = baseX at baseEq
      subst baseX
      cases tyY with
      | mk baseY modsY =>
        change BaseType.V = baseY at sameBase
        subst baseY
        exact .or_i typedX typedY
  case andor typedX d u typedY typedZ _branch sameBase =>
    rename_i tyY tyZ
    cases tyY with
    | mk baseY modsY =>
      change BaseType.V = baseY at baseEq
      subst baseY
      cases tyZ with
      | mk baseZ modsZ =>
        change BaseType.V = baseZ at sameBase
        subst baseZ
        exact .andor typedX d u typedY typedZ
  case v_wrap typedX => exact .verify typedX

theorem conditional_split_closed {thenBranch elseBranch : Script}
    (thenBalanced : BalancedControlFlow thenBranch) (elseBalanced : BalancedControlFlow elseBranch) :
    splitConditional (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
      some { branches := [thenBranch, elseBranch], after := [] } := by
  simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced (suffix := [])

theorem notifElse_truth_cases {thenBranch elseBranch : Script} {selector : StackElement}
    {rest alt out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (thenBalanced : BalancedControlFlow thenBranch) (elseBalanced : BalancedControlFlow elseBranch)
    (run : Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF])
      (selector :: rest) alt flags ctx (.success out outAlt)) :
    (castToBool selector = false ∧ Eval thenBranch rest alt flags ctx (.success out outAlt)) ∨
    (castToBool selector = true ∧ Eval elseBranch rest alt flags ctx (.success out outAlt)) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case notif_execute =>
    rename_i frame split minimal selected
    cases resultEq
    change splitConditional (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) = some frame at split
    rw [conditional_split_closed thenBalanced elseBalanced] at split
    cases split
    cases selectedBool : castToBool selector
    · exact Or.inl ⟨rfl, by simpa [ConditionalFrame.select, selectConditionalBranches, selectedBool] using selected⟩
    · exact Or.inr ⟨rfl, by simpa [ConditionalFrame.select, selectConditionalBranches, selectedBool] using selected⟩
  case notif_unbalanced =>
    rename_i selectedResult split minimal selected
    change splitConditional (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) = none at split
    rw [conditional_split_closed thenBalanced elseBalanced] at split
    contradiction
  all_goals cases resultEq

theorem branch_V_frame {X Y : CoreFragment} {modsY : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest args tail : Stack} {top : StackElement}
    (typedY : HasType sc Y ⟨.V, modsY⟩) (wfY : Y.WellFormed sc)
    (inputEq : other.toInitialStack ++ rest = args ++ tail)
    (runX : Eval (compile X) (args ++ tail) [] flags env.txCtx (.success (top :: tail) []))
    (runY : Eval (compile Y) tail [] flags env.txCtx (.success rest [])) :
    ∃ left right, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) := by
  obtain ⟨right, tailEq⟩ := typed_V_input_frame typedY wfY runY
  have stackEq : other.toInitialStack = args ++ right.toInitialStack := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputEq
  have otherEq : other = right ++ args.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  refine ⟨args.reverse, right, otherEq, ?_, ?_⟩
  · rw [tailEq] at runX
    simpa only [Witness.toInitialStack, List.reverse_reverse] using runX
  · rw [← tailEq]; exact runY

theorem andor_run_V_frame {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {rest : Stack}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.V, modsY⟩) (typedZ : HasType sc Z ⟨.V, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
    (run : Eval (compile (.andor X Y Z)) (other.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) :
    (∃ left right top, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧ castToBool top = false ∧
      Eval (compile Z) (right.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) ∨
    (∃ left right top, other = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧ castToBool top = true ∧
      Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) := by
  have combined : Eval (compile X ++ ([.op .OP_NOTIF] ++ compile Z ++ [.op .OP_ELSE] ++ compile Y ++ [.op .OP_ENDIF]))
      (other.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, midAlt, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX
    (other.toInitialStack ++ rest) [] flags env.txCtx (.success mid midAlt) runX
  cases altEq
  obtain ⟨args, tail, top, inputEq, outputEq, _⟩ := effect.b_inv
  rw [outputEq] at tailRun runX
  rw [inputEq] at runX
  rcases notifElse_truth_cases (compile_balancedControlFlow Z) (compile_balancedControlFlow Y) tailRun with
      ⟨falsehood, runZ⟩ | ⟨truth, runY⟩
  · obtain ⟨left, right, eq, rx, rz⟩ := branch_V_frame typedZ wfZ inputEq runX runZ
    exact Or.inl ⟨left, right, top, eq, rx, falsehood, rz⟩
  · obtain ⟨left, right, eq, rx, ry⟩ := branch_V_frame typedY wfY inputEq runX runY
    exact Or.inr ⟨left, right, top, eq, rx, truth, ry⟩

theorem andor_malleability_children {X Y Z : CoreFragment} {mods : MalleabilityModifiers}
    (mal : HasMalleability sc (.andor X Y Z) mods) (nm : mods.nonMalleable = true) :
    ∃ mx my mz, HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      HasMalleability sc Z mz ∧ mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      mz.nonMalleable = true ∧ mx.e = true := by
  cases mal with
  | andor hx hy hz =>
    obtain ⟨nx, ny, nz, ex, _signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    exact ⟨_, _, _, hx, hy, hz, nx, ny, nz, ex⟩

theorem ambientExecutionV_andor {X Y Z : CoreFragment} {modsX modsY modsZ : CorrectnessModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.V, modsY⟩) (typedZ : HasType sc Z ⟨.V, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionVIn sc Y) (executeZ : AmbientExecutionVIn sc Z)
    (unsignedX : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat) :
    AmbientExecutionVIn sc (.andor X Y Z) := by
  intro parent env flags pa po consumed rest context bounded run
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  rcases andor_run_V_frame typedX typedY typedZ wfX wfY wfZ run with
      ⟨left, right, top, eq, _runX, _falsehood, runZ⟩ | ⟨left, right, top, eq, runX, truth, runY⟩
  · subst consumed
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases executeZ parent env flags pa po right rest contextZ
      (fun item hi => boundAll item (List.mem_append_right _ hi)) runZ with unsignedZ | checkedZ
    · exact Or.inl (unsigned_select_right_raw (unsigned_combine (unsignedX env) unsignedZ))
    · exact Or.inr (checkedSignature_mono keysZ inZ checkedZ)
  · subst consumed
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have contextY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases executeX parent env flags pa po left top (right.toInitialStack ++ rest) contextX boundAll runX truth
      with unsignedX | checkedX
    · rcases executeY parent env flags pa po right rest contextY
        (fun item hi => boundAll item (List.mem_append_right _ hi)) runY with unsignedY | checkedY
      · exact Or.inl (unsigned_select_left_raw (unsigned_combine unsignedX unsignedY))
      · exact Or.inr (checkedSignature_mono keysY inY checkedY)
    · exact Or.inr (checkedSignature_mono keysX inX checkedX)

theorem ambientExecutionV_andor_from_children {X Y Z : CoreFragment}
    {modsX modsY modsZ : CorrectnessModifiers} {mods : MalleabilityModifiers}
    (typedX : HasType sc X ⟨.B, modsX⟩)
    (typedY : HasType sc Y ⟨.V, modsY⟩) (typedZ : HasType sc Z ⟨.V, modsZ⟩)
    (wfX : X.WellFormed sc) (wfY : Y.WellFormed sc) (wfZ : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mods) (nm : mods.nonMalleable = true)
    (executeX : AmbientExecutionBIn sc X) (executeY : AmbientExecutionVIn sc Y) (executeZ : AmbientExecutionVIn sc Z) :
    AmbientExecutionVIn sc (.andor X Y Z) := by
  obtain ⟨mx, _my, _mz, hx, _hy, _hz, nx, _ny, _nz, ex⟩ := andor_malleability_children mal nm
  exact ambientExecutionV_andor typedX typedY typedZ wfX wfY wfZ executeX executeY executeZ
    (expressive_rawUnsigned wfX typedX hx nx ex)

def VBoundary : CoreFragment → CoreFragment → Prop
  | .v X, child => child = X
  | .and_v X Y, child => VBoundary X child ∨ VBoundary Y child
  | .or_c X Y, child => child = X ∨ VBoundary Y child
  | .or_i X Y, child => VBoundary X child ∨ VBoundary Y child
  | .andor X Y Z, child => child = X ∨ VBoundary Y child ∨ VBoundary Z child
  | _, _ => False

def BExecutionPremiseIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (mods : CorrectnessModifiers) (malMods : MalleabilityModifiers),
    HasType sc fragment ⟨.B, mods⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment malMods → malMods.nonMalleable = true → AmbientExecutionBIn sc fragment

abbrev BExecutionPremise := BExecutionPremiseIn .tapscript

theorem ambientExecutionV_from_boundary {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (boundary : ∀ child, VBoundary fragment child → BExecutionPremiseIn sc child) : AmbientExecutionVIn sc fragment := by
  cases typed_V_shape typed with
  | verify childTyped =>
    cases mal with
    | v childMal =>
      exact ambientExecution_verify (boundary _ rfl _ _ childTyped wf childMal nm)
  | and_v typedX typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
    exact ambientExecutionV_and_v typedX typedY wf.1 wf.2.1
      (ambientExecutionV_from_boundary typedX wf.1 hx nx (fun child h => boundary child (Or.inl h)))
      (ambientExecutionV_from_boundary typedY wf.2.1 hy ny (fun child h => boundary child (Or.inr h)))
  | or_c typedX _d _u typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny, _ex, _signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
    exact ambientExecutionV_or_c_from_children typedX typedY wf.1 wf.2 mal nm
      (boundary _ (Or.inl rfl) _ _ typedX wf.1 hx nx)
      (ambientExecutionV_from_boundary typedY wf.2 hy ny (fun child h => boundary child (Or.inr h)))
  | or_i typedX typedY =>
    obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
    exact ambientExecution_or_i_V typedX typedY wf.1 wf.2
      (ambientExecutionV_from_boundary typedX wf.1 hx nx (fun child h => boundary child (Or.inl h)))
      (ambientExecutionV_from_boundary typedY wf.2 hy ny (fun child h => boundary child (Or.inr h)))
  | andor typedX _d _u typedY typedZ =>
    obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, _ex⟩ := andor_malleability_children mal nm
    exact ambientExecutionV_andor_from_children typedX typedY typedZ wf.1 wf.2.1 wf.2.2.1 mal nm
      (boundary _ (Or.inl rfl) _ _ typedX wf.1 hx nx)
      (ambientExecutionV_from_boundary typedY wf.2.1 hy ny (fun child h => boundary child (Or.inr (Or.inl h))))
      (ambientExecutionV_from_boundary typedZ wf.2.2.1 hz nz (fun child h => boundary child (Or.inr (Or.inr h))))
termination_by sizeOf fragment

theorem ambientSignedV_from_boundary {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (signed : malMods.s = true)
    (boundary : ∀ child, VBoundary fragment child → BExecutionPremiseIn sc child) : AmbientSignedVIn sc fragment :=
  signedV_of_malleability typed wf mal signed (ambientExecutionV_from_boundary typed wf mal nm boundary)

theorem vBoundary_smaller {fragment child : CoreFragment} (member : VBoundary fragment child) :
    sizeOf child < sizeOf fragment := by
  cases fragment <;> simp only [VBoundary] at member
  all_goals try contradiction
  case v X => subst child; simp
  case and_v X Y =>
    rcases member with h | h
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
  case or_c X Y =>
    rcases member with h | h
    · subst child; simp; omega
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
  case or_i X Y =>
    rcases member with h | h
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
  case andor X Y Z =>
    rcases member with h | h | h
    · subst child; simp; omega
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
    · exact Nat.lt_trans (vBoundary_smaller h) (by simp; omega)
termination_by sizeOf fragment

theorem ambientExecutionV_from_smaller_B {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {malMods : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, mods⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment malMods) (nm : malMods.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremiseIn sc child) : AmbientExecutionVIn sc fragment :=
  ambientExecutionV_from_boundary typed wf mal nm (fun child h => ihB child (vBoundary_smaller h))

theorem uniform_signedV_of_uniform_B
    (executeB : ∀ fragment, BExecutionPremiseIn sc fragment) :
    ∀ (fragment : CoreFragment) (mods : CorrectnessModifiers) (malMods : MalleabilityModifiers),
      HasType sc fragment ⟨.V, mods⟩ → fragment.WellFormed sc →
      HasMalleability sc fragment malMods → malMods.nonMalleable = true → malMods.s = true →
      AmbientSignedVIn sc fragment := by
  intro fragment mods malMods typed wf mal nm signed
  exact ambientSignedV_from_boundary typed wf mal nm signed (fun child _ => executeB child)

end LeanMiniscript.Extraction.TapscriptRecovery.SignedV
