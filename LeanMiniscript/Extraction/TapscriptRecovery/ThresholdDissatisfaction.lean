import LeanMiniscript.Extraction.TapscriptRecovery.SignedDissatisfaction

/-! Classify false threshold executions and decompose selectors and key fragments. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdDsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat WBoolean ThresholdAlt
  ThresholdRun ThresholdRows ThresholdUnit ThresholdCanonical AndorForced
  SignedDsat MultiADsat

theorem push_equal_comparison_inv {k : Nat} {acc top : StackElement}
    {tail rest alt outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx
      (.success (top :: rest) outAlt)) :
    outAlt = alt ∧ rest = tail ∧
      top = if acc = scriptNat k then trueElement else falseElement := by
  by_cases eq : scriptNum (k : Int) = acc
  · have canonical : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx
        (.success (trueElement :: tail) alt) :=
      Eval.pushNum _ _ _ _ _ _ _ (Eval.equal_true _ _ _ [] _ _ _ _ eq Eval.done)
    obtain ⟨stackEq, altEq⟩ := ExecResult.success.inj (Eval.result_unique run canonical)
    obtain ⟨rfl, rfl⟩ := List.cons.inj stackEq
    exact ⟨altEq, rfl, by simp [show acc = scriptNat k from eq.symm]⟩
  · have canonical : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx
        (.success (falseElement :: tail) alt) :=
      Eval.pushNum _ _ _ _ _ _ _ (Eval.equal_false _ _ _ [] _ _ _ _ eq Eval.done)
    obtain ⟨stackEq, altEq⟩ := ExecResult.success.inj (Eval.result_unique run canonical)
    obtain ⟨rfl, rfl⟩ := List.cons.inj stackEq
    exact ⟨altEq, rfl, by simp [show acc ≠ scriptNat k from Ne.symm eq]⟩

theorem threshold_run_comparison {k : Nat} {children : List CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    {input rest alt outAlt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.thresh k children)) input alt flags ctx (.success (top :: rest) outAlt)) :
    outAlt = alt ∧
    ∃ first remaining firstMods types args firstRest value final,
      children = first :: remaining ∧
      HasType sc first ⟨.B, firstMods⟩ ∧ firstMods.d = true ∧ firstMods.u = true ∧
      HasTypeList sc remaining types ∧ thresholdRestTypes types ∧
      input = args ++ firstRest ∧
      Eval (compile first) (args ++ firstRest) alt flags ctx (.success (value :: firstRest) alt) ∧
      TailRunTrace flags ctx alt remaining value firstRest final rest ∧
      top = if final = scriptNat k then trueElement else falseElement := by
  cases typed with
  | @thresh k first remaining firstMods types ft fd fu tt ts _positive _atMost =>
    have combined : Eval (compile first ++ (compileThreshTail remaining ++ [.pushNum k, .op .OP_EQUAL]))
        input alt flags ctx (.success (top :: rest) outAlt) := by
      simpa [compile, compileWithKeyHash, compileThreshWithKeyHash, compileThreshTail, List.append_assoc] using run
    obtain ⟨mid, midAlt, firstRun, tailRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow first) combined
    obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType ft wf.2.1.1 _ _ _ _ _ firstRun
    subst midAlt
    obtain ⟨args, firstRest, value, inputEq, outputEq, _⟩ := effect.b_inv
    obtain ⟨last, lastAlt, addsRun, equalRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compileThreshTail_balancedControlFlow remaining) tailRun
    rw [outputEq] at addsRun
    obtain ⟨altEq, final, finalRest, finalEq, trace⟩ := typed_thresh_tail_inv tt ts wf.2.1.2 addsRun
    subst lastAlt
    rw [finalEq] at equalRun
    obtain ⟨altEq, rfl, comparison⟩ := push_equal_comparison_inv equalRun
    refine ⟨altEq, first, remaining, firstMods, types, args, firstRest, value, final,
      rfl, ft, fd, fu, tt, ts, inputEq, ?_, trace, comparison⟩
    rw [inputEq, outputEq] at firstRun
    exact firstRun

theorem threshold_witness_comparison {k : Nat} {children : List CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    {own : Witness} {rest alt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.thresh k children)) (own.toInitialStack ++ rest) alt flags ctx
      (.success (top :: rest) alt)) :
    ∃ first remaining firstMods types firstArgs tailArgs value final,
      children = first :: remaining ∧
      HasType sc first ⟨.B, firstMods⟩ ∧ firstMods.d = true ∧ firstMods.u = true ∧
      HasTypeList sc remaining types ∧ thresholdRestTypes types ∧
      own = tailArgs.reverse ++ firstArgs.reverse ∧
      Eval (compile first) (firstArgs ++ (tailArgs ++ rest)) alt flags ctx
        (.success (value :: (tailArgs ++ rest)) alt) ∧
      TailRunTrace flags ctx alt remaining value (tailArgs ++ rest) final rest ∧
      top = if final = scriptNat k then trueElement else falseElement := by
  obtain ⟨_, first, remaining, firstMods, types, firstArgs, firstRest, value, final,
    eq, ft, fd, fu, tt, ts, inputEq, firstRun, trace, comparison⟩ := threshold_run_comparison typed wf run
  obtain ⟨tailArgs, rfl⟩ := trace.input_frame
  have witnessEq : own = tailArgs.reverse ++ firstArgs.reverse := by
    have runtimeEq : own.toInitialStack = firstArgs ++ tailArgs := by
      apply List.append_cancel_right
      simpa [List.append_assoc] using inputEq
    simpa [Witness.toInitialStack] using congrArg List.reverse runtimeEq
  exact ⟨first, remaining, firstMods, types, firstArgs, tailArgs, value, final,
    eq, ft, fd, fu, tt, ts, witnessEq, firstRun, trace, comparison⟩

theorem list_signed_static {children : List CoreFragment} {mods : List MalleabilityModifiers}
    (mal : HasMalleabilityList sc children mods)
    (nm : MalleabilityModifiers.allNonMalleable mods = true)
    (e : MalleabilityModifiers.allE mods = true)
    (s : MalleabilityModifiers.allS mods = true) :
    ∀ child ∈ children, ∃ mm, HasMalleability sc child mm ∧
      mm.nonMalleable = true ∧ mm.e = true ∧ mm.s = true := by
  cases mal with
  | nil => simp
  | cons head tail =>
    obtain ⟨hn, tn⟩ := Bool.and_eq_true_iff.mp nm
    obtain ⟨he, te⟩ := Bool.and_eq_true_iff.mp e
    obtain ⟨hs, ts⟩ := Bool.and_eq_true_iff.mp s
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head, hn, he, hs⟩
    · exact list_signed_static tail tn te ts child member
termination_by sizeOf children

theorem threshold_signed_children {k : Nat} {children : List CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability sc (.thresh k children) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) :
    ∀ child ∈ children, ∃ hm, HasMalleability sc child hm ∧
      hm.nonMalleable = true ∧ hm.e = true ∧ hm.s = true := by
  cases mal with
  | thresh childrenMal =>
    obtain ⟨allNm, allE, _count⟩ := (boolAnd3_eq_true _ _ _).mp nm
    exact list_signed_static childrenMal allNm allE e

theorem zero_row_rawUnsigned {pairs : List CandidatePair}
    (rows : ∀ pair ∈ pairs, RawUnsigned pair.dsat) :
    RawUnsigned (CandidatePair.selectExactly 0 pairs) := by
  induction pairs using List.snocInduction with
  | nil => exact ⟨_, rfl, rfl⟩
  | snoc pairs pair ih =>
    rw [CandidatePair.selectExactly_append, CandidatePair.extendCounts_getD_zero]
    exact unsigned_combine (ih (fun p h => rows p (by simp [h]))) (rows pair (by simp))

theorem positive_rows_signed {pairs : List CandidatePair}
    (rows : ∀ pair ∈ pairs, pair.sat.Signed) :
    ∀ n, 0 < n → (CandidatePair.selectExactly n pairs).Signed := by
  induction pairs using List.snocInduction with
  | nil =>
    intro n positive
    cases n with
    | zero => omega
    | succ n => simpa using CandidateResult.signed_impossible
  | snoc pairs pair ih =>
    intro n positive
    cases n with
    | zero => omega
    | succ n =>
      rw [CandidatePair.selectExactly_append, CandidatePair.extendCounts_getD_succ]
      exact CandidateResult.Signed.select
        ((ih (fun p h => rows p (by simp [h])) (n + 1) (by omega)).combine_left)
        ((rows pair (by simp)).combine_right)

theorem signed_list_of_getD {rows : List CandidateResult}
    (all : ∀ n, (rows.getD n .impossible).Signed) : ∀ row ∈ rows, row.Signed := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact all 0
    · exact ih (fun n => all (n + 1)) r member

theorem threshold_fold_zero (k : Nat) (entries : List (CandidateResult × Nat))
    (canonical : CandidateResult) (raw : RawUnsigned canonical)
    (signed : ∀ entry ∈ entries, entry.1.Signed) :
    entries.foldl
      (fun selected entry => if entry.2 = k then selected else selected.select entry.1.markOvercomplete)
      canonical = canonical := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    have selectEq : canonical.select entry.1.markOvercomplete = canonical :=
      rawUnsigned_select_signed_eq raw (signed entry (by simp)).markOvercomplete
    by_cases skip : entry.2 = k
    · simpa [skip] using ih (fun ent h => signed ent (by simp [h]))
    · simpa [skip, selectEq] using ih (fun ent h => signed ent (by simp [h]))

theorem threshold_zero_selector {pairs : List CandidatePair} (k : Nat)
    (raw : RawUnsigned (CandidatePair.selectExactly 0 pairs))
    (signed : ∀ n, 0 < n → (CandidatePair.selectExactly n pairs).Signed) :
    CandidatePair.thresholdDissatisfaction k (CandidatePair.countCandidates pairs) =
      CandidatePair.selectExactly 0 pairs := by
  cases statesEq : CandidatePair.countCandidates pairs with
  | nil => simp [CandidatePair.thresholdDissatisfaction, CandidatePair.selectExactly, statesEq]
  | cons canonical positive =>
    have rawHead : RawUnsigned canonical := by simpa [CandidatePair.selectExactly, statesEq] using raw
    have tailSigned : ∀ row ∈ positive, row.Signed := signed_list_of_getD (fun n => by
      simpa [CandidatePair.selectExactly, statesEq] using signed (n + 1) (by omega))
    simp only [CandidatePair.thresholdDissatisfaction]
    have result := threshold_fold_zero k (positive.zipIdx 1) canonical rawHead
      (fun entry member => tailSigned entry.1 (List.fst_mem_of_mem_zipIdx member))
    simpa [CandidatePair.selectExactly, statesEq] using result

theorem threshold_dsat_zero_selector {k : Nat} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) (env : SatEnv) :
    (satisfactionCandidates (.thresh k children) env).dsat =
      CandidatePair.selectExactly 0 (satisfactionCandidatesList children env) := by
  have raw : ∀ pair ∈ satisfactionCandidatesList children env, RawUnsigned pair.dsat := by
    intro pair member
    rw [satisfactionCandidatesList_eq_map] at member
    obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp member
    exact threshold_children_dsat_unsigned typed wf mal nm env child childMem
  have signed : ∀ pair ∈ satisfactionCandidatesList children env, pair.sat.Signed := by
    intro pair member
    rw [satisfactionCandidatesList_eq_map] at member
    obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp member
    obtain ⟨ty, _oldMm, ct, cw, _oldMal, _oldNm, _oldE⟩ := threshold_children_static typed wf mal nm child childMem
    obtain ⟨hm, ch, _cn, _ce, cs⟩ := threshold_signed_children mal nm e child childMem
    exact (malleabilityCandidateSound env cw ct ch).signedSat cs
  simpa [satisfactionCandidates, threshold_candidate_guard wf] using
    threshold_zero_selector k (zero_row_rawUnsigned raw) (positive_rows_signed signed)

theorem signed_B_run_false {child parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc child ⟨.B, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (s : mm.s = true)
    (context : ExecutionContextIn sc parent child env flags pa po own)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (free : ¬ CheckedSignature child env flags own) :
    castToBool top = false := by
  cases truth : castToBool top with
  | false => rfl
  | true => exact (free (signed_consumption_of_malleability wf typed mal s
      (uniform_B_execution child cm mm typed wf mal nm parent env flags pa po own top rest
        context bounded run truth))).elim

theorem signed_W_run_false {child parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {saved top : StackElement} {rest : Stack} {order : BaseWOutputOrder}
    (typed : HasType sc child ⟨.W, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (s : mm.s = true)
    (context : ExecutionContextIn sc parent child env flags pa po own)
    (bounded : ∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) [])) (free : ¬ CheckedSignature child env flags own) :
    castToBool top = false := by
  cases truth : castToBool top with
  | false => rfl
  | true => exact (free (signed_consumption_of_malleability wf typed mal s
      (ambientExecutionW_step typed wf mal nm (fun sub _ => uniform_B_execution sub)
        parent env flags pa po own saved top rest order context bounded run truth))).elim

theorem signed_B_run_dsat {child parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc child ⟨.B, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (s : mm.s = true)
    (complete : AmbientDsatCompleteIn sc child)
    (context : ExecutionContextIn sc parent child env flags pa po own) (nodup : child.keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (free : ¬ CheckedSignature child env flags own) :
    castToBool top = false ∧ dissatisfy child env = some own := by
  have falsehood := signed_B_run_false typed wf mal nm s context bounded run free
  exact ⟨falsehood, complete parent env flags pa po own top rest context nodup bounded run falsehood free⟩

theorem signed_W_run_dsat {child parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {saved top : StackElement} {rest : Stack} {order : BaseWOutputOrder}
    (typed : HasType sc child ⟨.W, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (s : mm.s = true)
    (complete : AmbientDsatCompleteWIn sc child)
    (context : ExecutionContextIn sc parent child env flags pa po own) (nodup : child.keys.Nodup)
    (bounded : ∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) [])) (free : ¬ CheckedSignature child env flags own) :
    castToBool top = false ∧ dissatisfy child env = some own := by
  have falsehood := signed_W_run_false typed wf mal nm s context bounded run free
  exact ⟨falsehood, complete parent env flags pa po own saved top rest order
    context nodup bounded run falsehood free⟩

theorem tail_zero_projection {env : SatEnv} {flags : ScriptFlags} {root parent : CoreFragment}
    {pa po : Witness} {children : List CoreFragment} {acc final : StackElement}
    {input rest : Stack}
    (trace : TailRunTrace flags env.txCtx [] children acc input final rest)
    (statics : ∀ child ∈ children, ∃ cm mm, HasType sc child ⟨.W, cm⟩ ∧
      child.WellFormed sc ∧ HasMalleability sc child mm ∧
      mm.nonMalleable = true ∧ mm.s = true)
    (complete : ∀ child ∈ children, AmbientDsatCompleteWIn sc child)
    (keys : ∀ child ∈ children, ∀ key ∈ child.keys, key ∈ root.keys)
    (locks : ∀ child ∈ children, ∀ lock ∈ child.hashLocks, lock ∈ root.hashLocks)
    (nodup : ∀ child ∈ children, child.keys.Nodup)
    (remaining previous : Witness) (prior : List CandidatePair)
    (frame : input = remaining.toInitialStack ++ rest)
    (context : ExecutionContextIn sc parent root env flags pa po (remaining ++ previous))
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (free : ¬ CheckedSignature root env flags (remaining ++ previous))
    (selected : (CandidatePair.selectExactly 0 prior).usableWitness? = some previous) :
    (CandidatePair.selectExactly 0 (prior ++ satisfactionCandidatesList children env)).usableWitness? =
      some (remaining ++ previous) := by
  cases trace with
  | nil =>
    have empty : remaining = [] := by
      have eq : remaining.toInitialStack = [] := by simpa using frame.symm
      simpa [Witness.toInitialStack] using congrArg List.reverse eq
    subst remaining
    simpa [satisfactionCandidatesList] using selected
  | @cons child children acc result final tail rest args order a b run da db next =>
    obtain ⟨tailArgs, tailEq⟩ := next.input_frame
    have ownEq : remaining = tailArgs.reverse ++ args.reverse := by
      have eq : remaining.toInitialStack = args ++ tailArgs := by
        apply List.append_cancel_right
        simpa [tailEq, List.append_assoc] using frame.symm
      simpa [Witness.toInitialStack] using congrArg List.reverse eq
    have ownIn : ∀ item ∈ args.reverse, item ∈ remaining ++ previous := by
      intro item member
      rw [ownEq]
      exact List.mem_append_left _ (List.mem_append_right _ member)
    have childContext := executionContext_restrict context (active := child)
      (keys child (by simp)) (locks child (by simp)) ownIn
    have childBound : ∀ item ∈ acc :: (Witness.toInitialStack args.reverse ++ tail),
        item.size ≤ maxScriptElementSize := by
      simpa [Witness.toInitialStack] using
        (show ∀ item ∈ acc :: (args ++ tail), item.size ≤ maxScriptElementSize from
          fun item member => by
            rcases List.mem_cons.mp member with rfl | member
            · exact ThresholdRows.decoded_size da
            · exact bounded item member)
    have childRun : Eval (compile child) (acc :: (Witness.toInitialStack args.reverse ++ tail)) [] flags env.txCtx
        (.success (order.outputs acc result ++ tail) []) := by simpa [Witness.toInitialStack] using run
    have childFree : ¬ CheckedSignature child env flags args.reverse :=
      fun h => free (checkedSignature_mono (keys child (by simp)) ownIn h)
    obtain ⟨cm, mm, ct, cw, ch, cn, cs⟩ := statics child (by simp)
    obtain ⟨_actualFalse, childSelected⟩ := signed_W_run_dsat ct cw ch cn cs
      (complete child (by simp)) childContext (nodup child (by simp)) childBound childRun childFree
    have nextSelected : (CandidatePair.selectExactly 0 (prior ++ [satisfactionCandidates child env])).usableWitness? =
        some (args.reverse ++ previous) := by
      rw [CandidatePair.selectExactly_append, CandidatePair.extendCounts_getD_zero]
      exact CandidateResult.combine_usableWitness_iff.mpr ⟨previous, args.reverse, selected, childSelected, rfl⟩
    have nextContext : ExecutionContextIn sc parent root env flags pa po (tailArgs.reverse ++ (args.reverse ++ previous)) := by
      simpa [ownEq, List.append_assoc] using context
    have nextFrame : tail = Witness.toInitialStack tailArgs.reverse ++ rest := by
      simpa [Witness.toInitialStack] using tailEq
    have nextBounded : ∀ item ∈ tail, item.size ≤ maxScriptElementSize :=
      fun item member => bounded item (List.mem_append_right _ member)
    have nextFree : ¬ CheckedSignature root env flags (tailArgs.reverse ++ (args.reverse ++ previous)) := by
      simpa [ownEq, List.append_assoc] using free
    have answer := tail_zero_projection next
      (fun c h => statics c (by simp [h])) (fun c h => complete c (by simp [h]))
      (fun c h => keys c (by simp [h])) (fun c h => locks c (by simp [h]))
      (fun c h => nodup c (by simp [h])) tailArgs.reverse (args.reverse ++ previous)
      (prior ++ [satisfactionCandidates child env]) nextFrame nextContext nextBounded nextFree nextSelected
    simpa [satisfactionCandidatesList, ownEq, List.append_assoc] using answer
termination_by sizeOf children

theorem threshold_actual_zero_row {k : Nat} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true)
    (completeB : ∀ child ∈ children, ∀ cx, HasType sc child ⟨.B, cx⟩ →
      cx.d = true → AmbientDsatCompleteIn sc child)
    (completeW : ∀ child ∈ children, ∀ cx, HasType sc child ⟨.W, cx⟩ →
      cx.d = true → AmbientDsatCompleteWIn sc child)
    {parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (context : ExecutionContextIn sc parent (.thresh k children) env flags pa po own)
    (nodup : (CoreFragment.thresh k children).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.thresh k children)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (free : ¬ CheckedSignature (.thresh k children) env flags own) :
    (CandidatePair.selectExactly 0 (satisfactionCandidatesList children env)).usableWitness? = some own := by
  obtain ⟨first, remaining, firstMods, types, firstArgs, tailArgs, value, final,
    childrenEq, ft, fd, _fu, tt, ts, ownEq, firstRun, trace, _comparison⟩ := threshold_witness_comparison typed wf run
  subst children
  subst own
  have member : first ∈ first :: remaining := by simp
  have keysFirst : ∀ key ∈ first.keys, key ∈ (CoreFragment.thresh k (first :: remaining)).keys :=
    threshold_keys_member member
  have locksFirst : ∀ lock ∈ first.hashLocks, lock ∈ (CoreFragment.thresh k (first :: remaining)).hashLocks :=
    threshold_locks_member member
  have inFirst : ∀ item ∈ firstArgs.reverse, item ∈ tailArgs.reverse ++ firstArgs.reverse :=
    fun _ h => List.mem_append_right _ h
  have firstContext := executionContext_restrict context keysFirst locksFirst inFirst
  have firstBound : ∀ item ∈ firstArgs ++ (tailArgs ++ rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.append_assoc] using bounded
  have firstFree : ¬ CheckedSignature first env flags firstArgs.reverse :=
    fun checked => free (checkedSignature_mono keysFirst inFirst checked)
  obtain ⟨_ty, _old, _ct, fw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm first member
  obtain ⟨fm, fh, fn, _fe, fs⟩ := threshold_signed_children mal nm e first member
  have firstRun' : Eval (compile first) (Witness.toInitialStack firstArgs.reverse ++ (tailArgs ++ rest)) [] flags env.txCtx
      (.success (value :: (tailArgs ++ rest)) []) := by simpa [Witness.toInitialStack] using firstRun
  obtain ⟨_firstFalse, firstSelected⟩ := signed_B_run_dsat ft fw fh fn fs
    (completeB first member firstMods ft fd) firstContext (child_keys_nodup nodup member)
    (by simpa [Witness.toInitialStack] using firstBound) firstRun' firstFree
  have tailStatics : ∀ child ∈ remaining, ∃ cx mx, HasType sc child ⟨.W, cx⟩ ∧
      child.WellFormed sc ∧ HasMalleability sc child mx ∧
      mx.nonMalleable = true ∧ mx.s = true := by
    intro child childMem
    obtain ⟨cx, ct, _cd, _cu⟩ := threshold_rest_member_type tt ts child childMem
    have memAll : child ∈ first :: remaining := List.mem_cons_of_mem _ childMem
    obtain ⟨_ty, _old, _ct, cw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm child memAll
    obtain ⟨mx, ch, cn, _ce, cs⟩ := threshold_signed_children mal nm e child memAll
    exact ⟨cx, mx, ct, cw, ch, cn, cs⟩
  have tailComplete : ∀ child ∈ remaining, AmbientDsatCompleteWIn sc child := by
    intro child childMem
    obtain ⟨cx, ct, cd, _cu⟩ := threshold_rest_member_type tt ts child childMem
    exact completeW child (List.mem_cons_of_mem _ childMem) cx ct cd
  have initial : (CandidatePair.selectExactly 0 [satisfactionCandidates first env]).usableWitness? =
      some firstArgs.reverse := by
    rw [CandidatePair.selectExactly_one_zero]
    exact firstSelected
  have result := tail_zero_projection (root := .thresh k (first :: remaining)) trace tailStatics tailComplete
    (fun child childMem => threshold_keys_member (List.mem_cons_of_mem first childMem))
    (fun child childMem => threshold_locks_member (List.mem_cons_of_mem first childMem))
    (fun child childMem => child_keys_nodup nodup (List.mem_cons_of_mem first childMem))
    tailArgs.reverse firstArgs.reverse [satisfactionCandidates first env]
    (by simp [Witness.toInitialStack]) context
    (fun item itemMem => firstBound item (List.mem_append_right _ itemMem)) free initial
  simpa [satisfactionCandidatesList] using result

theorem ambientDsatComplete_thresh_signed {k : Nat} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true)
    (completeB : ∀ child ∈ children, ∀ cx, HasType sc child ⟨.B, cx⟩ →
      cx.d = true → AmbientDsatCompleteIn sc child)
    (completeW : ∀ child ∈ children, ∀ cx, HasType sc child ⟨.W, cx⟩ →
      cx.d = true → AmbientDsatCompleteWIn sc child) : AmbientDsatCompleteIn sc (.thresh k children) := by
  intro parent env flags pa po own top rest context nodup bounded run _falsehood free
  change (satisfactionCandidates (.thresh k children) env).dsat.usableWitness? = some own
  rw [threshold_dsat_zero_selector typed wf mal nm e env]
  exact threshold_actual_zero_row typed wf mal nm e completeB completeW context nodup bounded run free

theorem signedDsatB_thresh_step {k : Nat} {children : List CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.thresh k children) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.thresh k children) := by
  intro cm mm typed wf mal nm _d e _s
  apply ambientDsatComplete_thresh_signed typed wf mal nm e
  · intro child member cx ct cd
    obtain ⟨_ty, _old, _ct, cw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm child member
    obtain ⟨mx, ch, cn, ce, cs⟩ := threshold_signed_children mal nm e child member
    exact ih child (threshold_child_smaller member) cx mx ct cw ch cn cd ce cs
  · intro child member cx ct cd
    obtain ⟨_ty, _old, _ct, cw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm child member
    obtain ⟨mx, ch, cn, ce, cs⟩ := threshold_signed_children mal nm e child member
    exact signedDsatW_step ct cw ch cn cd ce cs
      (fun sub smaller => ih sub (Nat.lt_trans smaller (threshold_child_smaller member)))

def RemainingSignedDsatAfterThreshold : CoreFragment → Prop
  | .or_i _ _ | .c (.or_i _ _) | .c (.andor _ _ _) => True
  | _ => False

theorem signedDsatB_constructor_step_after_threshold (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child)
    (residual : RemainingSignedDsatAfterThreshold fragment → SignedDsatBIn sc fragment) :
    SignedDsatBIn sc fragment := by
  apply signedDsatB_constructor_step_after_multi_a fragment ih unsigned
  intro remaining
  cases fragment <;> try { exact signedDsatB_thresh_step ih } <;> try { exact residual trivial }
  case c X => cases X <;> first | exact residual trivial | exact False.elim remaining
  all_goals exact False.elim remaining

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdDsat

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrIDsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat AndorForced SignedDsat
  ThresholdDsat

theorem expressive_implies_d {ctx : ScriptContext} {fragment : CoreFragment}
    {ty : MiniType} {mm : MalleabilityModifiers}
    (typed : HasType ctx fragment ty) (mal : HasMalleability ctx fragment mm)
    (e : mm.e = true) : ty.mods.d = true := by
  cases typed with
  | zero => rfl
  | one => cases mal; cases e
  | pk_k => rfl
  | pk_h => rfl
  | older => cases mal; cases e
  | after => cases mal; cases e
  | sha256 => cases mal; cases e
  | hash256 => cases mal; cases e
  | ripemd160 => cases mal; cases e
  | hash160 => cases mal; cases e
  | and_v _tx _ty _base => cases mal; cases e
  | and_b tx ty =>
    cases mal with
    | and_b hx hy =>
      obtain ⟨ex, ey, _sx, _sy⟩ := (boolAnd4_eq_true _ _ _ _).mp e
      exact Bool.and_eq_true_iff.mpr ⟨expressive_implies_d tx hx ex, expressive_implies_d ty hy ey⟩
  | or_b => rfl
  | or_c => cases mal; cases e
  | or_d _tx _dx _ux ty =>
    cases mal with
    | or_d _hx hy =>
      have child := expressive_implies_d ty hy e
      exact child
  | or_i tx ty _base _same =>
    cases mal with
    | or_i hx hy =>
      apply Bool.or_eq_true_iff.mpr
      rcases Bool.or_eq_true_iff.mp e with left | right
      · exact Or.inl (expressive_implies_d tx hx (Bool.and_eq_true_iff.mp left).1)
      · exact Or.inr (expressive_implies_d ty hy (Bool.and_eq_true_iff.mp right).1)
  | andor _tx _dx _ux _ty tz _base _same =>
    cases mal with
    | andor _hx _hy hz =>
      have child := expressive_implies_d tz hz (Bool.and_eq_true_iff.mp e).1
      exact child
  | c_wrap tx =>
    cases mal with
    | c hx =>
      have child := expressive_implies_d tx hx e
      exact child
  | v_wrap => cases mal; cases e
  | a_wrap tx =>
    cases mal with
    | a hx =>
      have child := expressive_implies_d tx hx e
      exact child
  | s_wrap tx _one =>
    cases mal with
    | s hx =>
      have child := expressive_implies_d tx hx e
      exact child
  | d_wrap => rfl
  | j_wrap => rfl
  | n_wrap tx =>
    cases mal with
    | n hx =>
      have child := expressive_implies_d tx hx e
      exact child
  | thresh => rfl
  | multi => rfl
  | multi_a => rfl
termination_by sizeOf fragment

theorem signedDsatB_apply_expressive {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (complete : SignedDsatBIn sc fragment)
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (e : mm.e = true) (s : mm.s = true) : AmbientDsatCompleteIn sc fragment :=
  complete cm mm typed wf mal nm (expressive_implies_d typed mal e) e s

theorem or_i_signed_expressive_static {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_i X Y) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) (s : mm.s = true) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ HasType sc Y ⟨.B, cy⟩ ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.s = true ∧ my.s = true ∧
      ((cx.d = true ∧ mx.e = true ∧ my.f = true) ∨
        (cy.d = true ∧ my.e = true ∧ mx.f = true)) := by
  obtain ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, _childrenD, sx, sy, choice⟩ :=
    or_i_residual_static typed mal nm (expressive_implies_d typed mal e) e s
  refine ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, sx, sy, ?_⟩
  rcases choice with ⟨ex, fy⟩ | ⟨ey, fx⟩
  · exact Or.inl ⟨expressive_implies_d tx hx ex, ex, fy⟩
  · exact Or.inr ⟨expressive_implies_d ty hy ey, ey, fx⟩

theorem selector_usable_eq_iff {result : CandidateResult} {selector : StackElement} {own : Witness} :
    (result.withSelector selector).usableWitness? = some (own ++ [selector]) ↔
      result.usableWitness? = some own := by
  rw [CandidateResult.withSelector_usableWitness_iff]
  constructor
  · rintro ⟨inner, selected, eq⟩
    have ownEq : own = inner := List.append_cancel_right eq
    subst inner
    exact selected
  · intro selected
    exact ⟨own, selected, rfl⟩

theorem or_i_left_usable_projection {X Y : CoreFragment} {env : SatEnv} {own : Witness}
    (raw : RawUnsigned (satisfactionCandidates X env).dsat)
    (forced : (satisfactionCandidates Y env).dsat.Signed) :
    dissatisfy (.or_i X Y) env = some (own ++ [trueElement]) ↔ dissatisfy X env = some own := by
  change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = _ ↔ _
  rw [dsat_or_i_left_eq raw forced]
  exact selector_usable_eq_iff

theorem or_i_right_usable_projection {X Y : CoreFragment} {env : SatEnv} {own : Witness}
    (forced : (satisfactionCandidates X env).dsat.Signed)
    (raw : RawUnsigned (satisfactionCandidates Y env).dsat) :
    dissatisfy (.or_i X Y) env = some (own ++ [falseElement]) ↔ dissatisfy Y env = some own := by
  change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = _ ↔ _
  rw [dsat_or_i_right_eq forced raw]
  exact selector_usable_eq_iff

theorem signedDsatB_or_i_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.or_i X Y) := by
  intro cm mm typed wf mal nm _d e s
  obtain ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, sx, sy, choice⟩ :=
    or_i_signed_expressive_static typed mal nm e s
  rcases choice with ⟨dx, ex, fy⟩ | ⟨dy, ey, fx⟩
  · exact signedDsat_or_i_left tx ty wf.1 wf.2 hx hy nx ny dx ex sx sy fy ih
  · exact signedDsat_or_i_right tx ty wf.1 wf.2 hx hy nx ny dy ey sy sx fx ih

def RemainingSignedDsatAfterOrI : CoreFragment → Prop
  | .c (.or_i _ _) | .c (.andor _ _ _) => True
  | _ => False

theorem signedDsatB_constructor_step_after_or_i (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child)
    (residual : RemainingSignedDsatAfterOrI fragment → SignedDsatBIn sc fragment) : SignedDsatBIn sc fragment := by
  apply signedDsatB_constructor_step_after_threshold fragment ih unsigned
  intro remaining
  cases fragment <;> try { exact signedDsatB_or_i_step ih } <;> try { exact residual trivial }
  case c X => cases X <;> first | exact residual trivial | exact False.elim remaining
  all_goals exact False.elim remaining

end LeanMiniscript.Extraction.TapscriptRecovery.OrIDsat

namespace LeanMiniscript.Extraction.TapscriptRecovery.CompoundKDsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat BExecution CompoundK
  ThresholdUnit AndorForced OrDFalseFamily ForcedK SignedDsat OrIDsat

def PendingDsatKIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (sig keyBytes : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags pa po ([sig] ++ own) →
    fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ (sig :: rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
      (.success (keyBytes :: sig :: rest) []) →
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig keyBytes = .ok false →
    ¬ CheckedSignature fragment env flags ([sig] ++ own) →
    dissatisfy fragment env = some ([sig] ++ own)

abbrev PendingDsatK := PendingDsatKIn .tapscript

theorem pending_of_c_complete {X : CoreFragment}
    (complete : AmbientDsatCompleteIn sc (.c X)) : PendingDsatKIn sc X := by
  intro parent env flags pa po own sig keyBytes rest context nodup bounded run checked free
  have cRun : Eval (compile (.c X)) (Witness.toInitialStack ([sig] ++ own) ++ rest) [] flags env.txCtx
      (.success (falseElement :: rest) []) := by
    simpa [compile, compileWithKeyHash, Witness.toInitialStack, List.reverse_append, List.append_assoc] using
      Eval.append run (Eval.checksigFalse checked (Eval.done (stack := falseElement :: rest)))
  have cContext : ExecutionContextIn sc parent (.c X) env flags pa po ([sig] ++ own) :=
    executionContext_restrict context (fun _ h => h) (fun _ h => h) (fun _ h => h)
  have result := complete parent env flags pa po ([sig] ++ own) falseElement rest cContext
    nodup (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded)
    cRun (by simp [castToBool, falseElement]) free
  simpa only [dissatisfy_c] using result

theorem c_false_key_frame {X parent : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType sc X ⟨.K, cm⟩) (wf : X.WellFormed sc)
    (context : ExecutionContextIn sc parent (.c X) env flags pa po own)
    (run : Eval (compile (.c X)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    ∃ (part : Witness) (sig : StackElement) (key : PubKey),
      key ∈ X.keys ∧ own = [sig] ++ part ∧ sig = falseElement ∧
      Eval (compile X) (part.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
        (.success (key.bytes :: sig :: rest) []) ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok false := by
  obtain ⟨part, sig, keyBytes, eq, childRun, checked⟩ := c_false_run_frame typed wf run falsehood
  subst own
  have childContext : ExecutionContextIn sc parent X env flags pa po part :=
    executionContext_restrict context (fun _ h => h) (fun _ h => h)
      (fun _ h => List.mem_append_right _ h)
  obtain ⟨key, member, output⟩ := keyOutput_of_typed typed wf
    parent env flags pa po part keyBytes (sig :: rest) childContext childRun
  subst keyBytes
  exact ⟨part, sig, key, member, rfl,
    Active.false_signature_empty context.rules checked,
    childRun, checked⟩

theorem c_complete_of_pending {X : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc X ⟨.K, cm⟩) (wf : X.WellFormed sc)
    (complete : PendingDsatKIn sc X) : AmbientDsatCompleteIn sc (.c X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  obtain ⟨part, sig, key, _member, eq, _empty, childRun, checked⟩ :=
    c_false_key_frame typed wf context run falsehood
  subst own
  have childContext : ExecutionContextIn sc parent X env flags pa po ([sig] ++ part) :=
    executionContext_restrict context (fun _ h => h) (fun _ h => h) (fun _ h => h)
  rw [dissatisfy_c]
  exact complete parent env flags pa po part sig key.bytes rest childContext nodup
    (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded) childRun checked free

theorem pending_of_signedDsatB {X : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc X ⟨.K, cm⟩)
    (wf : X.WellFormed sc) (mal : HasMalleability sc X mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true)
    (complete : SignedDsatBIn sc (.c X)) : PendingDsatKIn sc X := by
  apply pending_of_c_complete
  exact signedDsatB_apply_expressive complete (.c_wrap typed) wf (.c mal) nm e rfl

theorem pending_or_i_left {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.K, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (rawX : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat)
    (signedY : ∀ env, (satisfactionCandidates Y env).dsat.Signed)
    (completeX : PendingDsatKIn sc X) (forcedY : AmbientForcedKIn sc Y) : PendingDsatKIn sc (.or_i X Y) := by
  intro parent env flags pa po own sig keyBytes rest context nodup bounded run checked free
  rcases or_i_run_K tx ty wx wy context.rules run with
    ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ [sig] ++ active, item ∈ [sig] ++ (active ++ [trueElement]) := by
      intro item member
      rcases List.mem_append.mp member with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    have canonical := completeX parent env flags pa po active sig keyBytes rest
      (executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inside)
      (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) childRun checked
      (fun evidence => free (checkedSignature_mono keysX inside evidence))
    simpa only [List.append_assoc] using
      (or_i_left_usable_projection (rawX env) (signedY env)).mpr canonical
  · subst own
    have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ active, item ∈ [sig] ++ (active ++ [falseElement]) :=
      fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
    exact (free (checkedSignature_mono keysY inside
      (forcedY parent env flags pa po active keyBytes (sig :: rest)
        (executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inside)
        (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) childRun))).elim

theorem pending_or_i_right {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.K, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (rawY : ∀ env, RawUnsigned (satisfactionCandidates Y env).dsat)
    (signedX : ∀ env, (satisfactionCandidates X env).dsat.Signed)
    (completeY : PendingDsatKIn sc Y) (forcedX : AmbientForcedKIn sc X) : PendingDsatKIn sc (.or_i X Y) := by
  intro parent env flags pa po own sig keyBytes rest context nodup bounded run checked free
  rcases or_i_run_K tx ty wx wy context.rules run with
    ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ active, item ∈ [sig] ++ (active ++ [trueElement]) :=
      fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
    exact (free (checkedSignature_mono keysX inside
      (forcedX parent env flags pa po active keyBytes (sig :: rest)
        (executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inside)
        (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) childRun))).elim
  · subst own
    have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ [sig] ++ active, item ∈ [sig] ++ (active ++ [falseElement]) := by
      intro item member
      rcases List.mem_append.mp member with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    have canonical := completeY parent env flags pa po active sig keyBytes rest
      (executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inside)
      (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) childRun checked
      (fun evidence => free (checkedSignature_mono keysY inside evidence))
    simpa only [List.append_assoc] using
      (or_i_right_usable_projection (signedX env) (rawY env)).mpr canonical

theorem signedDsatB_c_or_i_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.c (.or_i X Y)) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.c (.or_i X Y)) := by
  intro cm mm typed wf mal nm _d e _s
  cases typed with
  | c_wrap typedK =>
    cases typed_K_shape typedK with
    | or_i tx ty =>
      cases mal with
      | c malK =>
        obtain ⟨mx, my, hx, hy, nx, ny, choice⟩ := or_i_expressive_children malK nm e
        apply c_complete_of_pending typedK wf
        rcases choice with ⟨ex, fy⟩ | ⟨ey, fx⟩
        · exact pending_or_i_left tx ty wf.1 wf.2
            (expressive_rawUnsigned wf.1 tx hx nx ex)
            (fun env => (malleabilityCandidateSound env wf.2 ty hy).forcedDsat fy)
            (pending_of_signedDsatB tx wf.1 hx nx ex (ih (.c X) (by simp; omega)))
            (uniform_forcedK Y _ _ ty wf.2 hy ny fy)
        · exact pending_or_i_right tx ty wf.1 wf.2
            (expressive_rawUnsigned wf.2 ty hy ny ey)
            (fun env => (malleabilityCandidateSound env wf.1 tx hx).forcedDsat fx)
            (pending_of_signedDsatB ty wf.2 hy ny ey (ih (.c Y) (by simp; omega)))
            (uniform_forcedK X _ _ tx wf.1 hx nx fx)

theorem andor_K_dsat_selector {X Y Z : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.K, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  cases typed_K_shape typed with
  | andor tx _dx _ux ty tz =>
    cases mal with
    | andor hx hy hz =>
      obtain ⟨nx, _ny, nz, ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      obtain ⟨ez, choice⟩ := Bool.and_eq_true_iff.mp e
      apply rawUnsigned_select_signed_eq
        (unsigned_combine (expressive_rawUnsigned wf.1 tx hx nx ex env)
          (expressive_rawUnsigned wf.2.2.1 tz hz nz ez env))
      rcases Bool.or_eq_true_iff.mp choice with sx | fy
      · exact ((malleabilityCandidateSound env wf.1 tx hx).signedSat sx).combine_left.markNonCanonical
      · exact ((malleabilityCandidateSound env wf.2.1 ty hy).forcedDsat fy).combine_right.markNonCanonical

theorem pending_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (tz : HasType sc Z ⟨.K, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (route : mx.s = true ∨ AmbientForcedKIn sc Y)
    (selector : ∀ env, (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat)
    (completeX : AmbientDsatCompleteIn sc X) (completeZ : PendingDsatKIn sc Z) :
    PendingDsatKIn sc (.andor X Y Z) := by
  intro parent env flags pa po own sig keyBytes rest context nodup bounded run checked free
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  have nodupX : X.keys.Nodup := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).1
  have nodupY : Y.keys.Nodup := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).2.1
  have nodupZ : Z.keys.Nodup := (List.pairwise_append.mp nodup).2.1
  rcases andor_run_K_frame tx ty tz wx wy wz run with
    ⟨left, right, value, eq, runX, falseX, runZ⟩ | ⟨left, right, value, eq, runX, trueX, runY⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ [sig] ++ (right ++ left) :=
      fun _ h => List.mem_append_right _ (List.mem_append_right _ h)
    have inZ : ∀ item ∈ [sig] ++ right, item ∈ [sig] ++ (right ++ left) := by
      intro item member
      rcases List.mem_append.mp member with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ (sig :: rest)),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have dx := completeX parent env flags pa po left value (right.toInitialStack ++ (sig :: rest))
      (executionContext_restrict context keysX
        (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX)
      nodupX bounds runX falseX (fun evidence => free (checkedSignature_mono keysX inX evidence))
    have dz := completeZ parent env flags pa po right sig keyBytes rest
      (executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ)
      nodupZ (fun item h => bounds item (List.mem_append_right _ h)) runZ checked
      (fun evidence => free (checkedSignature_mono keysZ inZ evidence))
    simpa only [List.append_assoc] using andor_dsat_projection (selector env) dx dz
  · subst own
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ (sig :: rest)),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases route with sx | forcedY
    · have inX : ∀ item ∈ left, item ∈ [sig] ++ (right ++ left) :=
        fun _ h => List.mem_append_right _ (List.mem_append_right _ h)
      have contextX := executionContext_restrict context keysX
        (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
      have evidence := signed_consumption_of_malleability wx tx hx sx
        (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left value
          (right.toInitialStack ++ (sig :: rest)) contextX bounds runX trueX)
      exact (free (checkedSignature_mono keysX inX evidence)).elim
    · have inY : ∀ item ∈ right, item ∈ [sig] ++ (right ++ left) :=
        fun _ h => List.mem_append_right _ (List.mem_append_left _ h)
      have evidence := forcedY parent env flags pa po right keyBytes (sig :: rest)
        (executionContext_restrict context keysY
          (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY)
        nodupY (fun item h => bounds item (List.mem_append_right _ h)) runY
      exact (free (checkedSignature_mono keysY inY evidence)).elim

theorem signedDsatB_c_andor_step {X Y Z : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.c (.andor X Y Z)) → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf (CoreFragment.c (.andor X Y Z)) → UnsignedFalseIn sc child) :
    SignedDsatBIn sc (.c (.andor X Y Z)) := by
  intro cm mm typed wf mal nm _d e _s
  cases typed with
  | c_wrap typedK =>
    cases typed_K_shape typedK with
    | andor tx dx ux ty tz =>
      cases mal with
      | c malK =>
        have selector := andor_K_dsat_selector typedK wf malK nm e
        cases malK with
        | @andor _ _ _ mx my mz hx hy hz =>
          obtain ⟨nx, ny, nz, ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
          obtain ⟨ez, choice⟩ := Bool.and_eq_true_iff.mp e
          have completeZ := pending_of_signedDsatB tz wf.2.2.1 hz nz ez
            (ih (.c Z) (by simp; omega))
          apply c_complete_of_pending typedK wf
          cases sx : mx.s with
          | true =>
            exact pending_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx (Or.inl sx) selector
              (ih X (by simp; omega) _ _ tx wf.1 hx nx dx ex sx) completeZ
          | false =>
            have fy : my.f = true := by simpa [sx] using choice
            exact pending_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx
              (Or.inr (uniform_forcedK Y _ _ ty wf.2.1 hy ny fy)) selector
              (unsigned X (by simp; omega) _ _ tx wf.1 hx nx dx ux ex sx) completeZ

theorem signedDsatB_constructor_step_from_unsigned (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child) : SignedDsatBIn sc fragment := by
  apply signedDsatB_constructor_step_after_or_i fragment ih unsigned
  intro remaining
  cases fragment <;> try { exact False.elim remaining }
  case c X =>
    cases X <;> try { exact False.elim remaining }
    case or_i X Y => exact signedDsatB_c_or_i_step ih
    case andor X Y Z => exact signedDsatB_c_andor_step ih unsigned

end LeanMiniscript.Extraction.TapscriptRecovery.CompoundKDsat
