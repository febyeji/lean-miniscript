import LeanMiniscript.Extraction.TapscriptRecovery.UnsignedBranches

/-! Reconstruct unsigned threshold satisfactions and classify unsigned false B executions. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThreshComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat WBoolean ThresholdAlt
  ThresholdRun ThresholdRows ThresholdUnit ThresholdCanonical DsatMaterial
  UnsignedSelection SignedExchange UnsignedComplete VRestComplete
  OrBComplete OrDComplete

theorem typed_W_du_children {fragment : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) :
    (∃ child cx, fragment = .a child ∧ HasType sc child ⟨.B, cx⟩ ∧ cm.d = cx.d ∧ cm.u = cx.u) ∨
    (∃ child cx, fragment = .s child ∧ HasType sc child ⟨.B, cx⟩ ∧ cx.o = true ∧ cm.d = cx.d ∧ cm.u = cx.u) := by
  generalize typeEq : (⟨.W, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case a_wrap tx => exact Or.inl ⟨_, _, rfl, tx, congrArg (fun ty : MiniType => ty.mods.d) typeEq, congrArg (fun ty : MiniType => ty.mods.u) typeEq⟩
  case s_wrap tx one => exact Or.inr ⟨_, _, rfl, tx, one, congrArg (fun ty : MiniType => ty.mods.d) typeEq, congrArg (fun ty : MiniType => ty.mods.u) typeEq⟩
  case and_v _tx _ty branch =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case or_i _tx _ty branch _same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim
  case andor _tx _d _u _ty _tz branch _same =>
    change BaseType.W = _ at baseEq
    have bad : branchBase .W := by rw [baseEq]; exact branch
    exact bad.elim

theorem conditionDsatW_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (u : cm.u = true) (e : mm.e = true)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub) : AmbientDsatCompleteWIn sc fragment := by
  rcases typed_W_du_children typed with ⟨child, cx, rfl, tx, deq, ueq⟩ | ⟨child, cx, rfl, tx, one, deq, ueq⟩
  · cases mal with
    | a hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm (deq.symm.trans d) (ueq.symm.trans u) e
      intro parent env flags pa po own saved top rest order context nodup bounded run falsehood free
      have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact complete parent env flags pa po own top rest
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood free
  · cases mal with
    | s hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm (deq.symm.trans d) (ueq.symm.trans u) e
      intro parent env flags pa po own saved top rest order context nodup bounded run falsehood free
      obtain ⟨_, childRun⟩ := s_run_child tx one wf run
      apply complete parent env flags pa po own top (saved :: rest)
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup _ childRun falsehood free
      intro item member
      apply bounded item
      simp only [List.mem_cons, List.mem_append] at member ⊢
      rcases member with member | rfl | member
      · exact Or.inr (Or.inl member)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr member)

def RowCompleteBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (top : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    ¬ CheckedSignature fragment env flags own →
    RawUnsigned (rowResult (satisfactionCandidates fragment env) (castToBool top)) ∧
    (rowResult (satisfactionCandidates fragment env) (castToBool top)).usableWitness? = some own

abbrev RowCompleteB := RowCompleteBIn .tapscript

def RowCompleteWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    ¬ CheckedSignature fragment env flags own →
    RawUnsigned (rowResult (satisfactionCandidates fragment env) (castToBool top)) ∧
    (rowResult (satisfactionCandidates fragment env) (castToBool top)).usableWitness? = some own

abbrev RowCompleteW := RowCompleteWIn .tapscript

theorem rowCompleteB {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sat : AmbientUnsignedSatCompleteBIn sc fragment) (dsat : AmbientDsatCompleteIn sc fragment) : RowCompleteBIn sc fragment := by
  intro parent env flags pa po own top rest context nodup bounded run free
  cases truth : castToBool top with
  | false => exact ⟨by simpa [rowResult, truth] using expressive_rawUnsigned wf typed mal nm e env,
      by simpa [rowResult, truth, dissatisfy] using dsat parent env flags pa po own top rest context nodup bounded run truth free⟩
  | true =>
    have raw := execution_without_checked_signature
      (uniform_B_execution fragment cm mm typed wf mal nm parent env flags pa po own top rest context bounded run truth) free
    exact ⟨by simpa [rowResult, truth] using raw,
      by simpa [rowResult, truth, satisfy] using sat parent env flags pa po own top rest context nodup bounded run truth free⟩

theorem rowCompleteW {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sat : AmbientUnsignedSatCompleteWIn sc fragment) (dsat : AmbientDsatCompleteWIn sc fragment) : RowCompleteWIn sc fragment := by
  intro parent env flags pa po own saved top rest order context nodup bounded run free
  cases truth : castToBool top with
  | false => exact ⟨by simpa [rowResult, truth] using expressive_rawUnsigned wf typed mal nm e env,
      by simpa [rowResult, truth, dissatisfy] using dsat parent env flags pa po own saved top rest order context nodup bounded run truth free⟩
  | true => exact ⟨by simpa [rowResult, truth] using unsigned_W_run typed wf mal nm context bounded run truth free,
      by simpa [rowResult, truth, satisfy] using sat parent env flags pa po own saved top rest order context nodup bounded run truth free⟩

theorem tail_usable_rows {env : SatEnv} {flags : ScriptFlags}
    {parent root : CoreFragment} {pa po : Witness}
    {children : List CoreFragment} {acc final : StackElement} {input rest : Stack}
    (trace : TailRunTrace flags env.txCtx [] children acc input final rest)
    (complete : ∀ child ∈ children, RowCompleteWIn sc child)
    (keys : ∀ child ∈ children, ∀ key ∈ child.keys, key ∈ root.keys)
    (locks : ∀ child ∈ children, ∀ lock ∈ child.hashLocks, lock ∈ root.hashLocks)
    (nodup : ∀ child ∈ children, child.keys.Nodup)
    (consumed : Witness) (frame : input = consumed.toInitialStack ++ rest)
    (context : ExecutionContextIn sc parent root env flags pa po consumed)
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (free : ¬ CheckedSignature root env flags consumed) :
    ∃ truths frames, TailTruths trace truths ∧
      UnsignedLayout (satisfactionCandidatesList children env) truths frames ∧ consumed = assemble frames := by
  induction trace generalizing consumed with
  | nil acc rest =>
    have empty : consumed = [] := by
      have eq : consumed.toInitialStack = [] := by simpa using frame.symm
      simpa [Witness.toInitialStack] using congrArg List.reverse eq
    exact ⟨[], [], .nil _ _, .nil, by simpa [assemble] using empty⟩
  | @cons child children acc result final tail rest args order a b run da db next ih =>
    obtain ⟨tailArgs, tailFrame⟩ := next.input_frame
    have consumedEq : consumed = tailArgs.reverse ++ args.reverse := by
      have eq : consumed.toInitialStack = args ++ tailArgs := by
        apply List.append_cancel_right
        simpa [tailFrame, List.append_assoc] using frame.symm
      simpa [Witness.toInitialStack] using congrArg List.reverse eq
    have ownIn : ∀ item ∈ args.reverse, item ∈ consumed := by
      intro item member; rw [consumedEq]; exact List.mem_append_right _ member
    have tailIn : ∀ item ∈ tailArgs.reverse, item ∈ consumed := by
      intro item member; rw [consumedEq]; exact List.mem_append_left _ member
    have childContext := executionContext_restrict context (active := child)
      (keys child (by simp)) (locks child (by simp)) ownIn
    have childFree : ¬ CheckedSignature child env flags args.reverse :=
      fun checked => free (checkedSignature_mono (keys child (by simp)) ownIn checked)
    obtain ⟨raw, usable⟩ := complete child (by simp) parent env flags pa po args.reverse acc result tail order
      childContext (nodup child (by simp))
      (by
        intro item member
        simp only [Witness.toInitialStack, List.reverse_reverse, List.mem_cons] at member
        rcases member with rfl | member
        · exact ThresholdRows.decoded_size da
        · exact bounded item member)
      (by simpa [Witness.toInitialStack] using run) childFree
    have nextContext := executionContext_restrict context (active := root)
      (fun _ h => h) (fun _ h => h) tailIn
    have nextFree : ¬ CheckedSignature root env flags tailArgs.reverse :=
      fun checked => free (checkedSignature_mono (fun _ h => h) tailIn checked)
    obtain ⟨truths, frames, observed, rows, eq⟩ := ih
      (fun c h => complete c (by simp [h]))
      (fun c h => keys c (by simp [h])) (fun c h => locks c (by simp [h]))
      (fun c h => nodup c (by simp [h])) tailArgs.reverse
      (by simpa [Witness.toInitialStack] using tailFrame) nextContext
      (fun item h => bounded item (List.mem_append_right _ h)) nextFree
    refine ⟨castToBool result :: truths, args.reverse :: frames,
      .cons (run := run) (da := da) (db := db) observed, .cons raw usable rows, ?_⟩
    simpa [assemble_cons, eq] using consumedEq

theorem threshold_actual_layout {k : Nat} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.thresh k children) → BSuccessCompleteIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf (CoreFragment.thresh k children) → BConditionFalseCompleteIn sc sub)
    {parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (context : ExecutionContextIn sc parent (.thresh k children) env flags pa po own)
    (nodup : (CoreFragment.thresh k children).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.thresh k children)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true)
    (free : ¬ CheckedSignature (.thresh k children) env flags own) :
    ∃ truths frames, UnsignedLayout (satisfactionCandidatesList children env) truths frames ∧
      (truths.map Bool.toNat).sum = k ∧ own = assemble frames := by
  obtain ⟨first, remaining, fm, types, firstArgs, tailArgs, value, eq, ft, fd, fu, tt, ts,
    consumedEq, firstRun, trace⟩ := threshold_witness_frame typed wf run truth
  subst children
  subst own
  have childStatic := threshold_children_static typed wf mal nm
  have firstBound : ∀ item ∈ firstArgs ++ (tailArgs ++ rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  have firstKeys : ∀ key ∈ first.keys, key ∈ (CoreFragment.thresh k (first :: remaining)).keys :=
    threshold_keys_member (by simp)
  have firstIn : ∀ item ∈ firstArgs.reverse, item ∈ tailArgs.reverse ++ firstArgs.reverse :=
    fun _ h => List.mem_append_right _ h
  have firstContext := executionContext_restrict context (active := first) firstKeys
    (threshold_locks_member (by simp)) firstIn
  have firstFree : ¬ CheckedSignature first env flags firstArgs.reverse :=
    fun checked => free (checkedSignature_mono firstKeys firstIn checked)
  obtain ⟨_ty, fmMal, _ft, fw, fh, fn, fe⟩ := childStatic first (by simp)
  have firstSmaller := threshold_child_smaller (k := k) (show first ∈ first :: remaining by simp)
  have firstComplete := rowCompleteB ft fw fh fn fe
    (ih first firstSmaller fm fmMal ft fw fh fn)
    (df first firstSmaller fm fmMal ft fw fh fn fd fu fe)
  obtain ⟨firstRaw, firstUsable⟩ := firstComplete parent env flags pa po firstArgs.reverse value
    (tailArgs ++ rest) firstContext (child_keys_nodup nodup (by simp))
    (by simpa [Witness.toInitialStack] using firstBound)
    (by simpa [Witness.toInitialStack] using firstRun) firstFree
  have tailComplete : ∀ child ∈ remaining, RowCompleteWIn sc child := by
    intro child member
    obtain ⟨wc, wt, wd, wu⟩ := threshold_rest_member_type tt ts child member
    obtain ⟨_ty, wm, _wt, ww, wh, wn, we⟩ := childStatic child (by simp [member])
    have smaller := threshold_child_smaller (k := k) (show child ∈ first :: remaining by simp [member])
    apply rowCompleteW wt ww wh wn we
    · apply unsignedSatCompleteW_from_smaller_B wt ww wh wn we
      intro sub bound cb mb tb wb hb nb _eb
      exact ih sub (Nat.lt_trans bound smaller) cb mb tb wb hb nb
    · exact conditionDsatW_from_smaller_B wt ww wh wn wd wu we
        (fun sub bound => df sub (Nat.lt_trans bound smaller))
  have tailIn : ∀ item ∈ tailArgs.reverse, item ∈ tailArgs.reverse ++ firstArgs.reverse :=
    fun _ h => List.mem_append_left _ h
  have tailContext := executionContext_restrict context
    (active := .thresh k (first :: remaining)) (fun _ h => h) (fun _ h => h) tailIn
  have tailFree : ¬ CheckedSignature (.thresh k (first :: remaining)) env flags tailArgs.reverse :=
    fun checked => free (checkedSignature_mono (fun _ h => h) tailIn checked)
  obtain ⟨truths, frames, observed, rows, tailEq⟩ := tail_usable_rows (root := .thresh k (first :: remaining)) trace tailComplete
    (fun child h => threshold_keys_member (show child ∈ first :: remaining by simp [h]))
    (fun child h => threshold_locks_member (show child ∈ first :: remaining by simp [h]))
    (fun child h => child_keys_nodup nodup (by simp [h])) tailArgs.reverse
    (by simp [Witness.toInitialStack]) tailContext
    (fun item h => firstBound item (List.mem_append_right _ h)) tailFree
  refine ⟨castToBool value :: truths, firstArgs.reverse :: frames,
    .cons firstRaw firstUsable rows, ?_, ?_⟩
  · exact threshold_trace_truth_count ft fu fw tt ts wf.2.1.2 context.version wf.2.2.2 firstBound firstRun observed
  · simp [assemble_cons, tailEq]

private theorem layout_choices {pairs bits frames} (rows : RowLayout pairs bits frames) :
    CandidatePair.ChoiceFrames pairs bits frames := by
  have go {pairs bits frames} (later : RowLayout pairs bits frames) :
      ∀ {prior bs ws}, CandidatePair.ChoiceFrames prior bs ws →
        CandidatePair.ChoiceFrames (prior ++ pairs) (bs ++ bits) (ws ++ frames) := by
    induction later with
    | nil => simp
    | @cons c cs b bs w ws sel _ ih =>
      intro prior bits frames layout
      cases b
      · simpa using ih (layout.snocDsat sel)
      · simpa using ih (layout.snocSat sel)
  exact go rows .nil

private theorem assemble_selected_frames {pairs bits frames} (rows : CandidatePair.ChoiceFrames pairs bits frames)
    (positions : List Nat) (matchBits : bits = TapscriptWitness.positionFlags positions pairs.length) :
    (CandidatePair.assembleThreshold positions pairs.length (bits.count true) pairs.reverse).usableWitness? =
      some (assemble frames) := by
  induction rows with
  | nil => rfl
  | @snocSat pairs bits frames child own prior sel ih =>
    simp only [List.length_append, List.length_singleton, TapscriptWitness.positionFlags, List.range_succ,
      List.map_append, List.map_singleton] at matchBits
    have mid : bits = TapscriptWitness.positionFlags positions pairs.length :=
      (List.append_inj' matchBits (by simp)).1
    have chosen : pairs.length ∈ positions := by simpa using (List.append_inj' matchBits (by simp)).2.symm
    simp only [List.length_append, List.length_singleton, List.count_append, List.count_singleton,
      beq_self_eq_true, List.reverse_append, List.reverse_singleton, List.singleton_append,
      CandidatePair.assembleThreshold, Nat.add_one_sub_one, chosen, if_true]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨_, _, ih mid, sel, assemble_snoc frames own⟩
  | @snocDsat pairs bits frames child own prior sel ih =>
    simp only [List.length_append, List.length_singleton, TapscriptWitness.positionFlags, List.range_succ,
      List.map_append, List.map_singleton] at matchBits
    have mid : bits = TapscriptWitness.positionFlags positions pairs.length :=
      (List.append_inj' matchBits (by simp)).1
    have skip : pairs.length ∉ positions := by simpa using (List.append_inj' matchBits (by simp)).2.symm
    simp only [List.length_append, List.length_singleton, List.count_append, List.count_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      CandidatePair.assembleThreshold, Nat.add_one_sub_one, skip, if_false]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨_, _, ih mid, sel, assemble_snoc frames own⟩

private theorem usable_all_unsigned {pairs bits frames} (rows : RowLayout pairs bits frames)
    (eqBits : bits = pairs.map CandidatePair.unsignedSat) :
    (CandidatePair.thresholdSatisfaction (bits.count true) pairs).usableWitness? = some (assemble frames) := by
  let selected := (pairs.zipIdx.filter (fun p => p.1.unsignedSat)).map Prod.snd
  have size : selected.length = bits.count true := by
    rw [eqBits]
    have h := congrArg (List.countP CandidatePair.unsignedSat) (List.zipIdx_map_fst 0 pairs)
    simp only [List.countP_map, Function.comp_def] at h
    simpa [selected, List.count, ← List.countP_eq_length_filter, Function.comp_def] using h
  have choice : CandidatePair.thresholdPositions (bits.count true) pairs = some selected := by
    simp [CandidatePair.thresholdPositions, ← size, selected]
  have matchBits : bits = TapscriptWitness.positionFlags selected pairs.length := by
    rw [eqBits]
    apply List.ext_getElem?; intro i
    by_cases bound : i < pairs.length
    · have inside : i ∈ selected ↔ pairs[i].unsignedSat = true := by
        constructor
        · intro hi
          obtain ⟨⟨row, n⟩, mem, rfl⟩ := List.mem_map.mp hi
          obtain ⟨atIndex, flag⟩ := List.mem_filter.mp mem
          have e := List.mk_mem_zipIdx_iff_getElem?.mp atIndex
          have eq : pairs[n] = row := by simpa [List.getElem?_eq_getElem bound] using e
          exact eq ▸ flag
        · intro h
          exact (CandidatePair.thresholdPositions_spec choice).2 i _ (List.getElem?_eq_getElem bound) h
      simp [TapscriptWitness.positionFlags, List.getElem?_range bound, List.getElem?_eq_getElem bound, inside]
    · have off : (List.range pairs.length)[i]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_lt bound)
      simp [TapscriptWitness.positionFlags, List.getElem?_eq_none (Nat.le_of_not_lt bound), off]
  have assembled := assemble_selected_frames (layout_choices rows) selected matchBits
  unfold CandidatePair.thresholdSatisfaction CandidatePair.thresholdSatisfactionFromCounts
  rw [choice]
  generalize eq : CandidatePair.assembleThreshold selected pairs.length (bits.count true) pairs.reverse = r at *
  cases r <;> simp_all [CandidateResult.usableWitness?]

private theorem bits_of_static_unsigned {pairs flags frames} (security : CandidatePair.SignatureSecurityList pairs flags)
    (rows : UnsignedLayout pairs (flags.map Bool.not) frames) :
    flags.map Bool.not = pairs.map CandidatePair.unsignedSat := by
  induction security generalizing frames with
  | nil => rfl
  | @cons pair flag ps fs head tail ih =>
    cases rows with
    | cons raw _ rest =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih rest⟩
      cases flag with
      | false =>
        obtain ⟨c, eq, h⟩ := raw
        change pair.sat = _ at eq
        simp [CandidatePair.unsignedSat, eq, h]
      | true =>
        cases h : pair.sat with
        | impossible => simp [CandidatePair.unsignedSat, h]
        | candidate c => simp [CandidatePair.unsignedSat, h, head.satSigned rfl c h]

theorem completeB_thresh_parent {k : Nat} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.thresh k children) → BSuccessCompleteIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf (CoreFragment.thresh k children) → BConditionFalseCompleteIn sc sub) :
    AmbientUnsignedSatCompleteBIn sc (.thresh k children) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  obtain ⟨truths, frames, rows, count, ownEq⟩ :=
    threshold_actual_layout typed wf mal nm ih df context nodup bounded run truth free
  obtain ⟨childMods, childMal, _allNm, _allE, bound⟩ := threshold_malleability_children mal nm
  have security := threshold_security (env := env) typed wf childMal
  obtain ⟨truthEq, countEq⟩ := unsigned_layout_eq_nonS security rows count (by simpa using bound)
  rw [truthEq] at rows
  have kept := usable_all_unsigned rows.layout (bits_of_static_unsigned security rows)
  have counts (bs : List Bool) : bs.count true = (bs.map Bool.toNat).sum := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [ih, Nat.add_comm]
  have quota : ((malleabilitySignedFlags childMods).map Bool.not).count true = k := by
    rw [← truthEq, counts, count]
  rw [quota, ← ownEq] at kept
  simpa only [satisfy, satisfactionCandidates, threshold_candidate_guard wf, if_true] using kept

theorem completeB_from_false_families (fragment : CoreFragment)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub)
    (ds : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) : BSuccessCompleteIn sc fragment := by
  have ih : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub := by
    intro sub smaller
    exact completeB_from_false_families sub
      (fun inner bound => df inner (Nat.lt_trans bound smaller))
      (fun inner bound => ds inner (Nat.lt_trans bound smaller))
  apply completeB_after_or_d fragment _ df ds
  intro sub bound residual cm mm typed wf mal nm _nonzero _zero _unsigned
  cases sub <;> simp only [RemainingBSuccessAfterOrD] at residual <;> try contradiction
  case thresh k children =>
    exact completeB_thresh_parent typed wf mal nm
      (fun child smaller => ih child (Nat.lt_of_lt_of_le smaller bound))
      (fun child smaller => df child (Nat.lt_of_lt_of_le smaller bound))
termination_by sizeOf fragment

theorem completeV_from_false_families {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub)
    (ds : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) :
    AmbientUnsignedSatCompleteVIn sc fragment := by
  apply completeV_from_smaller_B typed wf mal nm _ df
  intro sub smaller
  exact completeB_from_false_families sub
    (fun inner bound => df inner (Nat.lt_trans bound smaller))
    (fun inner bound => ds inner (Nat.lt_trans bound smaller))

end LeanMiniscript.Extraction.TapscriptRecovery.ThreshComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.UnsignedFalse

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI OrDC Dsat ThresholdUnit
  DsatMaterial UnsignedComplete VRestComplete OrBComplete

def UnsignedFalseIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.d = true → cm.u = true → mm.e = true → mm.s = false → AmbientDsatCompleteIn sc fragment

abbrev UnsignedFalse := UnsignedFalseIn .tapscript

inductive UnsignedFalseShape : CoreFragment → Prop where
  | or_b (X Y : CoreFragment) : UnsignedFalseShape (.or_b X Y)
  | or_d (X Y : CoreFragment) : UnsignedFalseShape (.or_d X Y)
  | or_i (X Y : CoreFragment) : UnsignedFalseShape (.or_i X Y)
  | andor (X Y Z : CoreFragment) : UnsignedFalseShape (.andor X Y Z)
  | d (X : CoreFragment) : UnsignedFalseShape (.d X)
  | j (X : CoreFragment) : UnsignedFalseShape (.j X)
  | n (X : CoreFragment) : UnsignedFalseShape (.n X)

theorem unsigned_false_shape {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩)
    (mal : HasMalleability sc fragment mm)
    (e : mm.e = true) (s : mm.s = false) : UnsignedFalseShape fragment := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case zero => cases mal; cases s
  case one => cases mal; cases e
  case older => cases mal; cases e
  case after => cases mal; cases e
  case sha256 => cases mal; cases e
  case hash256 => cases mal; cases e
  case ripemd160 => cases mal; cases e
  case hash160 => cases mal; cases e
  case and_v => cases mal; cases e
  case and_b =>
    cases mal with
    | and_b hx hy =>
      obtain ⟨_, _, sx, _⟩ := (boolAnd4_eq_true _ _ _ _).mp e
      simp [sx] at s
  case or_b => exact .or_b _ _
  case or_d => exact .or_d _ _
  case or_i => exact .or_i _ _
  case andor => exact .andor _ _ _
  case c_wrap => cases mal; cases s
  case d_wrap => exact .d _
  case j_wrap => exact .j _
  case n_wrap => exact .n _
  case thresh k first children cx types ft fd fu tt ts positive atMost =>
    cases mal with
    | thresh hm =>
      have count := allS_count_zero e
      simp only [MalleabilityModifiers.fewerThanNonS, count, decide_eq_false_iff_not] at s
      omega
  case multi => cases mal; cases s
  case multi_a => cases mal; cases s

theorem d_run_input {X : CoreFragment} {cm : CorrectnessModifiers}
    {input rest : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (typed : HasType sc X ⟨.V, cm⟩) (wf : X.WellFormed sc) (zero : cm.z = true)
    (run : Eval (compile (.d X)) input [] flags ctx (.success (top :: rest) [])) : input = top :: rest := by
  have combined : Eval ([.op .OP_DUP] ++ ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF]))
      input [] flags ctx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, midAlt, dupRun, conditional⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (.atom (by simp [NonConditional])) combined
  cases input with
  | nil =>
    have failed := Eval.fixedArityStackUnderflow_result
      (opcode := .OP_DUP) (required := 1) (arity := rfl) (underflow := by simp) dupRun
    contradiction
  | cons selector tail =>
    have canonical : Eval [.op .OP_DUP] (selector :: tail) [] flags ctx
        (.success (selector :: selector :: tail) []) := Eval.dup selector tail [] [] flags ctx _ Eval.done
    cases Eval.result_unique dupRun canonical
    rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditional with
      ⟨_falsehood, eq, _altEq⟩ | ⟨_truth, childRun⟩
    · exact eq.symm
    · obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf _ _ _ _ _ childRun
      obtain ⟨args, eq, arity⟩ := effect.v_inv
      have empty := List.eq_nil_of_length_eq_zero (arity.1 zero)
      simpa [empty] using eq

theorem ambientDsatComplete_d {X : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc X ⟨.V, cm⟩) (wf : X.WellFormed sc) (zero : cm.z = true) :
    AmbientDsatCompleteIn sc (.d X) := by
  intro parent env flags pa po own top rest context _nodup _bounded run falsehood _free
  have inputEq := d_run_input typed wf zero run
  rw [inputEq] at run
  have topEq : top = falseElement := by
    change Eval (.op .OP_DUP :: (.op .OP_IF :: (compile X ++ [.op .OP_ENDIF]))) _ _ _ _ _ at run
    generalize outputEq : ExecResult.success (top :: rest) [] = output at run
    cases run <;> try { simp_all [Opcode.isUpgradeableNop]; done }
    case dup =>
      rename_i next
      cases outputEq
      rcases Active.minimal_selector_of_rules context.rules (if_minimal_of_success next) with h | h
      · exact h
      · rw [h] at falsehood; cases falsehood
    all_goals cases outputEq
  have ownEq : own = [falseElement] := by
    rw [topEq] at inputEq
    have stackEq : own.toInitialStack = [falseElement] :=
      List.append_cancel_right (show own.toInitialStack ++ rest = [falseElement] ++ rest from inputEq)
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  subst own
  rfl

theorem j_run_cases {X : CoreFragment} {input rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.j X)) input [] flags ctx (.success (top :: rest) [])) :
    (input = falseElement :: rest ∧ top = falseElement) ∨
    Eval (compile X) input [] flags ctx (.success (top :: rest) []) := by
  change Eval ([.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
    input [] flags ctx (.success (top :: rest) []) at run
  cases run with
  | size operand tail alt script flags ctx result inner =>
    cases inner with
    | zeroNotEqual sizeBytes value tail' alt' script' flags' ctx' result' decoded conditionalRun =>
      have canonical := decodeScriptNum_scriptNat_of_le_maxScriptElementSize (bounded operand (by simp)) flags.minimalData
      rw [canonical] at decoded
      cases decoded
      have conditional : Eval ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
          (boolToElement ((operand.size : Int) != 0) :: operand :: tail) [] flags ctx (.success (top :: rest) []) := by
        simpa [List.append_assoc] using conditionalRun
      rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditional with
        ⟨falsehood, outEq, _altEq⟩ | ⟨_selected, childRun⟩
      · have sizeZero : operand.size = 0 := by simpa using falsehood
        have empty := ByteArray.size_eq_zero_iff.mp sizeZero
        have eq := List.cons.inj outEq
        have emptyEq : operand = falseElement := by
          apply ByteArray.ext
          simpa [falseElement] using congrArg ByteArray.data empty
        exact Or.inl ⟨by simp [emptyEq, eq.2], eq.1.trans emptyEq⟩
      · exact Or.inr childRun
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem ambientDsatComplete_j {X : CoreFragment} (forced : AmbientForcedFalseIn sc X)
    (signed : ∀ env, (satisfactionCandidates X env).dsat.Signed) :
    AmbientDsatCompleteIn sc (.j X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  rcases j_run_cases bounded run with ⟨inputEq, _topEq⟩ | childRun
  · have ownEq : own = [falseElement] := by
      have stackEq : own.toInitialStack = [falseElement] :=
        List.append_cancel_right (show own.toInitialStack ++ rest = [falseElement] ++ rest from inputEq)
      simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
    subst own
    change ((CandidateResult.usable [falseElement] false).select
      (satisfactionCandidates X env).dsat.requireNonemptyRuntimeTop.markNonCanonical).usableWitness? = _
    rw [rawUnsigned_select_signed_eq
      (show RawUnsigned (CandidateResult.usable [falseElement] false) from ⟨_, rfl, rfl⟩)
      (signed env).requireNonemptyRuntimeTop.markNonCanonical]
    rfl
  · have cc := executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h)
    exact (free (forced parent env flags pa po own top rest cc nodup bounded childRun falsehood)).elim

def UnsignedForcedNuIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.n = true → cm.u = true → mm.f = true → mm.s = false → AmbientForcedFalseIn sc fragment

abbrev UnsignedForcedNu := UnsignedForcedNuIn .tapscript

theorem unsignedFalse_d (child : CoreFragment) : UnsignedFalseIn sc (.d child) := by
  intro cm mm typed wf _mal _nm _d _u _e _s
  cases typed with
  | d_wrap tx zero => exact ambientDsatComplete_d tx wf zero

theorem unsignedFalse_j (child : CoreFragment) (forced : UnsignedForcedNuIn sc child) :
    UnsignedFalseIn sc (.j child) := by
  intro cm mm typed wf mal nm _d u e s
  cases typed with
  | j_wrap tx nonzero =>
    cases mal with
    | j hx =>
      exact ambientDsatComplete_j (forced _ _ tx wf hx nm nonzero u e s)
        (fun env => (malleabilityCandidateSound env (show child.WellFormed sc from wf) tx hx).forcedDsat e)

theorem or_d_unsigned_guards {X Y : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_d X Y) mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (u : cm.u = true) (e : mm.e = true) (s : mm.s = false) :
    ∃ cx cy mx my,
      HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧ cy.d = true ∧ cy.u = true ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.e = true ∧ my.e = true ∧
      ((mx.s = true ∧ my.s = false) ∨ (mx.s = false ∧ my.s = true)) := by
  cases typed with
  | or_d tx dx ux ty =>
    cases mal with
    | or_d hx hy =>
      obtain ⟨nx, ny, ex, signed⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      refine ⟨_, _, _, _, tx, dx, ux, ty, d, u, hx, hy, nx, ny, ex, e, ?_⟩
      have split : ∀ a b : Bool, (a || b) = true → (a && b) = false →
          ((a = true ∧ b = false) ∨ (a = false ∧ b = true)) := by
        intro a b
        cases a <;> cases b <;> simp
      exact split _ _ signed s

theorem unsignedFalse_or_d (X Y : CoreFragment)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → UnsignedFalseIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → SignedDsatCompleteBIn sc sub) :
    UnsignedFalseIn sc (.or_d X Y) := by
  intro cm mm typed wf mal nm d u e s
  obtain ⟨cx, cy, mx, my, tx, dx, ux, ty, dy, uy, hx, hy, nx, ny, ex, ey, split⟩ :=
    or_d_unsigned_guards typed mal nm d u e s
  apply ambientDsatComplete_or_d tx ty wf.1 wf.2
  · rcases split with ⟨sx, _sy⟩ | ⟨sx, _sy⟩
    · exact signed X (by simp; omega) cx mx tx wf.1 hx nx dx ex sx
    · exact ih X (by simp; omega) cx mx tx wf.1 hx nx dx ux ex sx
  · rcases split with ⟨_sx, sy⟩ | ⟨_sx, sy⟩
    · exact ih Y (by simp; omega) cy my ty wf.2 hy ny dy uy ey sy
    · exact signed Y (by simp; omega) cy my ty wf.2 hy ny dy ey sy

theorem n_false_decoded {X : CoreFragment} {input rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.n X)) input [] flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ value, Eval (compile X) input [] flags ctx (.success (value :: rest) []) ∧
      decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) := by
  change Eval (compile X ++ [.op .OP_0NOTEQUAL]) input [] flags ctx (.success (top :: rest) []) at run
  obtain ⟨mid, midAlt, childRun, normalize⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  cases normalize with
  | zeroNotEqual operand value tail alt script flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      have zero : value = 0 := by simpa using falsehood
      exact ⟨operand, childRun, by simpa [zero] using decoded⟩
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

def DecodedZeroDsatCompleteIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (value : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (value :: rest) []) →
    decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) →
    ¬ CheckedSignature fragment env flags own → dissatisfy fragment env = some own

abbrev DecodedZeroDsatComplete := DecodedZeroDsatCompleteIn .tapscript

theorem ambientDsatComplete_n_of_decodedZero {X : CoreFragment} (complete : DecodedZeroDsatCompleteIn sc X) :
    AmbientDsatCompleteIn sc (.n X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  obtain ⟨value, childRun, zero⟩ := n_false_decoded run falsehood
  exact complete parent env flags pa po own value rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded childRun zero free

theorem conditionFalse_of_unsigned_signed {fragment : CoreFragment}
    (unsigned : UnsignedFalseIn sc fragment) (signed : SignedDsatCompleteBIn sc fragment) :
    BConditionFalseCompleteIn sc fragment := by
  intro cm mm typed wf mal nm d u e
  cases s : mm.s with
  | false => exact unsigned cm mm typed wf mal nm d u e s
  | true => exact signed cm mm typed wf mal nm d e s

end LeanMiniscript.Extraction.TapscriptRecovery.UnsignedFalse
