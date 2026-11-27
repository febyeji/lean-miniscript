import LeanMiniscript.Extraction.TapscriptRecovery.KeyExecution

/-! Decompose threshold executions into typed B and W rows and assemble unsigned witnesses. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdAlt

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI SignedV WBoolean

theorem child_size_lt_list {child : CoreFragment} {children : List CoreFragment}
    (member : child ∈ children) : sizeOf child < sizeOf children := by
  induction children with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp; omega
    · have smaller := ih member
      simp only [List.cons.sizeOf_spec]
      omega

theorem uniform_savedAltTransfer (fragment : CoreFragment) : SavedAltTransfer fragment :=
  fun _ _ _ _ _ run => Miniscript.Eval.compile_erase_altStack run

theorem uniform_savedAltPremise (fragment : CoreFragment) : SavedAltPremise fragment := by
  intro _mods _mm _typed _wf _mal _nm
  exact uniform_savedAltTransfer fragment

theorem ambientExecutionW_step {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.W, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremise child) :
    AmbientExecutionW fragment :=
  ambientExecutionW_from_smaller_B typed wf mal nm ihB (fun child _ => uniform_savedAltTransfer child)

theorem ambientExecutionB_from_threshold {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingBThresh child → BExecutionPremise child) :
    AmbientExecutionB fragment :=
  ambientExecutionB_from_thresh_and_transfer typed wf mal nm remaining
    (fun child _ => uniform_savedAltPremise child)

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdAlt

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdRun

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat SignedV WBoolean
  ThresholdAlt

export _root_.LeanMiniscript.Extraction.TapscriptWitness (TailRunTrace)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (TailRunTrace.input_frame)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (typed_thresh_tail_inv)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (typed_threshold_run_inv)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_witness_frame)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_candidate_guard)

theorem threshold_malleability_children {k : Nat} {children : List CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability .tapscript (.thresh k children) mm) (nm : mm.nonMalleable = true) :
    ∃ childMods, HasMalleabilityList .tapscript children childMods ∧
      MalleabilityModifiers.allNonMalleable childMods = true ∧
      MalleabilityModifiers.allE childMods = true ∧ MalleabilityModifiers.countNonS childMods ≤ k := by
  cases mal with
  | thresh childrenMal =>
    obtain ⟨allNm, allE, count⟩ := (boolAnd3_eq_true _ _ _).mp nm
    exact ⟨_, childrenMal, allNm, allE, by simpa [MalleabilityModifiers.atMostNonS] using count⟩

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_children_static)

theorem threshold_children_dsat_unsigned {k : Nat} {children : List CoreFragment}
    {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (env : SatEnv) : ∀ child ∈ children, RawUnsigned (satisfactionCandidates child env).dsat := by
  intro child member
  obtain ⟨ty, cm, ct, cw, ch, cn, ce⟩ := threshold_children_static typed wf mal nm child member
  exact expressive_rawUnsigned cw ct ch cn ce env

inductive UnsignedRows : List CandidatePair → Nat → Prop where
  | nil : UnsignedRows [] 0
  | dsat {children : List CandidatePair} {child : CandidatePair} {count : Nat}
      (previous : UnsignedRows children count) (unsigned : RawUnsigned child.dsat) :
      UnsignedRows (children ++ [child]) count
  | sat {children : List CandidatePair} {child : CandidatePair} {count : Nat}
      (previous : UnsignedRows children count) (unsigned : RawUnsigned child.sat) :
      UnsignedRows (children ++ [child]) (count + 1)

theorem UnsignedRows.selected {children : List CandidatePair} {count : Nat}
    (rows : UnsignedRows children count) : RawUnsigned (CandidatePair.selectExactly count children) := by
  induction rows with
  | nil => exact ⟨_, rfl, rfl⟩
  | @dsat children child count previous unsigned ih =>
    rw [CandidatePair.selectExactly_append]
    cases count with
    | zero => rw [CandidatePair.extendCounts_getD_zero]; exact unsigned_combine ih unsigned
    | succ count =>
      rw [CandidatePair.extendCounts_getD_succ]
      exact unsigned_select_left_raw (unsigned_combine ih unsigned)
  | sat previous unsigned ih =>
    rw [CandidatePair.selectExactly_append, CandidatePair.extendCounts_getD_succ]
    exact unsigned_select_right_raw (unsigned_combine ih unsigned)

private theorem flags_snoc (positions : List Nat) (n : Nat) :
    TapscriptWitness.positionFlags positions (n + 1) = TapscriptWitness.positionFlags positions n ++ [decide (n ∈ positions)] := by
  simp [TapscriptWitness.positionFlags, List.range_succ]

private def IncludesUnsigned (positions : List Nat) (children : List CandidatePair) : Prop :=
  ∀ i child, children[i]? = some child → child.unsignedSat = true → i ∈ positions

private theorem IncludesUnsigned.prior {positions : List Nat} {children : List CandidatePair} {last}
    (inc : IncludesUnsigned positions (children ++ [last])) : IncludesUnsigned positions children := by
  intro i child found unsigned
  apply inc i child _ unsigned
  rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]

private theorem IncludesUnsigned.last {positions : List Nat} {children : List CandidatePair} {child}
    (inc : IncludesUnsigned positions (children ++ [child])) (raw : RawUnsigned child.sat) :
    children.length ∈ positions := by
  obtain ⟨c, eq, flag⟩ := raw
  exact inc _ child (by simp) (by simp [CandidatePair.unsignedSat, eq, flag])

private theorem UnsignedRows.count_le {children : List CandidatePair} {count positions}
    (rows : UnsignedRows children count) (inc : IncludesUnsigned positions children) :
    count ≤ (TapscriptWitness.positionFlags positions children.length).count true := by
  induction rows with
  | nil => exact Nat.zero_le _
  | dsat _ _ ih =>
    have prev := ih inc.prior
    simp only [List.length_append, List.length_singleton, flags_snoc, List.count_append]
    omega
  | sat _ raw ih =>
    have prev := ih inc.prior
    simpa [flags_snoc, inc.last raw] using Nat.succ_le_succ prev

private theorem UnsignedRows.assemble {children : List CandidatePair} {count positions}
    (rows : UnsignedRows children count) (inc : IncludesUnsigned positions children)
    (quota : (TapscriptWitness.positionFlags positions children.length).count true = count) :
    RawUnsigned (CandidatePair.assembleThreshold positions children.length count children.reverse) := by
  induction rows with
  | nil => exact ⟨_, rfl, rfl⟩
  | @dsat children child count prev raw ih =>
    simp only [List.length_append, List.length_singleton, flags_snoc, List.count_append] at quota
    have earlier := prev.count_le inc.prior
    have skip : children.length ∉ positions := by
      intro mem
      simp [mem] at quota
      omega
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.length_append,
      List.length_singleton, CandidatePair.assembleThreshold, Nat.add_one_sub_one, skip, if_false]
    exact unsigned_combine (ih inc.prior (by simpa [skip] using quota)) raw
  | @sat children child count prev raw ih =>
    have take := inc.last raw
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.length_append,
      List.length_singleton, CandidatePair.assembleThreshold, Nat.add_one_sub_one, take, if_true]
    exact unsigned_combine (ih inc.prior (by simpa [flags_snoc, take] using quota)) raw

private theorem assemble_count {positions : List Nat} {count} {prior : List CandidatePair}
    (possible : (CandidatePair.assembleThreshold positions prior.length count prior).Possible) :
    (TapscriptWitness.positionFlags positions prior.length).count true = count := by
  induction prior generalizing count with
  | nil => cases count <;> simp_all [TapscriptWitness.positionFlags, CandidatePair.assembleThreshold, CandidateResult.Possible]
  | cons row prior ih =>
    simp only [List.length_cons, CandidatePair.assembleThreshold, Nat.add_one_sub_one] at possible
    simp only [List.length_cons, flags_snoc, List.count_append]
    split at possible
    next take =>
      cases count with
      | zero => contradiction
      | succ count =>
        have h := ih ((CandidateResult.combine_possible_iff _ _).mp possible).1
        simp [take, h]
    next skip =>
      have h := ih ((CandidateResult.combine_possible_iff _ _).mp possible).1
      simp [skip, h]

theorem UnsignedRows.threshold_unsigned {children : List CandidatePair} {count}
    (rows : UnsignedRows children count) : RawUnsigned (CandidatePair.thresholdSatisfaction count children) := by
  rcases CandidatePair.thresholdSatisfaction_cases count children with fallback | ⟨positions, c, chosen, eq, result⟩
  · obtain ⟨c, ec, flag⟩ := rows.selected
    rw [fallback, ec]
    exact ⟨_, rfl, flag⟩
  · have possible : (CandidatePair.assembleThreshold positions children.reverse.length count children.reverse).Possible := by
      rw [List.length_reverse, eq]
      exact fun h => nomatch h
    obtain ⟨c', e, flag⟩ := rows.assemble ((CandidatePair.thresholdPositions_spec chosen).2) (by simpa using assemble_count possible)
    rw [eq] at e
    cases e
    exact ⟨_, result, flag⟩

theorem threshold_sat_unsigned_of_rows {k : Nat} {children : List CoreFragment} {env : SatEnv}
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (rows : UnsignedRows (satisfactionCandidatesList children env) k) :
    RawUnsigned (satisfactionCandidates (.thresh k children) env).sat := by
  simpa only [satisfactionCandidates, _root_.LeanMiniscript.Extraction.TapscriptWitness.threshold_candidate_guard wf, if_true] using rows.threshold_unsigned

export _root_.LeanMiniscript.Extraction.TapscriptWitness (decoded_unit_count)

inductive EvidenceRows (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags) :
    List CandidatePair → Nat → Witness → Prop where
  | nil : EvidenceRows parent env flags [] 0 []
  | dsat {children : List CandidatePair} {child : CandidatePair} {count : Nat} {previous : Witness}
      (own : Witness) (prior : EvidenceRows parent env flags children count previous)
      (unsigned : RawUnsigned child.dsat) :
      EvidenceRows parent env flags (children ++ [child]) count (own ++ previous)
  | sat {children : List CandidatePair} {child : CandidatePair} {count : Nat} {previous : Witness}
      (own : Witness) (prior : EvidenceRows parent env flags children count previous)
      (evidence : RawUnsigned child.sat ∨ CheckedSignature parent env flags own) :
      EvidenceRows parent env flags (children ++ [child]) (count + 1) (own ++ previous)

theorem threshold_evidence_of_rows {k : Nat} {children : List CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {consumed : Witness}
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (rows : EvidenceRows (.thresh k children) env flags (satisfactionCandidatesList children env) k consumed) :
    ExecutionEvidence (.thresh k children) env flags consumed := by
  have classify {pairs count own} (trace : EvidenceRows (.thresh k children) env flags pairs count own) :
      UnsignedRows pairs count ∨ CheckedSignature (.thresh k children) env flags own := by
    induction trace with
    | nil => exact .inl .nil
    | dsat _ _ raw ih =>
      rcases ih with prev | h
      · exact .inl (.dsat prev raw)
      · exact .inr (checkedSignature_mono (fun _ h => h) (fun _ h => List.mem_append_right _ h) h)
    | sat _ _ proof ih =>
      rcases ih with prev | h
      · rcases proof with raw | h
        · exact .inl (.sat prev raw)
        · exact .inr (checkedSignature_mono (fun _ h => h) (fun _ h => List.mem_append_left _ h) h)
      · exact .inr (checkedSignature_mono (fun _ h => h) (fun _ h => List.mem_append_right _ h) h)
  exact (classify rows).imp (threshold_sat_unsigned_of_rows wf) id

theorem threshold_singleton_run {k : Nat} {child : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript (.thresh k [child]) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k [child]).WellFormed .tapscript)
    {input rest alt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.thresh k [child])) input alt flags ctx (.success (top :: rest) alt))
    (truth : castToBool top = true) :
    Eval (compile child) input alt flags ctx (.success (scriptNat k :: rest) alt) := by
  obtain ⟨_, _, first, remaining, firstMods, types, args, firstRest, value,
    eq, _, _, _, _, _, inputEq, firstRun, trace⟩ := typed_threshold_run_inv typed wf run truth
  cases eq
  cases trace
  rw [← inputEq] at firstRun
  exact firstRun

theorem threshold_singleton_execution {k : Nat} {child : CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript (.thresh k [child]) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k [child]).WellFormed .tapscript)
    (execute : AmbientExecutionB child) : AmbientExecutionB (.thresh k [child]) := by
  have kEq : k = 1 := by have := wf.1; simp only [validThreshold, List.length_singleton] at this; omega
  subst k
  intro parent env flags pa po consumed top rest context bounded run truth
  have childRun := threshold_singleton_run typed wf run truth
  have childContext := executionContext_restrict context (active := child)
    (fun _ h => by simpa [CoreFragment.keys, CoreFragment.keysList] using h)
    (fun _ h => by simpa [CoreFragment.hashLocks, CoreFragment.hashLocksList] using h)
    (fun _ h => h)
  rcases execute parent env flags pa po consumed (scriptNat 1) rest childContext bounded childRun (by decide) with hu | hs
  · apply Or.inl
    apply threshold_sat_unsigned_of_rows wf
    have rows := UnsignedRows.sat (child := satisfactionCandidates child env) UnsignedRows.nil hu
    simpa [satisfactionCandidatesList] using rows
  · exact Or.inr (checkedSignature_mono
      (fun _ h => by simpa [CoreFragment.keys, CoreFragment.keysList] using h) (fun _ h => h) hs)

theorem threshold_child_smaller {k : Nat} {children : List CoreFragment} {child : CoreFragment}
    (member : child ∈ children) : sizeOf child < sizeOf (CoreFragment.thresh k children) := by
  have smaller := child_size_lt_list member
  simp only [CoreFragment.thresh.sizeOf_spec]
  omega

theorem threshold_singleton_step {k : Nat} {child : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.thresh k [child]) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k [child]).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.thresh k [child]) mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ fragment, sizeOf fragment < sizeOf (CoreFragment.thresh k [child]) → BExecutionPremise fragment) :
    AmbientExecutionB (.thresh k [child]) := by
  apply threshold_singleton_execution typed wf
  obtain ⟨ty, cm, _ct, cw, ch, cn, _ce⟩ := threshold_children_static typed wf mal nm child (by simp)
  cases typed with
  | thresh childTyped _ _ _ _ _ _ =>
    exact ihB child (threshold_child_smaller (by simp)) _ cm childTyped cw ch cn

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_rest_member_type)

def RemainingMultiThreshold : CoreFragment → Prop
  | .thresh _ children => 2 ≤ children.length
  | _ => False

theorem ambientExecutionB_from_multiThreshold {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (remaining : ∀ child, sizeOf child ≤ sizeOf fragment → RemainingMultiThreshold child → BExecutionPremise child) :
    AmbientExecutionB fragment := by
  have childB : ∀ child, sizeOf child < sizeOf fragment → BExecutionPremise child := by
    intro child smaller cm hm tc wc hc nc
    exact ambientExecutionB_from_multiThreshold tc wc hc nc
      (fun residual bound h => remaining residual (Nat.le_trans bound (Nat.le_of_lt smaller)) h)
  apply ambientExecutionB_from_threshold typed wf mal nm
  intro residual bound isRemaining cm hm tc wc hc nc
  cases residual <;> simp only [RemainingBThresh] at isRemaining
  all_goals try contradiction
  case thresh k children =>
    cases children with
    | nil =>
      obtain ⟨first, rest, impossible⟩ := typed_thresh_has_children tc
      cases impossible
    | cons first rest =>
      cases rest with
      | nil =>
        exact threshold_singleton_step tc wc hc nc
          (fun child smaller => childB child (Nat.lt_of_lt_of_le smaller bound))
      | cons second tail => exact remaining _ bound (by simp [RemainingMultiThreshold]) cm hm tc wc hc nc
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdRun

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdRows

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat SignedV WBoolean ThresholdAlt
  ThresholdRun

theorem decoded_size {value : StackElement} {n : Int} {minimal : Bool}
    (decoded : decodeScriptNum value minimal maxArithmeticScriptNumBytes = .ok n) :
    value.size ≤ maxScriptElementSize := by
  unfold decodeScriptNum at decoded
  split at decoded
  · contradiction
  · change ¬ value.size > 4 at ‹¬ _›
    change value.size ≤ 520
    omega

theorem nat_boundary_decode {n : Nat} {value : Int} {minimal : Bool}
    (bound : n ≤ maxArithmeticScriptNatExclusive)
    (decoded : decodeScriptNum (scriptNat n) minimal maxArithmeticScriptNumBytes = .ok value) :
    n < maxArithmeticScriptNatExclusive ∧ value = n := by
  have strict : n < maxArithmeticScriptNatExclusive := by
    by_cases lt : n < maxArithmeticScriptNatExclusive
    · exact lt
    · have eq : n = maxArithmeticScriptNatExclusive := by omega
      subst n
      have oversized : (scriptNat maxArithmeticScriptNatExclusive).size > maxArithmeticScriptNumBytes := by decide
      simp [decodeScriptNum, oversized] at decoded
  exact ⟨strict, Except.ok.inj (decoded.symm.trans (decodeScriptNum_scriptNat_of_lt strict minimal))⟩

export _root_.LeanMiniscript.Extraction.TapscriptWitness (TailRunTrace.initial_decode)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (UnitB)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (UnitW)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_keys_member)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_locks_member)

theorem tail_rows {env : SatEnv} {flags : ScriptFlags} {root parent : CoreFragment}
    {pa po : Witness} {children : List CoreFragment} {acc final : StackElement}
    {input rest : Stack} {k : Nat}
    (trace : TailRunTrace flags env.txCtx [] children acc input final rest)
    (finalEq : final = scriptNat k) (kbound : k < maxArithmeticScriptNatExclusive)
    (executors : ∀ child ∈ children, AmbientExecutionW child)
    (units : ∀ child ∈ children, UnitW child)
    (falseRows : ∀ child ∈ children, RawUnsigned (satisfactionCandidates child env).dsat)
    (keys : ∀ child ∈ children, ∀ key ∈ child.keys, key ∈ root.keys)
    (locks : ∀ child ∈ children, ∀ lock ∈ child.hashLocks, lock ∈ root.hashLocks)
    (remaining previous : Witness) (prior : List CandidatePair) (count : Nat)
    (frame : input = remaining.toInitialStack ++ rest)
    (context : ExecutionContext parent root env flags pa po (remaining ++ previous))
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (countBound : count < maxArithmeticScriptNatExclusive)
    (decoded : decodeScriptNum acc flags.minimalData maxArithmeticScriptNumBytes = .ok (count : Int))
    (rows : EvidenceRows root env flags prior count previous) :
    EvidenceRows root env flags (prior ++ satisfactionCandidatesList children env) k (remaining ++ previous) := by
  cases trace with
  | nil =>
    have empty : remaining = [] := by
      have eq : remaining.toInitialStack = [] := by simpa using frame.symm
      simpa [Witness.toInitialStack] using congrArg List.reverse eq
    subst remaining
    rw [finalEq, decodeScriptNum_scriptNat_of_lt kbound flags.minimalData] at decoded
    have numbers := Except.ok.inj decoded
    have eq : count = k := Int.ofNat.inj numbers.symm
    subst count
    simpa [satisfactionCandidatesList] using rows
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
    have childBound : ∀ item ∈ acc :: (Witness.toInitialStack args.reverse ++ tail), item.size ≤ maxScriptElementSize := by
      simpa [Witness.toInitialStack] using
        (show ∀ item ∈ acc :: (args ++ tail), item.size ≤ maxScriptElementSize from
          fun item member => by
            rcases List.mem_cons.mp member with rfl | member
            · exact decoded_size da
            · exact bounded item member)
    have childRun : Eval (compile child) (acc :: (Witness.toInitialStack args.reverse ++ tail)) [] flags env.txCtx
        (.success (order.outputs acc result ++ tail) []) := by simpa [Witness.toInitialStack] using run
    have unit := units child (by simp) env flags args.reverse acc result tail order context.version childBound childRun
    have bEq := decoded_unit_count db unit
    have aEq : a = (count : Int) := Except.ok.inj (da.symm.trans decoded)
    have sumEq : a + b = ((count + (castToBool result).toNat : Nat) : Int) := by
      rw [aEq, bEq]
      simp
    have nextDecode := TailRunTrace.initial_decode next finalEq kbound
    obtain ⟨nextN, nextDecoded⟩ := nextDecode
    rw [sumEq] at nextDecoded
    have nextLe : count + (castToBool result).toNat ≤ maxArithmeticScriptNatExclusive := by
      cases castToBool result <;> simp <;> omega
    obtain ⟨nextBound, nextEq⟩ := nat_boundary_decode nextLe nextDecoded
    rw [nextEq] at nextDecoded
    have nextRows : EvidenceRows root env flags (prior ++ [satisfactionCandidates child env])
        (count + (castToBool result).toNat) (args.reverse ++ previous) := by
      cases truth : castToBool result with
      | false => simpa [truth] using EvidenceRows.dsat args.reverse rows (falseRows child (by simp))
      | true =>
        have evidence := executors child (by simp) parent env flags pa po args.reverse acc result tail order
          childContext childBound childRun truth
        have promoted : RawUnsigned (satisfactionCandidates child env).sat ∨ CheckedSignature root env flags args.reverse :=
          evidence.imp_right (checkedSignature_mono (keys child (by simp)) (fun _ h => h))
        simpa [truth] using EvidenceRows.sat args.reverse rows promoted
    have nextContext : ExecutionContext parent root env flags pa po (tailArgs.reverse ++ (args.reverse ++ previous)) := by
      simpa [ownEq, List.append_assoc] using context
    have nextFrame : tail = Witness.toInitialStack tailArgs.reverse ++ rest := by
      simpa [Witness.toInitialStack] using tailEq
    have nextBounded : ∀ item ∈ tail, item.size ≤ maxScriptElementSize :=
      fun item member => bounded item (List.mem_append_right _ member)
    have answer := tail_rows next finalEq kbound
      (fun c h => executors c (by simp [h])) (fun c h => units c (by simp [h]))
      (fun c h => falseRows c (by simp [h])) (fun c h => keys c (by simp [h]))
      (fun c h => locks c (by simp [h])) tailArgs.reverse (args.reverse ++ previous)
      (prior ++ [satisfactionCandidates child env]) (count + (castToBool result).toNat)
      nextFrame nextContext nextBounded nextBound (by simpa [sumEq] using nextDecoded) nextRows
    simpa [satisfactionCandidatesList, ownEq, List.append_assoc] using answer
termination_by sizeOf children

theorem threshold_execution_of_units {k : Nat} {children : List CoreFragment}
    {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ fragment, sizeOf fragment < sizeOf (CoreFragment.thresh k children) → BExecutionPremise fragment)
    (unitsB : ∀ child ∈ children, ∀ cm, HasType .tapscript child ⟨.B, cm⟩ → cm.u = true → UnitB child)
    (unitsW : ∀ child ∈ children, ∀ cm, HasType .tapscript child ⟨.W, cm⟩ → cm.u = true → UnitW child) :
    AmbientExecutionB (.thresh k children) := by
  intro parent env flags pa po consumed top rest context bounded run truth
  obtain ⟨first, remaining, firstMods, types, firstArgs, tailArgs, value,
    eq, ft, _fd, fu, tt, ts, witnessEq, firstRun, trace⟩ := threshold_witness_frame typed wf run truth
  subst children
  subst consumed
  have member : first ∈ first :: remaining := by simp
  have firstKeys := threshold_keys_member member
  have firstLocks := threshold_locks_member member
  have firstIn : ∀ item ∈ firstArgs.reverse, item ∈ tailArgs.reverse ++ firstArgs.reverse :=
    fun _ h => List.mem_append_right _ h
  have firstContext := executionContext_restrict context (active := first) firstKeys firstLocks firstIn
  have firstBound : ∀ item ∈ firstArgs ++ (tailArgs ++ rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  have firstUnit := unitsB first member firstMods ft fu env flags _ _ value context.version firstBound firstRun
  obtain ⟨_ty, firstMM, _ct, fw, fm, fn, _fe⟩ := threshold_children_static typed wf mal nm first member
  have firstExecute := ihB first (threshold_child_smaller member) firstMods firstMM ft fw fm fn
  have firstRun' : Eval (compile first) (Witness.toInitialStack firstArgs.reverse ++ (tailArgs ++ rest)) [] flags env.txCtx
      (.success (value :: (tailArgs ++ rest)) []) := by simpa [Witness.toInitialStack] using firstRun
  have firstRows : EvidenceRows (.thresh k (first :: remaining)) env flags
      [satisfactionCandidates first env] (castToBool value).toNat firstArgs.reverse := by
    cases h : castToBool value with
    | false =>
      simpa [h] using EvidenceRows.dsat (parent := .thresh k (first :: remaining)) (flags := flags)
        firstArgs.reverse EvidenceRows.nil (threshold_children_dsat_unsigned typed wf mal nm env first member)
    | true =>
      have evidence := firstExecute parent env flags pa po firstArgs.reverse value (tailArgs ++ rest)
        firstContext (by simpa [Witness.toInitialStack] using firstBound) firstRun' h
      have promoted : RawUnsigned (satisfactionCandidates first env).sat ∨
          CheckedSignature (.thresh k (first :: remaining)) env flags firstArgs.reverse :=
        evidence.imp_right (checkedSignature_mono firstKeys (fun _ h => h))
      simpa [h] using EvidenceRows.sat firstArgs.reverse EvidenceRows.nil promoted
  have kbound : k < maxArithmeticScriptNatExclusive := wf.2.2.2
  obtain ⟨firstN, firstDecoded⟩ := TailRunTrace.initial_decode trace rfl kbound
  rw [decoded_unit_count firstDecoded firstUnit] at firstDecoded
  have executeTail : ∀ child ∈ remaining, AmbientExecutionW child := by
    intro child member
    obtain ⟨cm, ct, _cd, _cu⟩ := threshold_rest_member_type tt ts child member
    have member' : child ∈ first :: remaining := by simp [member]
    obtain ⟨_ty, hm, _ct, cw, ch, cn, _ce⟩ := threshold_children_static typed wf mal nm child member'
    exact ambientExecutionW_step ct cw ch cn
      (fun sub smaller => ihB sub (Nat.lt_trans smaller (threshold_child_smaller member')))
  have unitTail : ∀ child ∈ remaining, UnitW child := by
    intro child member
    obtain ⟨cm, ct, _cd, cu⟩ := threshold_rest_member_type tt ts child member
    exact unitsW child (by simp [member]) cm ct cu
  have countBound : (castToBool value).toNat < maxArithmeticScriptNatExclusive := by
    cases castToBool value <;> decide
  have rows := tail_rows (root := .thresh k (first :: remaining)) trace rfl kbound executeTail unitTail
    (fun child h => threshold_children_dsat_unsigned typed wf mal nm env child (by simp [h]))
    (fun child h => threshold_keys_member (show child ∈ first :: remaining by simp [h]))
    (fun child h => threshold_locks_member (show child ∈ first :: remaining by simp [h]))
    tailArgs.reverse firstArgs.reverse [satisfactionCandidates first env] (castToBool value).toNat
    (by simp [Witness.toInitialStack]) context
    (fun item h => firstBound item (List.mem_append_right _ h)) countBound firstDecoded firstRows
  apply threshold_evidence_of_rows wf
  simpa [satisfactionCandidatesList] using rows

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdRows

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdUnit

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI SignedV BWrappers ThresholdRun
  ThresholdRows

theorem if_minimal_of_success {script : Script} {selector : StackElement} {input alt output outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (.op .OP_IF :: script) (selector :: input) alt flags ctx (.success output outAlt)) :
    minimalIfSatisfied flags ctx.sigVersion selector := by
  generalize resultEq : ExecResult.success output outAlt = result at run
  cases run <;> simp_all [Opcode.isUpgradeableNop]

theorem unit_d {X : CoreFragment} {mx : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.V, mx⟩) (wx : X.WellFormed .tapscript)
    (zero : mx.z = true) : UnitB (.d X) := by
  intro env flags input rest top version _bounded run truth
  have rx := d_success_child run truth
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ rx
  obtain ⟨args, eq, arity⟩ := effect.v_inv
  have empty : args = [] := List.eq_nil_of_length_eq_zero (arity.1 zero)
  have inputEq : input = top :: rest := by simpa [empty] using eq
  rw [inputEq] at run
  change Eval (.op .OP_DUP :: (.op .OP_IF :: (compile X ++ [.op .OP_ENDIF]))) _ _ _ _ _ at run
  generalize outputEq : ExecResult.success (top :: rest) [] = output at run
  cases run <;> try { simp_all [Opcode.isUpgradeableNop]; done }
  case dup =>
    rename_i next
    cases outputEq
    have minimal := if_minimal_of_success next
    rcases minimal_selector version minimal with falseTop | trueTop
    · rw [falseTop] at truth
      cases truth
    · exact trueTop
  all_goals cases outputEq

export _root_.LeanMiniscript.Extraction.TapscriptWitness (unitB_of_hasType)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (unitW_of_hasType)

theorem threshold_execution_step {k : Nat} {children : List CoreFragment}
    {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ihB : ∀ fragment, sizeOf fragment < sizeOf (CoreFragment.thresh k children) → BExecutionPremise fragment) :
    AmbientExecutionB (.thresh k children) := by
  apply threshold_execution_of_units typed wf mal nm ihB
  · intro child member cm ct cu
    obtain ⟨_ty, _mm, _ct, cw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm child member
    exact unitB_of_hasType ct cw cu
  · intro child member cm ct cu
    obtain ⟨_ty, _mm, _ct, cw, _ch, _cn, _ce⟩ := threshold_children_static typed wf mal nm child member
    exact unitW_of_hasType ct cw cu

theorem ambientExecutionB_of_judgments {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true) :
    AmbientExecutionB fragment := by
  apply ambientExecutionB_from_multiThreshold typed wf mal nm
  intro child bound residual cm hm tc wc hc nc
  cases child <;> simp only [RemainingMultiThreshold] at residual
  all_goals try contradiction
  case thresh k children =>
    apply threshold_execution_step tc wc hc nc
    intro sub smaller sm sh st sw ss sn
    exact ambientExecutionB_of_judgments st sw ss sn
termination_by sizeOf fragment
decreasing_by omega

theorem uniform_B_execution : ∀ fragment, BExecutionPremise fragment := by
  intro fragment mods mm typed wf mal nm
  exact ambientExecutionB_of_judgments typed wf mal nm

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdUnit

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdCanonical

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction ThresholdRun

def rowResult (pair : CandidatePair) (truth : Bool) : CandidateResult :=
  if truth then pair.sat else pair.dsat

inductive RowLayout : List CandidatePair → List Bool → List Witness → Prop where
  | nil : RowLayout [] [] []
  | cons {child : CandidatePair} {children : List CandidatePair} {truth : Bool} {truths : List Bool}
      {own : Witness} {frames : List Witness}
      (selected : (rowResult child truth).usableWitness? = some own)
      (tail : RowLayout children truths frames) :
      RowLayout (child :: children) (truth :: truths) (own :: frames)

def assemble (frames : List Witness) : Witness :=
  ((frames.map Witness.toInitialStack).flatten).reverse

theorem assemble_cons (own : Witness) (frames : List Witness) :
    assemble (own :: frames) = assemble frames ++ own := by
  simp [assemble, Witness.toInitialStack]

export _root_.LeanMiniscript.Extraction.TapscriptWitness (TailTruths)

theorem child_keys_nodup {children : List CoreFragment} {child : CoreFragment}
    (nodup : (CoreFragment.keysList children).Nodup) (member : child ∈ children) : child.keys.Nodup := by
  induction children with
  | nil => simp at member
  | cons first children ih =>
    obtain ⟨head, tail, _cross⟩ := List.pairwise_append.mp nodup
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih tail member

theorem allWF_member {children : List CoreFragment}
    (wf : CoreFragment.allWellFormed .tapscript children) {child : CoreFragment}
    (member : child ∈ children) : child.WellFormed .tapscript := by
  induction children with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact wf.1
    · exact ih wf.2 member

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_trace_truth_count)

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdCanonical

namespace LeanMiniscript.Extraction.TapscriptRecovery.ThresholdSelection

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction ThresholdRun

inductive TruthIncluded : List Bool → List Bool → Prop where
  | nil : TruthIncluded [] []
  | cons {a c : Bool} {actual selected : List Bool}
      (head : a = true → c = true) (tail : TruthIncluded actual selected) :
      TruthIncluded (a :: actual) (c :: selected)

theorem truthIncluded_count_le {actual selected : List Bool}
    (included : TruthIncluded actual selected) :
    (actual.map Bool.toNat).sum ≤ (selected.map Bool.toNat).sum := by
  induction included with
  | nil => simp
  | @cons a c actual selected head tail ih =>
    cases a <;> cases c <;> simp_all [Bool.toNat, List.sum_cons] <;> omega

theorem truthIncluded_eq_of_count {actual selected : List Bool}
    (included : TruthIncluded actual selected)
    (count : (actual.map Bool.toNat).sum = (selected.map Bool.toNat).sum) :
    actual = selected := by
  induction included with
  | nil => rfl
  | @cons a c actual selected head tail ih =>
    have monotone := truthIncluded_count_le tail
    cases a <;> cases c <;> simp_all [Bool.toNat, List.sum_cons] <;> omega

end LeanMiniscript.Extraction.TapscriptRecovery.ThresholdSelection
