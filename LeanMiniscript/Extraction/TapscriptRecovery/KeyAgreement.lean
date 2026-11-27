import LeanMiniscript.Extraction.TapscriptRecovery.BooleanAgreement

/-! Complete compound key agreement and reduce B agreement to the threshold case. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.KAgreement

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Transport Active OrI BExecution
  SignedV CompoundK OriginCounts CheckedRows SlotLocal CompositeRows
  VConditions BChoiceMaterial DAgreement

def PendingTrueK (fragment root : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) : Prop :=
  ∀ (own expected : Witness) (sig keyBytes : StackElement) (rest : Stack),
    ExecutionContext root fragment env flags pa po ([sig] ++ own) → fragment.keys.Nodup →
    satisfy fragment env = some expected →
    (∀ item ∈ own.toInitialStack ++ (sig :: rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
      (.success (keyBytes :: sig :: rest) []) →
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig keyBytes = .ok true →
    [sig] ++ own = expected

theorem pending_checked {fragment root : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness} {sig keyBytes : StackElement} {rest : Stack}
    (typed : HasType .tapscript fragment ⟨.K, cm⟩) (wf : fragment.WellFormed .tapscript)
    (context : ExecutionContext root fragment env flags pa po ([sig] ++ own))
    (run : Eval (compile fragment) (own.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
      (.success (keyBytes :: sig :: rest) []))
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig keyBytes = .ok true) :
    CheckedSignature fragment env flags ([sig] ++ own) := by
  have cc := executionContext_restrict context (active := fragment)
    (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_append_right _ h)
  obtain ⟨key, member, eq⟩ := keyOutput_of_typed typed wf root env flags pa po own keyBytes (sig :: rest) cc run
  exact ⟨sig, by simp, key, member, by simpa [eq] using checked⟩

theorem pending_of_checked_c {fragment root : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (typed : HasType .tapscript fragment ⟨.K, cm⟩) (wf : fragment.WellFormed .tapscript)
    (agreement : CheckedTrueRowAgreementB (.c fragment) root env flags pa po) :
    PendingTrueK fragment root env flags pa po := by
  intro own expected sig keyBytes rest context nodup canonical bounded run checked
  have crun : Eval (compile (.c fragment)) (Witness.toInitialStack ([sig] ++ own) ++ rest) [] flags env.txCtx
      (.success (trueElement :: rest) []) := by
    simpa [compile, compileWithKeyHash, Witness.toInitialStack, List.reverse_append, List.append_assoc] using
      Eval.append run (Eval.checksigTrue checked (Eval.done (stack := trueElement :: rest)))
  have cc : ExecutionContext root (.c fragment) env flags pa po ([sig] ++ own) :=
    executionContext_restrict context (fun _ h => h) (fun _ h => h) (fun _ h => h)
  exact agreement _ expected trueElement rest cc nodup (by simpa using canonical)
    (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded)
    crun (by decide) (by simpa only [CheckedSignature, CoreFragment.keys] using pending_checked typed wf context run checked)

theorem checked_c_of_pending {fragment root : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (typed : HasType .tapscript fragment ⟨.K, cm⟩) (wf : fragment.WellFormed .tapscript)
    (agreement : PendingTrueK fragment root env flags pa po) :
    CheckedTrueRowAgreementB (.c fragment) root env flags pa po := by
  intro other expected top rest context nodup canonical bounded run truth _checked
  obtain ⟨own, sig, keyBytes, eq, krun, checked⟩ := c_run_frame typed wf run truth
  subst other
  have cc : ExecutionContext root fragment env flags pa po ([sig] ++ own) :=
    executionContext_restrict context (fun _ h => h) (fun _ h => h) (fun _ h => h)
  exact agreement own expected sig keyBytes rest cc nodup (by simpa using canonical)
    (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded) krun checked

theorem pending_and_v {X Y root : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (tx : HasType .tapscript X ⟨.V, cx⟩) (ty : HasType .tapscript Y ⟨.K, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (nx : mx.nonMalleable = true)
    (ix : CheckedTrueRowAgreementV X root env flags pa po)
    (iy : PendingTrueK Y root env flags pa po) : PendingTrueK (.and_v X Y) root env flags pa po := by
  intro own expected sig keyBytes rest context nodup canonical bounded run checked
  obtain ⟨ox, oy, ownEq, rx, ry⟩ := and_v_run_K_frame tx ty wx wy run
  subst own
  obtain ⟨sx, sy, satX, satY, expectedEq⟩ := CandidateResult.combine_usableWitness_iff.mp canonical
  have cc : ExecutionContext root (.and_v X Y) env flags pa po (([sig] ++ oy) ++ ox) := by
    simpa only [List.append_assoc] using context
  have bound : ∀ item ∈ Witness.toInitialStack (([sig] ++ oy) ++ ox) ++ rest, item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts cc
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) bound
  have ex := agree_V tx wx hx nx ix ccx (List.pairwise_append.mp nodup).1 satX bx
    (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using rx)
  have ey := iy oy sy sig keyBytes rest ccy (List.pairwise_append.mp nodup).2.1 satY
    (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using byBound) ry checked
  simp only [expectedEq, ← ex, ← ey, Witness.combine, List.append_assoc]

theorem pending_or_i {X Y root : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (tx : HasType .tapscript X ⟨.K, cx⟩) (ty : HasType .tapscript Y ⟨.K, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (material : CheckedMaterial (.or_i X Y) root env flags pa po)
    (ix : PendingTrueK X root env flags pa po) (iy : PendingTrueK Y root env flags pa po) :
    PendingTrueK (.or_i X Y) root env flags pa po := by
  intro own expected sig keyBytes rest context nodup canonical bounded run checked
  rcases or_i_run_K tx ty wx wy context.version run with ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have included : ∀ item ∈ [sig] ++ active, item ∈ [sig] ++ (active ++ [trueElement]) := by
      intro item member; simpa only [List.append_assoc] using List.mem_append_left [trueElement] member
    have cc := executionContext_restrict context (active := X) (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ h) included
    have evidence := pending_checked tx wx cc childRun checked
    obtain ⟨selected, satX, expectedEq⟩ := or_i_selected_left material context nodup canonical included (Or.inr evidence)
    have eq := ix active selected sig keyBytes rest cc (List.pairwise_append.mp nodup).1 satX
      (bounded_without_selector bounded) childRun checked
    rw [expectedEq, ← eq, List.append_assoc]
  · subst own
    have included : ∀ item ∈ [sig] ++ active, item ∈ [sig] ++ (active ++ [falseElement]) := by
      intro item member; simpa only [List.append_assoc] using List.mem_append_left [falseElement] member
    have cc := executionContext_restrict context (active := Y) (fun _ h => List.mem_append_right _ h)
      (fun _ h => List.mem_append_right _ h) included
    have evidence := pending_checked ty wy cc childRun checked
    obtain ⟨selected, satY, expectedEq⟩ := or_i_selected_right material context nodup canonical included (Or.inr evidence)
    have eq := iy active selected sig keyBytes rest cc (List.pairwise_append.mp nodup).2.1 satY
      (bounded_without_selector bounded) childRun checked
    rw [expectedEq, ← eq, List.append_assoc]

theorem pending_andor {X Y Z root : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (d : cx.d = true) (u : cx.u = true)
    (ty : HasType .tapscript Y ⟨.K, cy⟩) (tz : HasType .tapscript Z ⟨.K, cz⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript) (wz : Z.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (nx : mx.nonMalleable = true) (ex : mx.e = true)
    (material : CheckedMaterial (.andor X Y Z) root env flags pa po)
    (ix : CheckedTrueRowAgreementB X root env flags pa po)
    (iy : PendingTrueK Y root env flags pa po) (iz : PendingTrueK Z root env flags pa po) :
    PendingTrueK (.andor X Y Z) root env flags pa po := by
  intro own expected sig keyBytes rest context nodup canonical bounded run checked
  have kx : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have ky : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have kz : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys := fun _ h => List.mem_append_right _ h
  have lx : ∀ lock ∈ X.hashLocks, lock ∈ (CoreFragment.andor X Y Z).hashLocks :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have ly : ∀ lock ∈ Y.hashLocks, lock ∈ (CoreFragment.andor X Y Z).hashLocks :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have lz : ∀ lock ∈ Z.hashLocks, lock ∈ (CoreFragment.andor X Y Z).hashLocks := fun _ h => List.mem_append_right _ h
  have ndXY := (List.pairwise_append.mp nodup).1
  have ndx := (List.pairwise_append.mp ndXY).1
  have ndy := (List.pairwise_append.mp ndXY).2.1
  have ndz := (List.pairwise_append.mp nodup).2.1
  have sepXZ : ∀ key ∈ X.keys, ∀ other ∈ Z.keys, key ≠ other :=
    fun key hk other ho => (List.pairwise_append.mp nodup).2.2 key (List.mem_append_left _ hk) other ho
  have sepYZ : ∀ key ∈ Y.keys, ∀ other ∈ Z.keys, key ≠ other :=
    fun key hk other ho => (List.pairwise_append.mp nodup).2.2 key (List.mem_append_right _ hk) other ho
  rcases andor_run_K_frame tx ty tz wx wy wz run with
      ⟨ox, oz, value, ownEq, runX, falsehood, runZ⟩ | ⟨ox, oy, value, ownEq, runX, truth, runY⟩
  · subst own
    have cc : ExecutionContext root (.andor X Y Z) env flags pa po (([sig] ++ oz) ++ ox) := by
      simpa only [List.append_assoc] using context
    have bound : ∀ item ∈ Witness.toInitialStack (([sig] ++ oz) ++ ox) ++ rest, item.size ≤ maxScriptElementSize := by
      simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
    obtain ⟨ccx, ccz, bx, bz⟩ := split_contexts cc kx kz lx lz bound
    have evidenceZ := pending_checked tz wz ccz runZ checked
    have inZ : ∀ item ∈ [sig] ++ oz, item ∈ [sig] ++ (oz ++ ox) := by
      intro item member; simpa only [List.append_assoc] using List.mem_append_left ox member
    rcases andor_candidate_rows canonical with
        ⟨sx, sy, expectedEq, satX, satY, _excluded⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, _excluded⟩
    · have sourcesZ : Items (LocalSlot Z env ([sig] ++ oz) []) expected := by
        rw [expectedEq]
        exact items_combine
          ((foreign_pair ccz (fun key member => context.childKeys key (kx key member))
            (fun key hk other ho => Ne.symm (sepXZ other ho key hk))).1 sx satX)
          ((foreign_pair ccz (fun key member => context.childKeys key (ky key member))
            (fun key hk other ho => Ne.symm (sepYZ other ho key hk))).1 sy satY)
      exact (free_of_sources material context canonical kz inZ sourcesZ evidenceZ).elim
    · have freeX := fallback_noChecked material context ccx tx wx hx nx ex canonical expectedEq
        dsatX satZ kx kz (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) sepXZ
      have eqX := false_agreement tx wx hx nx d u ex ccx ndx dsatX bx
        (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using runX) falsehood freeX
      have eqZ := iz oz sz sig keyBytes rest ccz ndz satZ
        (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bz) runZ checked
      rw [expectedEq, ← eqX, ← eqZ, List.append_assoc]
  · subst own
    have cc : ExecutionContext root (.andor X Y Z) env flags pa po (([sig] ++ oy) ++ ox) := by
      simpa only [List.append_assoc] using context
    have bound : ∀ item ∈ Witness.toInitialStack (([sig] ++ oy) ++ ox) ++ rest, item.size ≤ maxScriptElementSize := by
      simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
    obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts cc kx ky lx ly bound
    have evidenceY := pending_checked ty wy ccy runY checked
    have inY : ∀ item ∈ [sig] ++ oy, item ∈ [sig] ++ (oy ++ ox) := by
      intro item member; simpa only [List.append_assoc] using List.mem_append_left ox member
    rcases andor_candidate_rows canonical with
        ⟨sx, sy, expectedEq, satX, satY, _excluded⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, _excluded⟩
    · have eqX := agree_B tx wx hx nx ix ccx ndx satX bx
        (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using runX) truth
      have eqY := iy oy sy sig keyBytes rest ccy ndy satY
        (by simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using byBound) runY checked
      rw [expectedEq, ← eqX, ← eqY, List.append_assoc]
    · have sourcesY : Items (LocalSlot Y env ([sig] ++ oy) []) expected := by
        rw [expectedEq]
        exact items_combine (dsat_sources tx wx hx nx ex context.sound
          (fun key member => context.keySizes key (context.childKeys key (kx key member))) dsatX)
          ((foreign_pair ccy (fun key member => context.childKeys key (kz key member)) sepYZ).1 sz satZ)
      exact (free_of_sources material context canonical ky inY sourcesY evidenceY).elim

theorem pending_from_smaller_B {fragment root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (typed : HasType .tapscript fragment ⟨.K, cm⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB fragment root env flags pa po) : PendingTrueK fragment root env flags pa po := by
  have smaller : ∀ sub, sizeOf sub < sizeOf fragment → ∀ cx mx,
      HasType .tapscript sub ⟨.K, cx⟩ → sub.WellFormed .tapscript →
      HasMalleability .tapscript sub mx → mx.nonMalleable = true → SlotPath sub root →
      PendingTrueK sub root env flags pa po := by
    intro sub small cx mx tx wx hx nx subPath
    apply pending_from_smaller_B tx wx hx nx subPath rootNodup rootCanonical
    intro inner innerSmall ci mi ti wi hi ni innerPath
    exact ihB inner (Nat.lt_trans innerSmall small) ci mi ti wi hi ni innerPath
  have material := checkedMaterial_canonical_root (env := env) (flags := flags) (pa := pa) (po := po)
    path rootNodup rootCanonical
  cases typed_K_shape typed with
  | pk_k key => exact pending_of_checked_c typed wf (checkedTrue_c_pk_k key root env flags pa po)
  | pk_h key => exact pending_of_checked_c typed wf (checkedTrue_c_pk_h key root env flags pa po)
  | and_v tx ty =>
    obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
    have ix := checkedV_from_smaller_B tx wf.1 hx nx (path_trans (.left .and_v .here) path) rootNodup
      (fun sub small cx mx tx wx hx nx subPath => ihB sub
        (Nat.lt_trans small (by simp; omega)) cx mx tx wx hx nx subPath)
    exact pending_and_v tx ty wf.1 wf.2.1 hx nx ix
      (smaller _ (by simp; omega) _ _ ty wf.2.1 hy ny (path_trans (.right .and_v .here) path))
  | or_i tx ty =>
    obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
    exact pending_or_i tx ty wf.1 wf.2 material
      (smaller _ (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .or_i .here) path))
      (smaller _ (by simp; omega) _ _ ty wf.2 hy ny (path_trans (.right .or_i .here) path))
  | andor tx d u ty tz =>
    obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
    exact pending_andor tx d u ty tz wf.1 wf.2.1 wf.2.2.1 hx nx ex material
      (ihB _ (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.condition .here) path))
      (smaller _ (by simp; omega) _ _ ty wf.2.1 hy ny (path_trans (.thenBranch .here) path))
      (smaller _ (by simp; omega) _ _ tz wf.2.2.1 hz nz (path_trans (.elseBranch .here) path))
termination_by sizeOf fragment

theorem checked_c_step {fragment root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (typed : HasType .tapscript (.c fragment) ⟨.B, cm⟩) (wf : (CoreFragment.c fragment).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.c fragment) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.c fragment) root) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB (.c fragment) root env flags pa po) :
    CheckedTrueRowAgreementB (.c fragment) root env flags pa po := by
  obtain ⟨cx, mx, tx, wx, hx, nx⟩ := c_static typed wf mal nm
  apply checked_c_of_pending tx wx
  apply pending_from_smaller_B tx wx hx nx (path_trans (.wrapper .c .here) path) rootNodup rootCanonical
  intro sub small cy my ty wy hy ny subPath
  exact ihB sub (Nat.lt_trans small (by simp)) cy my ty wy hy ny subPath

theorem pending_only_c_or_thresh {fragment : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (pending : BPendingWithoutD fragment) :
    (∃ child, fragment = .c child) ∨ (∃ k children, fragment = .thresh k children) := by
  cases fragment <;> simp_all [BPendingWithoutD, CoreFragment.keys]
  all_goals cases typed
  exact noLegacyMulti_tapscript _ _ wf

theorem checkedB_threshold_step {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootWF : root.WellFormed .tapscript) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB fragment root env flags pa po)
    (ihV : SmallerCheckedV fragment root env flags pa po)
    (rest : (∃ k children, fragment = .thresh k children) → CheckedTrueRowAgreementB fragment root env flags pa po) :
    CheckedTrueRowAgreementB fragment root env flags pa po := by
  apply checkedB_without_d_step typed wf mal nm path rootWF rootNodup rootCanonical ihB ihV
  intro pending
  rcases pending_only_c_or_thresh typed wf pending with ⟨child, rfl⟩ | threshold
  · exact checked_c_step typed wf mal nm path rootNodup rootCanonical ihB
  · exact rest threshold

end LeanMiniscript.Extraction.TapscriptRecovery.KAgreement
