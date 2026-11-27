import LeanMiniscript.Extraction.TapscriptRecovery.UnsignedAtoms

/-! Recover unsigned witnesses of V and B branches under their modifier hypotheses. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.VRestComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI OrDC Dsat SignedV ThresholdRun
  ThresholdUnit SignedExchange UnsignedComplete ZeroComplete NFComplete
  BnVnComplete

theorem select_left_of_signed_alternative {left right : CandidateResult}
    (guard : left.Signed ∨ right.Signed) (raw : RawUnsigned left) : left.select right = left := by
  rcases guard with signed | signed
  · exact (signed_excludes_unsigned signed raw).elim
  · exact rawUnsigned_select_signed_eq raw signed

theorem select_right_of_signed_alternative {left right : CandidateResult}
    (guard : left.Signed ∨ right.Signed) (raw : RawUnsigned right) : left.select right = right := by
  rcases guard with signed | signed
  · exact signed_select_rawUnsigned_eq signed raw
  · exact (signed_excludes_unsigned signed raw).elim

theorem unsigned_V_run {fragment parent : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness} {rest : Stack}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContextIn sc parent fragment env flags pa po own)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest []))
    (free : ¬ CheckedSignature fragment env flags own) : RawUnsigned (satisfactionCandidates fragment env).sat := by
  exact execution_without_checked_signature
    (ambientExecutionV_from_smaller_B typed wf mal nm (fun sub _ => uniform_B_execution sub)
      parent env flags pa po own rest context bounded run) free

theorem or_c_choice_guard {X Y : CoreFragment} {cx cy : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (mal : HasMalleability sc (.or_c X Y) mm) (nm : mm.nonMalleable = true) (env : SatEnv) :
    (satisfactionCandidates X env).sat.Signed ∨
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat).Signed := by
  obtain ⟨mx, my, hx, hy, _nx, _ny, _ex, signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
  rcases signed with sx | sy
  · exact Or.inl ((malleabilityCandidateSound env wx tx hx).signedSat sx)
  · exact Or.inr ((malleabilityCandidateSound env wy ty hy).signedSat sy).combine_right

theorem andor_choice_guard {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (tz : HasType sc Z ⟨.V, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true) (env : SatEnv) :
    ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).Signed ∨
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat).Signed := by
  cases mal with
  | andor hx hy hz =>
    obtain ⟨_nx, _ny, _nz, _ex, signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    rcases Bool.or_eq_true_iff.mp signed with xy | sz
    · rcases Bool.or_eq_true_iff.mp xy with sx | sy
      · exact Or.inl ((malleabilityCandidateSound env wx tx hx).signedSat sx).combine_left
      · exact Or.inl ((malleabilityCandidateSound env wy ty hy).signedSat sy).combine_right
    · exact Or.inr ((malleabilityCandidateSound env wz tz hz).signedSat sz).combine_right

theorem completeV_or_i {X Y : CoreFragment} {cx cy : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.V, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (mal : HasMalleability sc (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (ix : AmbientUnsignedSatCompleteVIn sc X) (iy : AmbientUnsignedSatCompleteVIn sc Y) :
    AmbientUnsignedSatCompleteVIn sc (.or_i X Y) := by
  obtain ⟨mx, my, hx, hy, nx, ny, signed⟩ := or_i_malleability_children mal nm
  intro parent env flags pa po own rest context nodup bounded run free
  have guard : ((satisfactionCandidates X env).sat.withSelector trueElement).Signed ∨
      ((satisfactionCandidates Y env).sat.withSelector falseElement).Signed := by
    rcases signed with sx | sy
    · exact Or.inl (((malleabilityCandidateSound env wx tx hx).signedSat sx).withSelector _)
    · exact Or.inr (((malleabilityCandidateSound env wy ty hy).signedSat sy).withSelector _)
  rcases or_i_run_V tx ty wx wy context.rules run with ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have inChild : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
    have keys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_left _ h
    have cc := executionContext_restrict context keys (fun _ h => List.mem_append_left _ h) inChild
    have absent : ¬ CheckedSignature X env flags active := fun checked => free (checkedSignature_mono keys inChild checked)
    have raw := unsigned_V_run tx wx hx nx cc (bounded_without_selector bounded) childRun absent
    have selected := ix parent env flags pa po active rest cc (List.pairwise_append.mp nodup).1
      (bounded_without_selector bounded) childRun absent
    change ((satisfactionCandidates X env).sat.withSelector trueElement |>.select
      ((satisfactionCandidates Y env).sat.withSelector falseElement)).usableWitness? = some (active ++ [trueElement])
    rw [select_left_of_signed_alternative guard (unsigned_withSelector raw)]
    exact CandidateResult.withSelector_usableWitness_iff.mpr ⟨active, selected, rfl⟩
  · subst own
    have inChild : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
    have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_right _ h
    have cc := executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inChild
    have absent : ¬ CheckedSignature Y env flags active := fun checked => free (checkedSignature_mono keys inChild checked)
    have raw := unsigned_V_run ty wy hy ny cc (bounded_without_selector bounded) childRun absent
    have selected := iy parent env flags pa po active rest cc (List.pairwise_append.mp nodup).2.1
      (bounded_without_selector bounded) childRun absent
    change ((satisfactionCandidates X env).sat.withSelector trueElement |>.select
      ((satisfactionCandidates Y env).sat.withSelector falseElement)).usableWitness? = some (active ++ [falseElement])
    rw [select_right_of_signed_alternative guard (unsigned_withSelector raw)]
    exact CandidateResult.withSelector_usableWitness_iff.mpr ⟨active, selected, rfl⟩

theorem completeV_or_c {X Y : CoreFragment} {cx cy : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (mal : HasMalleability sc (.or_c X Y) mm) (nm : mm.nonMalleable = true)
    (ix : AmbientUnsignedSatCompleteBIn sc X) (iy : AmbientUnsignedSatCompleteVIn sc Y)
    (dx : AmbientDsatCompleteIn sc X) : AmbientUnsignedSatCompleteVIn sc (.or_c X Y) := by
  obtain ⟨mx, my, hx, hy, nx, ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
  intro parent env flags pa po own rest context nodup bounded run free
  have guard := or_c_choice_guard tx ty wx wy mal nm env
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_c X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_c X Y).keys := fun _ h => List.mem_append_right _ h
  rcases shortCircuit_run_frame (keep := false) (top := falseElement) tx ty wx wy run with
      ⟨top, runX, truth⟩ | ⟨left, right, top, eq, runX, falsehood, runY⟩
  · have cc := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) (fun _ h => h)
    have absent : ¬ CheckedSignature X env flags own := fun checked => free (checkedSignature_mono keysX (fun _ h => h) checked)
    have raw := execution_without_checked_signature
      (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po own top rest cc bounded runX truth) absent
    have selected := ix parent env flags pa po own top rest cc (List.pairwise_append.mp nodup).1 bounded runX truth absent
    change ((satisfactionCandidates X env).sat.select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)).usableWitness? = some own
    rw [select_left_of_signed_alternative guard raw]
    exact selected
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
    have ccY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
    have absentY : ¬ CheckedSignature Y env flags right := fun checked => free (checkedSignature_mono keysY inY checked)
    have boundY : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
      fun item h => all item (List.mem_append_right _ h)
    have rawY := unsigned_V_run ty wy hy ny ccY boundY runY absentY
    have raw := unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env) rawY
    have selectedX := dx parent env flags pa po left top (right.toInitialStack ++ rest) ccX
      (List.pairwise_append.mp nodup).1 all runX falsehood absentX
    have selectedY := iy parent env flags pa po right rest ccY (List.pairwise_append.mp nodup).2.1 boundY runY absentY
    change ((satisfactionCandidates X env).sat.select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)).usableWitness? = some (right ++ left)
    rw [select_right_of_signed_alternative guard raw]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩

theorem completeV_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (tz : HasType sc Z ⟨.V, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (ix : AmbientUnsignedSatCompleteBIn sc X) (iy : AmbientUnsignedSatCompleteVIn sc Y)
    (iz : AmbientUnsignedSatCompleteVIn sc Z) (dx : AmbientDsatCompleteIn sc X) :
    AmbientUnsignedSatCompleteVIn sc (.andor X Y Z) := by
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
  intro parent env flags pa po own rest context nodup bounded run free
  have guard := andor_choice_guard tx ty tz wx wy wz mal nm env
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  have ndXY := (List.pairwise_append.mp nodup).1
  have ndX := (List.pairwise_append.mp ndXY).1
  have ndY := (List.pairwise_append.mp ndXY).2.1
  have ndZ := (List.pairwise_append.mp nodup).2.1
  rcases andor_run_V_frame tx ty tz wx wy wz run with
      ⟨left, right, top, eq, runX, falsehood, runZ⟩ | ⟨left, right, top, eq, runX, truth, runY⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have ccZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
    have absentZ : ¬ CheckedSignature Z env flags right := fun checked => free (checkedSignature_mono keysZ inZ checked)
    have boundZ : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
      fun item h => all item (List.mem_append_right _ h)
    have rawZ := unsigned_V_run tz wz hz nz ccZ boundZ runZ absentZ
    have raw := unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env) rawZ
    have selectedX := dx parent env flags pa po left top (right.toInitialStack ++ rest) ccX ndX all runX falsehood absentX
    have selectedZ := iz parent env flags pa po right rest ccZ ndZ boundZ runZ absentZ
    change (((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat)).usableWitness? = some (right ++ left)
    rw [select_right_of_signed_alternative guard raw]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedZ, rfl⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have ccY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
    have absentY : ¬ CheckedSignature Y env flags right := fun checked => free (checkedSignature_mono keysY inY checked)
    have boundY : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
      fun item h => all item (List.mem_append_right _ h)
    have rawX := execution_without_checked_signature
      (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left top
        (right.toInitialStack ++ rest) ccX all runX truth) absentX
    have rawY := unsigned_V_run ty wy hy ny ccY boundY runY absentY
    have selectedX := ix parent env flags pa po left top (right.toInitialStack ++ rest) ccX ndX all runX truth absentX
    have selectedY := iy parent env flags pa po right rest ccY ndY boundY runY absentY
    change (((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat)).usableWitness? = some (right ++ left)
    rw [select_left_of_signed_alternative guard (unsigned_combine rawX rawY)]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩

def BSuccessCompleteIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true → AmbientUnsignedSatCompleteBIn sc fragment

abbrev BSuccessComplete := BSuccessCompleteIn .tapscript

def BConditionFalseCompleteIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.d = true → cm.u = true → mm.e = true → AmbientDsatCompleteIn sc fragment

abbrev BConditionFalseComplete := BConditionFalseCompleteIn .tapscript

theorem completeV_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (successB : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub)
    (falseB : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub) :
    AmbientUnsignedSatCompleteVIn sc fragment := by
  have childV : ∀ sub, sizeOf sub < sizeOf fragment → ∀ cx mx,
      HasType sc sub ⟨.V, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → AmbientUnsignedSatCompleteVIn sc sub := by
    intro sub smaller cx mx tx wx hx nx
    exact completeV_from_smaller_B tx wx hx nx
      (fun inner bound => successB inner (Nat.lt_trans bound smaller))
      (fun inner bound => falseB inner (Nat.lt_trans bound smaller))
  cases typed_V_shape typed with
  | verify tx =>
    cases mal with
    | v hx => exact complete_v (successB _ (by simp) _ _ tx wf hx nm)
  | and_v tx ty =>
    obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
    exact completeV_and_v tx ty wf.1 wf.2.1
      (childV _ (by simp; omega) _ _ tx wf.1 hx nx)
      (childV _ (by simp; omega) _ _ ty wf.2.1 hy ny)
  | or_i tx ty =>
    obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
    exact completeV_or_i tx ty wf.1 wf.2 mal nm
      (childV _ (by simp; omega) _ _ tx wf.1 hx nx)
      (childV _ (by simp; omega) _ _ ty wf.2 hy ny)
  | or_c tx d u ty =>
    obtain ⟨mx, my, hx, hy, nx, ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
    exact completeV_or_c tx ty wf.1 wf.2 mal nm
      (successB _ (by simp; omega) _ _ tx wf.1 hx nx)
      (childV _ (by simp; omega) _ _ ty wf.2 hy ny)
      (falseB _ (by simp; omega) _ _ tx wf.1 hx nx d u ex)
  | andor tx d u ty tz =>
    obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
    exact completeV_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 mal nm
      (successB _ (by simp; omega) _ _ tx wf.1 hx nx)
      (childV _ (by simp; omega) _ _ ty wf.2.1 hy ny)
      (childV _ (by simp; omega) _ _ tz wf.2.2.1 hz nz)
      (falseB _ (by simp; omega) _ _ tx wf.1 hx nx d u ex)
termination_by sizeOf fragment

def VSuccessCompleteIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.V, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true → AmbientUnsignedSatCompleteVIn sc fragment

abbrev VSuccessComplete := VSuccessCompleteIn .tapscript

theorem bSuccess_of_bn_rest {fragment : CoreFragment}
    (bn : CompleteBnIn sc fragment) (rest : CompleteBRestIn sc fragment) : BSuccessCompleteIn sc fragment := by
  intro cm mm typed wf mal nm
  apply completeB_split typed wf mal nm
  · intro nonzero
    cases signed : mm.s with
    | true => exact complete_of_signed typed wf mal nm signed
    | false => exact bn cm mm typed wf mal nm nonzero signed
  · exact fun nonzero zero unsigned => rest cm mm typed wf mal nm nonzero zero unsigned

theorem completeBnV_from_B_residuals (fragment : CoreFragment)
    (br : ∀ sub, sizeOf sub < sizeOf fragment → CompleteBRestIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub) :
    CompleteBnIn sc fragment ∧ VSuccessCompleteIn sc fragment := by
  have ih : ∀ sub, sizeOf sub < sizeOf fragment → CompleteBnIn sc sub ∧ VSuccessCompleteIn sc sub := by
    intro sub smaller
    exact completeBnV_from_B_residuals sub
      (fun inner bound => br inner (Nat.lt_trans bound smaller))
      (fun inner bound => df inner (Nat.lt_trans bound smaller))
  constructor
  · intro cm mm typed wf mal nm nonzero unsigned
    apply completeBn_step typed wf mal nm nonzero unsigned _ br
    intro sub smaller
    refine ⟨(ih sub smaller).1, ?_⟩
    intro cx mx tx wx hx nx _nonzero _unsigned
    exact (ih sub smaller).2 cx mx tx wx hx nx
  · intro cm mm typed wf mal nm
    exact completeV_from_smaller_B typed wf mal nm
      (fun sub smaller => bSuccess_of_bn_rest (ih sub smaller).1 (br sub smaller)) df
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.VRestComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.BRestComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Active OrI OrDC Dsat SignedV BExecution
  ThresholdUnit SignedExchange UnsignedComplete NFComplete BnVnComplete
  VRestComplete

theorem andor_B_choice_guard {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true) (env : SatEnv) :
    ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).Signed ∨
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat).Signed := by
  cases mal with
  | andor hx hy hz =>
    obtain ⟨_nx, _ny, _nz, _ex, signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    rcases Bool.or_eq_true_iff.mp signed with xy | sz
    · rcases Bool.or_eq_true_iff.mp xy with sx | sy
      · exact Or.inl ((malleabilityCandidateSound env wx tx hx).signedSat sx).combine_left
      · exact Or.inl ((malleabilityCandidateSound env wy ty hy).signedSat sy).combine_right
    · exact Or.inr ((malleabilityCandidateSound env wz tz hz).signedSat sz).combine_right

theorem completeB_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (ix : AmbientUnsignedSatCompleteBIn sc X) (iy : AmbientUnsignedSatCompleteBIn sc Y)
    (iz : AmbientUnsignedSatCompleteBIn sc Z) (dx : AmbientDsatCompleteIn sc X) :
    AmbientUnsignedSatCompleteBIn sc (.andor X Y Z) := by
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
  intro parent env flags pa po own resultTop rest context nodup bounded run outputTruth free
  have guard := andor_B_choice_guard tx ty tz wx wy wz mal nm env
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  have ndXY := (List.pairwise_append.mp nodup).1
  have ndX := (List.pairwise_append.mp ndXY).1
  have ndY := (List.pairwise_append.mp ndXY).2.1
  have ndZ := (List.pairwise_append.mp nodup).2.1
  rcases andor_run_B_frame tx ty tz wx wy wz run with
      ⟨left, right, top, eq, runX, falsehood, runZ⟩ | ⟨left, right, top, eq, runX, truth, runY⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have ccZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
    have absentZ : ¬ CheckedSignature Z env flags right := fun checked => free (checkedSignature_mono keysZ inZ checked)
    have boundZ : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
      fun item h => all item (List.mem_append_right _ h)
    have rawZ := execution_without_checked_signature
      (uniform_B_execution Z cz mz tz wz hz nz parent env flags pa po right resultTop rest ccZ boundZ runZ outputTruth) absentZ
    have raw := unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env) rawZ
    have selectedX := dx parent env flags pa po left top (right.toInitialStack ++ rest) ccX ndX all runX falsehood absentX
    have selectedZ := iz parent env flags pa po right resultTop rest ccZ ndZ boundZ runZ outputTruth absentZ
    change (((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat)).usableWitness? = some (right ++ left)
    rw [select_right_of_signed_alternative guard raw]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedZ, rfl⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have ccY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
    have absentY : ¬ CheckedSignature Y env flags right := fun checked => free (checkedSignature_mono keysY inY checked)
    have boundY : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
      fun item h => all item (List.mem_append_right _ h)
    have rawX := execution_without_checked_signature
      (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left top
        (right.toInitialStack ++ rest) ccX all runX truth) absentX
    have rawY := execution_without_checked_signature
      (uniform_B_execution Y cy my ty wy hy ny parent env flags pa po right resultTop rest ccY boundY runY outputTruth) absentY
    have selectedX := ix parent env flags pa po left top (right.toInitialStack ++ rest) ccX ndX all runX truth absentX
    have selectedY := iy parent env flags pa po right resultTop rest ccY ndY boundY runY outputTruth absentY
    change (((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat)).usableWitness? = some (right ++ left)
    rw [select_left_of_signed_alternative guard (unsigned_combine rawX rawY)]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩

inductive BRestShape : CoreFragment → Prop where
  | and_v (X Y : CoreFragment) : BRestShape (.and_v X Y)
  | and_b (X Y : CoreFragment) : BRestShape (.and_b X Y)
  | or_b (X Y : CoreFragment) : BRestShape (.or_b X Y)
  | or_d (X Y : CoreFragment) : BRestShape (.or_d X Y)
  | or_i (X Y : CoreFragment) : BRestShape (.or_i X Y)
  | andor (X Y Z : CoreFragment) : BRestShape (.andor X Y Z)
  | n (X : CoreFragment) : BRestShape (.n X)
  | thresh (k : Nat) (children : List CoreFragment) : BRestShape (.thresh k children)

theorem brest_shape {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (mal : HasMalleability sc fragment mm)
    (nonzero : cm.n = false) (zero : cm.z = false) (unsigned : mm.s = false) : BRestShape fragment := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have n : ty.mods.n = false := by rw [← typeEq]; exact nonzero
  have z : ty.mods.z = false := by rw [← typeEq]; exact zero
  cases typed <;> try { cases baseEq }
  case zero => cases z
  case one => cases z
  case older => cases z
  case after => cases z
  case sha256 => cases n
  case hash256 => cases n
  case ripemd160 => cases n
  case hash160 => cases n
  case and_v => exact .and_v _ _
  case and_b => exact .and_b _ _
  case or_b => exact .or_b _ _
  case or_d => exact .or_d _ _
  case or_i => exact .or_i _ _
  case andor => exact .andor _ _ _
  case c_wrap => cases mal; cases unsigned
  case d_wrap => cases n
  case j_wrap => cases n
  case n_wrap => exact .n _
  case thresh => exact .thresh _ _
  case multi => cases n
  case multi_a => cases mal; cases unsigned

theorem completeB_andor_parent {X Y Z : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → BSuccessCompleteIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → BConditionFalseCompleteIn sc sub) :
    AmbientUnsignedSatCompleteBIn sc (.andor X Y Z) := by
  obtain ⟨cx, cy, cz, tx, d, u, ty, tz⟩ := andor_B_typed_children typed
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
  exact completeB_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 mal nm
    (ih X (by simp; omega) cx mx tx wf.1 hx nx)
    (ih Y (by simp; omega) cy my ty wf.2.1 hy ny)
    (ih Z (by simp; omega) cz mz tz wf.2.2.1 hz nz)
    (df X (by simp; omega) cx mx tx wf.1 hx nx d u ex)

def RemainingBSuccess : CoreFragment → Prop
  | .or_b _ _ | .or_d _ _ | .thresh _ _ => True
  | _ => False

theorem completeBRest_step {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (nonzero : cm.n = false) (zero : cm.z = false) (unsigned : mm.s = false)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub)
    (remaining : RemainingBSuccess fragment → CompleteBRestIn sc fragment) : AmbientUnsignedSatCompleteBIn sc fragment := by
  cases brest_shape typed mal nonzero zero unsigned with
  | and_v X Y =>
    cases typed_B_shape typed with
    | and_v tx ty =>
      obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
      exact completeB_and_v tx ty wf.1 wf.2.1
        (completeV_from_smaller_B tx wf.1 hx nx
          (fun sub smaller => ih sub (Nat.lt_trans smaller (by simp; omega)))
          (fun sub smaller => df sub (Nat.lt_trans smaller (by simp; omega))))
        (ih Y (by simp; omega) _ my ty wf.2.1 hy ny)
    | remaining impossible => cases impossible
  | and_b X Y =>
    cases typed with
    | and_b tx ty => cases mal with
      | and_b hx hy =>
        obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
        obtain ⟨_sx, sy⟩ := Bool.or_eq_false_iff.mp unsigned
        exact completeB_and_b tx ty wf.1 wf.2.1
          (ih X (by simp; omega) _ _ tx wf.1 hx nx)
          (completeW_unsigned ty wf.2.1 hy ny sy (by
            intro sub smaller cx mx tx wx hx nx _unsigned
            exact ih sub (Nat.lt_trans smaller (by simp; omega)) cx mx tx wx hx nx))
  | or_b X Y => exact remaining trivial _ _ typed wf mal nm nonzero zero unsigned
  | or_d X Y => exact remaining trivial _ _ typed wf mal nm nonzero zero unsigned
  | or_i X Y =>
    cases typed_B_shape typed with
    | or_i tx ty =>
      obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
      exact complete_or_i tx ty wf.1 wf.2 mal nm
        (ih X (by simp; omega) _ mx tx wf.1 hx nx)
        (ih Y (by simp; omega) _ my ty wf.2 hy ny)
    | remaining impossible => cases impossible
  | andor X Y Z => exact completeB_andor_parent typed wf mal nm ih df
  | n child =>
    cases typed with
    | n_wrap tx => cases mal with
      | n hx => exact unsignedSatComplete_n (ih child (by simp) _ _ tx wf hx nm)
  | thresh k children => exact remaining trivial _ _ typed wf mal nm nonzero zero unsigned

theorem completeB_from_remaining (fragment : CoreFragment)
    (remaining : ∀ sub, sizeOf sub ≤ sizeOf fragment → RemainingBSuccess sub → CompleteBRestIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub) : BSuccessCompleteIn sc fragment := by
  have ih : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub := by
    intro sub smaller
    exact completeB_from_remaining sub
      (fun inner bound isRemaining => remaining inner (Nat.le_trans bound (Nat.le_of_lt smaller)) isRemaining)
      (fun inner bound => df inner (Nat.lt_trans bound smaller))
  have bn : CompleteBnIn sc fragment := (completeBnV_from_B_residuals fragment (by
    intro sub smaller cm mm typed wf mal nm _nonzero _zero _unsigned
    exact ih sub smaller cm mm typed wf mal nm) df).1
  have rest : CompleteBRestIn sc fragment := by
    intro cm mm typed wf mal nm nonzero zero unsigned
    exact completeBRest_step typed wf mal nm nonzero zero unsigned ih df
      (remaining fragment (Nat.le_refl _))
  exact bSuccess_of_bn_rest bn rest
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.BRestComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrBComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat WBoolean ThresholdAlt
  ThresholdUnit SignedExchange BnVnComplete VRestComplete BRestComplete

def AmbientDsatCompleteWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = false → ¬ CheckedSignature fragment env flags own → dissatisfy fragment env = some own

abbrev AmbientDsatCompleteW := AmbientDsatCompleteWIn .tapscript

def SignedDsatCompleteBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.d = true → mm.e = true → mm.s = true → AmbientDsatCompleteIn sc fragment

abbrev SignedDsatCompleteB := SignedDsatCompleteBIn .tapscript

theorem typed_W_d_children {fragment : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) :
    (∃ child cx, fragment = .a child ∧ HasType sc child ⟨.B, cx⟩ ∧ cm.d = cx.d) ∨
    (∃ child cx, fragment = .s child ∧ HasType sc child ⟨.B, cx⟩ ∧ cx.o = true ∧ cm.d = cx.d) := by
  generalize typeEq : (⟨.W, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed <;> try { cases baseEq }
  case a_wrap tx => exact Or.inl ⟨_, _, rfl, tx, congrArg (fun ty : MiniType => ty.mods.d) typeEq⟩
  case s_wrap tx one => exact Or.inr ⟨_, _, rfl, tx, one, congrArg (fun ty : MiniType => ty.mods.d) typeEq⟩
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

theorem signedDsatW_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (e : mm.e = true) (signed : mm.s = true)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) : AmbientDsatCompleteWIn sc fragment := by
  rcases typed_W_d_children typed with ⟨child, cx, rfl, tx, deq⟩ | ⟨child, cx, rfl, tx, one, deq⟩
  · have cd : cx.d = true := deq.symm.trans d
    cases mal with
    | a hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm cd e signed
      intro parent env flags pa po own saved top rest order context nodup bounded run falsehood free
      have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact complete parent env flags pa po own top rest
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood free
  · have cd : cx.d = true := deq.symm.trans d
    cases mal with
    | s hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm cd e signed
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

theorem unsigned_W_run {fragment parent : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness} {saved top : StackElement}
    {rest : Stack} {order : BaseWOutputOrder}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContextIn sc parent fragment env flags pa po own)
    (bounded : ∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize)
    (run : Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) [])) (truth : castToBool top = true)
    (free : ¬ CheckedSignature fragment env flags own) : RawUnsigned (satisfactionCandidates fragment env).sat := by
  exact execution_without_checked_signature
    (ambientExecutionW_from_smaller_B typed wf mal nm (fun sub _ => uniform_B_execution sub)
      (fun sub _ => uniform_savedAltTransfer sub)
      parent env flags pa po own saved top rest order context bounded run truth) free

theorem or_b_select_left {sx dx sy dy : CandidateResult}
    (sat : RawUnsigned sx) (dsat : RawUnsigned dy) (other : sy.Signed) :
    ((sx.combine dy).select (dx.combine sy)).select (sx.combine sy).markOvercomplete = sx.combine dy := by
  rw [rawUnsigned_select_signed_eq (unsigned_combine sat dsat) other.combine_right]
  exact rawUnsigned_select_signed_eq (unsigned_combine sat dsat) other.combine_right.markOvercomplete

theorem or_b_select_right {sx dx sy dy : CandidateResult}
    (dsat : RawUnsigned dx) (sat : RawUnsigned sy) (other : sx.Signed) :
    ((sx.combine dy).select (dx.combine sy)).select (sx.combine sy).markOvercomplete = dx.combine sy := by
  rw [signed_select_rawUnsigned_eq other.combine_left (unsigned_combine dsat sat)]
  exact rawUnsigned_select_signed_eq (unsigned_combine dsat sat) other.combine_left.markOvercomplete

theorem signed_alternative_excludes_two_unsigned {left right : CandidateResult}
    (signed : left.Signed ∨ right.Signed) (rawLeft : RawUnsigned left) (rawRight : RawUnsigned right) : False := by
  rcases signed with leftSigned | rightSigned
  · exact signed_excludes_unsigned leftSigned rawLeft
  · exact signed_excludes_unsigned rightSigned rawRight

theorem completeB_or_b {X Y : CoreFragment} {cx cy : CorrectnessModifiers} {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (ex : mx.e = true) (ey : my.e = true) (signed : mx.s = true ∨ my.s = true)
    (ix : AmbientUnsignedSatCompleteBIn sc X) (iy : AmbientUnsignedSatCompleteWIn sc Y)
    (dx : mx.s = true → AmbientDsatCompleteIn sc X) (dy : my.s = true → AmbientDsatCompleteWIn sc Y) :
    AmbientUnsignedSatCompleteBIn sc (.or_b X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by, actual⟩ :=
    boolean_run_frame (isOr := true) tx ty wx wy run truth
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_right _ h
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have ccX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have ccY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have boundY : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact bx
    · exact all item (List.mem_append_right _ member)
  have absentX : ¬ CheckedSignature X env flags left := fun checked => free (checkedSignature_mono keysX inX checked)
  have absentY : ¬ CheckedSignature Y env flags right := fun checked => free (checkedSignature_mono keysY inY checked)
  have rawX := fun trueX => execution_without_checked_signature
    (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left x (right.toInitialStack ++ rest)
      ccX all runX trueX) absentX
  have rawY := fun trueY => unsigned_W_run ty wy hy ny ccY boundY runY trueY absentY
  have sx := (malleabilityCandidateSound env wx tx hx).signedSat
  have sy := (malleabilityCandidateSound env wy ty hy).signedSat
  have guard : (satisfactionCandidates X env).sat.Signed ∨ (satisfactionCandidates Y env).sat.Signed :=
    signed.elim (fun s => Or.inl (sx s)) (fun s => Or.inr (sy s))
  cases trueX : castToBool x with
  | false =>
    have trueY : castToBool y = true := by simpa [BooleanTruth, trueX] using actual
    have signedX : mx.s = true := by
      rcases signed with s | s
      · exact s
      · exact (signed_excludes_unsigned (sy s) (rawY trueY)).elim
    have selectedX := dx signedX parent env flags pa po left x (right.toInitialStack ++ rest) ccX
      (List.pairwise_append.mp nodup).1 all runX trueX absentX
    have selectedY := iy parent env flags pa po right x y rest order ccY
      (List.pairwise_append.mp nodup).2.1 boundY runY trueY absentY
    change ((((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).dsat).select
      ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)).select
      ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).markOvercomplete).usableWitness? = some (right ++ left)
    rw [or_b_select_right (expressive_rawUnsigned wx tx hx nx ex env) (rawY trueY) (sx signedX)]
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩
  | true =>
    cases trueY : castToBool y with
    | false =>
      have signedY : my.s = true := by
        rcases signed with s | s
        · exact (signed_excludes_unsigned (sx s) (rawX trueX)).elim
        · exact s
      have selectedX := ix parent env flags pa po left x (right.toInitialStack ++ rest) ccX
        (List.pairwise_append.mp nodup).1 all runX trueX absentX
      have selectedY := dy signedY parent env flags pa po right x y rest order ccY
        (List.pairwise_append.mp nodup).2.1 boundY runY trueY absentY
      change ((((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).dsat).select
        ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)).select
        ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat).markOvercomplete).usableWitness? = some (right ++ left)
      rw [or_b_select_left (rawX trueX) (expressive_rawUnsigned wy ty hy ny ey env) (sy signedY)]
      exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩
    | true => exact (signed_alternative_excludes_two_unsigned guard (rawX trueX) (rawY trueY)).elim

theorem completeB_or_b_parent {X Y : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_b X Y) ⟨.B, cm⟩) (wf : (CoreFragment.or_b X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_b X Y) mm) (nm : mm.nonMalleable = true)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_b X Y) → BSuccessCompleteIn sc sub)
    (ds : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_b X Y) → SignedDsatCompleteBIn sc sub) :
    AmbientUnsignedSatCompleteBIn sc (.or_b X Y) := by
  obtain ⟨cx, cy, mx, my, tx, dx, ty, dy, wx, wy, hx, hy, nx, ny, ex, ey, signed⟩ :=
    or_b_static typed wf mal nm
  exact completeB_or_b tx ty wx wy hx hy nx ny ex ey signed
    (ih X (by simp; omega) cx mx tx wx hx nx)
    (unsignedSatCompleteW_from_smaller_B ty wy hy ny ey (by
      intro sub smaller cz mz tz wz hz nz _ez
      exact ih sub (Nat.lt_trans smaller (by simp; omega)) cz mz tz wz hz nz))
    (fun signedX => ds X (by simp; omega) cx mx tx wx hx nx dx ex signedX)
    (fun signedY => signedDsatW_from_smaller_B ty wy hy ny dy ey signedY
      (fun sub smaller => ds sub (Nat.lt_trans smaller (by simp; omega))))

def RemainingBSuccessAfterOrB : CoreFragment → Prop
  | .or_d _ _ | .thresh _ _ => True
  | _ => False

theorem completeB_after_or_b (fragment : CoreFragment)
    (remaining : ∀ sub, sizeOf sub ≤ sizeOf fragment → RemainingBSuccessAfterOrB sub → CompleteBRestIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub)
    (ds : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) : BSuccessCompleteIn sc fragment := by
  have ih : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub := by
    intro sub smaller
    exact completeB_after_or_b sub
      (fun inner bound residual => remaining inner (Nat.le_trans bound (Nat.le_of_lt smaller)) residual)
      (fun inner bound => df inner (Nat.lt_trans bound smaller))
      (fun inner bound => ds inner (Nat.lt_trans bound smaller))
  apply completeB_from_remaining fragment _ df
  intro sub bound residual cm mm typed wf mal nm nonzero zero unsigned
  cases sub <;> simp only [RemainingBSuccess] at residual <;> try contradiction
  case or_b X Y =>
    exact completeB_or_b_parent typed wf mal nm
      (fun child smaller => ih child (Nat.lt_of_lt_of_le smaller bound))
      (fun child smaller => ds child (Nat.lt_of_lt_of_le smaller bound))
  case or_d X Y => exact remaining _ bound trivial cm mm typed wf mal nm nonzero zero unsigned
  case thresh k children => exact remaining _ bound trivial cm mm typed wf mal nm nonzero zero unsigned
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.OrBComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrDComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat BExecution ThresholdUnit
  SignedExchange BnVnComplete VRestComplete OrBComplete

def SmallerBIn (sc : ScriptContext) (X Y : CoreFragment) : Prop :=
  ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → BSuccessCompleteIn sc sub

abbrev SmallerB := SmallerBIn .tapscript

theorem or_d_static {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_d X Y) mm)
    (nm : mm.nonMalleable = true) :
    ∃ cx cy mx my,
      HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      mx.e = true ∧ (mx.s = true ∨ my.s = true) := by
  cases typed_B_shape typed with
  | or_d tx dx ux ty =>
    cases mal with
    | or_d hx hy =>
      obtain ⟨nx, ny, ex, signed⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      exact ⟨_, _, _, _, tx, dx, ux, ty, hx, hy, nx, ny, ex,
        Bool.or_eq_true_iff.mp signed⟩
  | remaining impossible => cases impossible

structure FallbackFrame (X Y : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (own : Witness) (top : StackElement) (rest : Stack) where
  left : Witness
  right : Witness
  value : StackElement
  split : own = right ++ left
  runLeft : Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest))
    [] flags env.txCtx (.success (value :: (right.toInitialStack ++ rest)) [])
  falseLeft : castToBool value = false
  runRight : Eval (compile Y) (right.toInitialStack ++ rest) [] flags env.txCtx
    (.success (top :: rest) [])

theorem or_d_run_cases {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (run : Eval (compile (.or_d X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    (∃ value, Eval (compile X) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (value :: rest) []) ∧ castToBool value = true) ∨
    Nonempty (FallbackFrame X Y env flags own top rest) := by
  cases typed_B_shape typed with
  | or_d tx _dx _ux ty =>
    rcases shortCircuit_run_frame (keep := true) tx ty wf.1 wf.2 run with h | h
    · exact Or.inl h
    · obtain ⟨left, right, value, split, runLeft, falseLeft, runRight⟩ := h
      exact Or.inr ⟨⟨left, right, value, split, runLeft, falseLeft, runRight⟩⟩
  | remaining impossible => cases impossible

theorem truthy_left_complete {X Y parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {value : StackElement} {rest : Stack}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_d X Y) mm)
    (nm : mm.nonMalleable = true) (ih : SmallerBIn sc X Y)
    (context : ExecutionContextIn sc parent (.or_d X Y) env flags pa po own)
    (nodup : (CoreFragment.or_d X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile X) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (value :: rest) [])) (truth : castToBool value = true)
    (free : ¬ CheckedSignature (.or_d X Y) env flags own) :
    satisfy (.or_d X Y) env = some own := by
  obtain ⟨cx, cy, mx, my, tx, _dx, _ux, ty, hx, hy, nx, ny, _ex, signed⟩ :=
    or_d_static typed mal nm
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_d X Y).keys :=
    fun _ h => List.mem_append_left _ h
  have contextX := executionContext_restrict context keysX
    (fun _ h => List.mem_append_left _ h) (fun _ h => h)
  have freeX : ¬ CheckedSignature X env flags own :=
    fun checked => free (checkedSignature_mono keysX (fun _ h => h) checked)
  have raw := execution_without_checked_signature
    (uniform_B_execution X cx mx tx wf.1 hx nx parent env flags pa po own value rest
      contextX bounded run truth) freeX
  have signedY : (satisfactionCandidates Y env).sat.Signed := by
    rcases signed with sx | sy
    · exact (signed_excludes_unsigned ((malleabilityCandidateSound env wf.1 tx hx).signedSat sx) raw).elim
    · exact (malleabilityCandidateSound env wf.2 ty hy).signedSat sy
  have selected := ih X (by simp; omega) cx mx tx wf.1 hx nx parent env flags pa po own
    value rest contextX (List.pairwise_append.mp nodup).1 bounded run truth freeX
  change ((satisfactionCandidates X env).sat.select
    ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)).usableWitness? = _
  rw [rawUnsigned_select_signed_eq raw signedY.combine_right]
  exact selected

theorem fallback_selection {X Y parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_d X Y) mm)
    (nm : mm.nonMalleable = true) (ih : SmallerBIn sc X Y)
    (context : ExecutionContextIn sc parent (.or_d X Y) env flags pa po own)
    (nodup : (CoreFragment.or_d X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (frame : FallbackFrame X Y env flags own top rest) (truth : castToBool top = true)
    (free : ¬ CheckedSignature (.or_d X Y) env flags own) :
    satisfy Y env = some frame.right ∧
    (satisfactionCandidates (.or_d X Y) env).sat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat ∧
    ∃ mx, HasMalleability sc X mx ∧ mx.nonMalleable = true ∧ mx.e = true ∧ mx.s = true := by
  obtain ⟨cx, cy, mx, my, tx, _dx, _ux, ty, hx, hy, nx, ny, ex, signed⟩ :=
    or_d_static typed mal nm
  have inY : ∀ item ∈ frame.right, item ∈ own := by
    intro item h; rw [frame.split]; exact List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys :=
    fun _ h => List.mem_append_right _ h
  have contextY := executionContext_restrict context keysY
    (fun _ h => List.mem_append_right _ h) inY
  have freeY : ¬ CheckedSignature Y env flags frame.right :=
    fun checked => free (checkedSignature_mono keysY inY checked)
  have bounds : ∀ item ∈ frame.left.toInitialStack ++ (frame.right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [frame.split, Witness.toInitialStack_append, List.append_assoc] using bounded
  have boundY := fun item h => bounds item (List.mem_append_right _ h)
  have rawY := execution_without_checked_signature
    (uniform_B_execution Y cy my ty wf.2 hy ny parent env flags pa po frame.right top rest
      contextY boundY frame.runRight truth) freeY
  have sx : mx.s = true := by
    rcases signed with sx | sy
    · exact sx
    · exact (signed_excludes_unsigned ((malleabilityCandidateSound env wf.2 ty hy).signedSat sy) rawY).elim
  have selectedY := ih Y (by simp; omega) cy my ty wf.2 hy ny parent env flags pa po
    frame.right top rest contextY (List.pairwise_append.mp nodup).2.1 boundY frame.runRight truth freeY
  refine ⟨selectedY, ?_, mx, hx, nx, ex, sx⟩
  exact signed_select_rawUnsigned_eq ((malleabilityCandidateSound env wf.1 tx hx).signedSat sx)
    (unsigned_combine (expressive_rawUnsigned wf.1 tx hx nx ex env) rawY)

theorem combine_projection_iff {left right : CandidateResult} {x y : Witness}
    (selectedY : right.usableWitness? = some y) :
    (left.combine right).usableWitness? = some (y ++ x) ↔ left.usableWitness? = some x := by
  constructor
  · intro selected
    obtain ⟨x', y', sx, sy, eq⟩ := CandidateResult.combine_usableWitness_iff.mp selected
    have yy : y' = y := Option.some.inj (sy.symm.trans selectedY)
    subst y'
    have xx : x' = x := List.append_cancel_left eq.symm
    simpa only [xx] using sx
  · intro selectedX
    exact CandidateResult.combine_usableWitness_iff.mpr ⟨x, y, selectedX, selectedY, rfl⟩

theorem fallback_exact_iff {X Y parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_d X Y) mm)
    (nm : mm.nonMalleable = true) (ih : SmallerBIn sc X Y)
    (context : ExecutionContextIn sc parent (.or_d X Y) env flags pa po own)
    (nodup : (CoreFragment.or_d X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (frame : FallbackFrame X Y env flags own top rest) (truth : castToBool top = true)
    (free : ¬ CheckedSignature (.or_d X Y) env flags own) :
    satisfy (.or_d X Y) env = some own ↔ dissatisfy X env = some frame.left := by
  obtain ⟨selectedY, selector, _⟩ := fallback_selection typed wf mal nm ih context nodup bounded frame truth free
  change (satisfactionCandidates (.or_d X Y) env).sat.usableWitness? = some own ↔ _
  rw [selector]
  simpa only [← frame.split, dissatisfy] using
    (combine_projection_iff (left := (satisfactionCandidates X env).dsat)
      (x := frame.left) selectedY)

theorem fallback_dsat_of_complete {X Y parent : CoreFragment}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (complete : AmbientDsatCompleteIn sc X)
    (context : ExecutionContextIn sc parent (.or_d X Y) env flags pa po own)
    (nodup : (CoreFragment.or_d X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (free : ¬ CheckedSignature (.or_d X Y) env flags own)
    (frame : FallbackFrame X Y env flags own top rest) :
    dissatisfy X env = some frame.left := by
  have inX : ∀ item ∈ frame.left, item ∈ own := by
    intro item h; rw [frame.split]; exact List.mem_append_right _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_d X Y).keys :=
    fun _ h => List.mem_append_left _ h
  have contextX := executionContext_restrict context keysX
    (fun _ h => List.mem_append_left _ h) inX
  have freeX : ¬ CheckedSignature X env flags frame.left :=
    fun checked => free (checkedSignature_mono keysX inX checked)
  have bounds : ∀ item ∈ frame.left.toInitialStack ++ (frame.right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [frame.split, Witness.toInitialStack_append, List.append_assoc] using bounded
  exact complete parent env flags pa po frame.left frame.value (frame.right.toInitialStack ++ rest)
    contextX (List.pairwise_append.mp nodup).1 bounds frame.runLeft frame.falseLeft freeX

theorem completeB_or_d_parent {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_d X Y) mm)
    (nm : mm.nonMalleable = true) (ih : SmallerBIn sc X Y)
    (falseX : BConditionFalseCompleteIn sc X ∨ SignedDsatCompleteBIn sc X) :
    AmbientUnsignedSatCompleteBIn sc (.or_d X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  rcases or_d_run_cases typed wf run with ⟨value, runX, truthX⟩ | fallback
  · exact truthy_left_complete typed wf mal nm ih context nodup bounded runX truthX free
  · obtain ⟨frame⟩ := fallback
    obtain ⟨_selectedY, _selection, mx, hx, nx, ex, sx⟩ :=
      fallback_selection typed wf mal nm ih context nodup bounded frame truth free
    obtain ⟨cx, _cy, _mx, _my, tx, dx, ux, _ty, _hx, _hy, _nx, _ny, _ex, _signed⟩ :=
      or_d_static typed mal nm
    have complete : AmbientDsatCompleteIn sc X := falseX.elim
      (fun df => df cx mx tx wf.1 hx nx dx ux ex)
      (fun ds => ds cx mx tx wf.1 hx nx dx ex sx)
    exact (fallback_exact_iff typed wf mal nm ih context nodup bounded frame truth free).mpr
      (fallback_dsat_of_complete complete context nodup bounded free frame)

theorem completeB_or_d_of_conditionFalse {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_d X Y) mm) (nm : mm.nonMalleable = true)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → BSuccessCompleteIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → BConditionFalseCompleteIn sc sub) :
    AmbientUnsignedSatCompleteBIn sc (.or_d X Y) :=
  completeB_or_d_parent typed wf mal nm ih (Or.inl (df X (by simp; omega)))

def RemainingBSuccessAfterOrD : CoreFragment → Prop
  | .thresh _ _ => True
  | _ => False

theorem completeB_after_or_d (fragment : CoreFragment)
    (remaining : ∀ sub, sizeOf sub ≤ sizeOf fragment → RemainingBSuccessAfterOrD sub → CompleteBRestIn sc sub)
    (df : ∀ sub, sizeOf sub < sizeOf fragment → BConditionFalseCompleteIn sc sub)
    (ds : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) : BSuccessCompleteIn sc fragment := by
  have ih : ∀ sub, sizeOf sub < sizeOf fragment → BSuccessCompleteIn sc sub := by
    intro sub smaller
    exact completeB_after_or_d sub
      (fun inner bound residual => remaining inner (Nat.le_trans bound (Nat.le_of_lt smaller)) residual)
      (fun inner bound => df inner (Nat.lt_trans bound smaller))
      (fun inner bound => ds inner (Nat.lt_trans bound smaller))
  apply completeB_after_or_b fragment _ df ds
  intro sub bound residual cm mm typed wf mal nm nonzero zero unsigned
  cases sub <;> simp only [RemainingBSuccessAfterOrB] at residual <;> try contradiction
  case or_d X Y =>
    exact completeB_or_d_of_conditionFalse typed wf mal nm
      (fun child smaller => ih child (Nat.lt_of_lt_of_le smaller bound))
      (fun child smaller => df child (Nat.lt_of_lt_of_le smaller bound))
  case thresh k children => exact remaining _ bound trivial cm mm typed wf mal nm nonzero zero unsigned
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.OrDComplete
