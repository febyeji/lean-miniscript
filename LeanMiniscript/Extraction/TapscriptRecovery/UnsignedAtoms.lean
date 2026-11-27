import LeanMiniscript.Extraction.TapscriptRecovery.ThresholdDissatisfaction

/-! Recover unsigned candidate witnesses for atoms and wrappers. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.ZeroComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat ForcedAndV SignedV BWrappers
  ThresholdRun ThresholdUnit DsatMaterial SignedExchange UnsignedComplete

theorem zero_threshold_shape {k : Nat} {children : List CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩) (zero : cm.z = true) :
    k = 1 ∧ ∃ child cx, children = [child] ∧ HasType sc child ⟨.B, cx⟩ ∧
      cx.z = true ∧ cx.d = true ∧ cx.u = true := by
  cases typed with
  | @thresh k child children cx types tx dx ux tails restTypes lower upper =>
    obtain ⟨zx, ztail⟩ := Bool.and_eq_true_iff.mp zero
    have empty : children = [] := by
      by_cases h : children = []
      · exact h
      · have noZero := (thresholdRestModifiers_noCount tails restTypes h).1
        rw [noZero] at ztail
        cases ztail
    subst children
    have count : k = 1 := by simpa using Nat.le_antisymm upper lower
    exact ⟨count, child, cx, rfl, tx, zx, dx, ux⟩

theorem zero_d_candidates {fragment : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (zero : cm.z = true) (d : cm.d = true) (env : SatEnv) :
    satisfactionCandidates fragment env = {sat := .impossible, dsat := .usable [] false} := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have z : ty.mods.z = true := by rw [← typeEq]; exact zero
  have dissat : ty.mods.d = true := by rw [← typeEq]; exact d
  cases typed <;> try { cases baseEq }
  case zero => rfl
  case one => cases dissat
  case older => cases dissat
  case after => cases dissat
  case sha256 => cases z
  case hash256 => cases z
  case hash160 => cases z
  case ripemd160 => cases z
  case and_v => cases dissat
  case and_b tx ty =>
    have noZero := (HasType.w_no_zo ty rfl).1
    exact (Bool.false_ne_true (noZero.symm.trans (Bool.and_eq_true_iff.mp z).2)).elim
  case or_b tx dx ty dy =>
    have noZero := (HasType.w_no_zo ty rfl).1
    exact (Bool.false_ne_true (noZero.symm.trans (Bool.and_eq_true_iff.mp z).2)).elim
  case or_d tx dx ux ty =>
    obtain ⟨zx, zy⟩ := Bool.and_eq_true_iff.mp z
    rw [satisfactionCandidates, zero_d_candidates tx wf.1 zx dx env,
      zero_d_candidates ty wf.2 zy dissat env]
    rfl
  case or_i => cases z
  case andor tx dx ux ty tz base same =>
    rename_i tyY tyZ
    cases tyY with
    | mk byy my =>
      change BaseType.B = byy at baseEq
      subst byy
      cases tyZ with
      | mk bzz mz =>
        change BaseType.B = bzz at same
        subst bzz
        obtain ⟨zxy, zz⟩ := Bool.and_eq_true_iff.mp z
        obtain ⟨zx, _zy⟩ := Bool.and_eq_true_iff.mp zxy
        rw [satisfactionCandidates, zero_d_candidates tx wf.1 zx dx env,
          zero_d_candidates tz wf.2.2.1 zz dissat env]
        rfl
  case c_wrap => cases z
  case d_wrap => cases z
  case j_wrap => cases z
  case n_wrap tx => exact zero_d_candidates tx wf z dissat env
  case multi => cases z
  case multi_a => cases z
  case thresh k child children cx types tx dx ux tails rt lower upper =>
    have parentType := HasType.thresh tx dx ux tails rt lower upper
    obtain ⟨rfl, selected, sx, eq, st, sz, sd, _⟩ := zero_threshold_shape parentType z
    have eqs := List.cons.inj eq
    cases eqs.1
    cases eqs.2
    have selectedZero := zero_d_candidates st wf.2.1.1 sz sd env
    simp only [satisfactionCandidates, if_pos (threshold_candidate_guard wf), satisfactionCandidatesList,
      selectedZero]
    rfl
termination_by sizeOf fragment

theorem zero_sat_candidates {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType sc fragment ty) (wf : fragment.WellFormed sc)
    (zero : ty.mods.z = true) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat = .impossible ∨
      (satisfactionCandidates fragment env).sat = .usable [] false := by
  cases typed with
  | zero => exact Or.inl rfl
  | one => exact Or.inr rfl
  | pk_k => cases zero
  | pk_h => cases zero
  | older n =>
    by_cases satisfied : sequenceSatisfied n env.txCtx
    · exact Or.inr (by simp [satisfactionCandidates, satisfied])
    · exact Or.inl (by simp [satisfactionCandidates, satisfied])
  | after n =>
    by_cases satisfied : locktimeSatisfied n env.txCtx
    · exact Or.inr (by simp [satisfactionCandidates, satisfied])
    · exact Or.inl (by simp [satisfactionCandidates, satisfied])
  | sha256 => cases zero
  | hash256 => cases zero
  | ripemd160 => cases zero
  | hash160 => cases zero
  | and_v tx ty _branch =>
    obtain ⟨zx, zy⟩ := Bool.and_eq_true_iff.mp zero
    have hx := zero_sat_candidates tx wf.1 zx env
    have hy := zero_sat_candidates ty wf.2.1 zy env
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals simp only [satisfactionCandidates, hx, hy]; first | exact Or.inl rfl | exact Or.inr rfl
  | and_b tx ty =>
    exact (Bool.false_ne_true ((HasType.w_no_zo ty rfl).1.symm.trans (Bool.and_eq_true_iff.mp zero).2)).elim
  | or_b tx _dx ty _dy =>
    exact (Bool.false_ne_true ((HasType.w_no_zo ty rfl).1.symm.trans (Bool.and_eq_true_iff.mp zero).2)).elim
  | or_c tx dx _ux ty =>
    obtain ⟨zx, zy⟩ := Bool.and_eq_true_iff.mp zero
    have hx := zero_d_candidates tx wf.1 zx dx env
    have hy := zero_sat_candidates ty wf.2 zy env
    rcases hy with hy | hy
    all_goals simp only [satisfactionCandidates, hx, hy]; first | exact Or.inl rfl | exact Or.inr rfl
  | or_d tx dx _ux ty =>
    obtain ⟨zx, zy⟩ := Bool.and_eq_true_iff.mp zero
    have hx := zero_d_candidates tx wf.1 zx dx env
    have hy := zero_sat_candidates ty wf.2 zy env
    rcases hy with hy | hy
    all_goals simp only [satisfactionCandidates, hx, hy]; first | exact Or.inl rfl | exact Or.inr rfl
  | or_i => cases zero
  | andor tx dx _ux _ty tz _base _same =>
    obtain ⟨zxy, zz⟩ := Bool.and_eq_true_iff.mp zero
    have hx := zero_d_candidates tx wf.1 (Bool.and_eq_true_iff.mp zxy).1 dx env
    have hz := zero_sat_candidates tz wf.2.2.1 zz env
    rcases hz with hz | hz
    all_goals
      simp only [satisfactionCandidates, hx, hz, CandidateResult.combine, CandidateResult.select]
      first | exact Or.inl rfl | exact Or.inr rfl
  | c_wrap => cases zero
  | v_wrap tx => exact zero_sat_candidates tx wf zero env
  | a_wrap => cases zero
  | s_wrap => cases zero
  | d_wrap => cases zero
  | j_wrap => cases zero
  | n_wrap tx => exact zero_sat_candidates tx wf zero env
  | multi => cases zero
  | multi_a => cases zero
  | @thresh k child children cx types tx dx ux tails rt lower upper =>
    have parentType := HasType.thresh tx dx ux tails rt lower upper
    obtain ⟨rfl, selected, sx, eq, st, sz, sd, _⟩ := zero_threshold_shape parentType zero
    have eqs := List.cons.inj eq
    cases eqs.1
    cases eqs.2
    have selectedZero := zero_d_candidates st wf.2.1.1 sz sd env
    simp only [satisfactionCandidates, if_pos (threshold_candidate_guard wf), satisfactionCandidatesList,
      selectedZero]
    exact Or.inl rfl
termination_by sizeOf fragment

theorem zero_usable_of_raw {fragment : CoreFragment} {ty : MiniType} {env : SatEnv}
    (typed : HasType sc fragment ty) (wf : fragment.WellFormed sc)
    (zero : ty.mods.z = true) (raw : RawUnsigned (satisfactionCandidates fragment env).sat) :
    satisfy fragment env = some [] := by
  rcases zero_sat_candidates typed wf zero env with impossible | usable
  · obtain ⟨candidate, eq, _⟩ := raw
    rw [impossible] at eq
    cases eq
  · simp [satisfy, usable, CandidateResult.usable, CandidateResult.usableWitness?]

def CompleteBzIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true → cm.z = true →
    AmbientUnsignedSatCompleteBIn sc fragment

abbrev CompleteBz := CompleteBzIn .tapscript

theorem uniform_completeBz (fragment : CoreFragment) : CompleteBzIn sc fragment := by
  intro cm mm typed wf mal nm zero parent env flags pa po own top rest context _nodup bounded run truth free
  have empty := zero_B_consumed typed wf zero run
  have raw := execution_without_checked_signature
    (uniform_B_execution fragment cm mm typed wf mal nm parent env flags pa po own top rest
      context bounded run truth) free
  simpa [empty] using zero_usable_of_raw typed wf zero raw

theorem uniform_completeVz (fragment : CoreFragment) : CompleteVzIn sc fragment := by
  intro cm mm typed wf mal nm zero parent env flags pa po own rest context _nodup bounded run free
  have empty := zero_V_consumed typed wf zero run
  have execute := ambientExecutionV_from_smaller_B typed wf mal nm (fun child _ => uniform_B_execution child)
  have raw := execution_without_checked_signature
    (execute parent env flags pa po own rest context bounded run) free
  simpa [empty] using zero_usable_of_raw typed wf zero raw

theorem complete_d_discharged {child : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.d child) ⟨.B, cm⟩) (wf : (CoreFragment.d child).WellFormed sc)
    (mal : HasMalleability sc (.d child) mm) (nm : mm.nonMalleable = true) :
    AmbientUnsignedSatCompleteBIn sc (.d child) := by
  obtain ⟨cx, mx, tx, zx, wx, hx, nx⟩ := d_static typed wf mal nm
  exact complete_d tx wx zx (uniform_completeVz child cx mx tx wx hx nx zx)

theorem zero_V_success_projection {fragment parent : CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags}
    {pa po own : Witness} {rest : Stack}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true) (zero : cm.z = true)
    (context : ExecutionContextIn sc parent fragment env flags pa po own)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) :
    own = [] ∧ satisfy fragment env = some [] := by
  have empty := zero_V_consumed typed wf zero run
  have free : ¬ CheckedSignature fragment env flags own := by
    intro ⟨sig, member, _⟩
    simp [empty] at member
  have execute := ambientExecutionV_from_smaller_B typed wf mal nm (fun child _ => uniform_B_execution child)
  have raw := execution_without_checked_signature
    (execute parent env flags pa po own rest context bounded run) free
  exact ⟨empty, zero_usable_of_raw typed wf zero raw⟩

theorem completeV_and_v {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.V, cx⟩) (ty : HasType sc Y ⟨.V, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (ix : AmbientUnsignedSatCompleteVIn sc X) (iy : AmbientUnsignedSatCompleteVIn sc Y) :
    AmbientUnsignedSatCompleteVIn sc (.and_v X Y) := by
  intro parent env flags pa po own rest context nodup bounded run free
  obtain ⟨left, right, eq, runX, runY⟩ := and_v_run_V_frame tx ty wx wy run
  subst own
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_right _ h
  have contextX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have selectedX := ix parent env flags pa po left (right.toInitialStack ++ rest) contextX
    (List.pairwise_append.mp nodup).1 boundAll runX
    (fun checked => free (checkedSignature_mono keysX inX checked))
  have selectedY := iy parent env flags pa po right rest contextY (List.pairwise_append.mp nodup).2.1
    (fun item member => boundAll item (List.mem_append_right _ member)) runY
    (fun checked => free (checkedSignature_mono keysY inY checked))
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, selectedX, selectedY, rfl⟩

end LeanMiniscript.Extraction.TapscriptRecovery.ZeroComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.NFComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat WBoolean SignedExchange
  UnsignedComplete ZeroComplete

theorem typed_W_n_false {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType sc fragment ty) (base : ty.base = .W) : ty.mods.n = false := by
  cases typed <;> simp_all [branchBase]

theorem completeB_and_v {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.V, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (ix : AmbientUnsignedSatCompleteVIn sc X) (iy : AmbientUnsignedSatCompleteBIn sc Y) :
    AmbientUnsignedSatCompleteBIn sc (.and_v X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  obtain ⟨left, right, eq, runX, runY⟩ := and_v_run_B_frame tx ty wx wy run
  subst own
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_right _ h
  have cx := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have cy := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have sx := ix parent env flags pa po left (right.toInitialStack ++ rest) cx
    (List.pairwise_append.mp nodup).1 all runX (fun checked => free (checkedSignature_mono keysX inX checked))
  have sy := iy parent env flags pa po right top rest cy (List.pairwise_append.mp nodup).2.1
    (fun item h => all item (List.mem_append_right _ h)) runY truth
    (fun checked => free (checkedSignature_mono keysY inY checked))
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, sx, sy, rfl⟩

theorem completeB_and_b {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (ix : AmbientUnsignedSatCompleteBIn sc X) (iy : AmbientUnsignedSatCompleteWIn sc Y) :
    AmbientUnsignedSatCompleteBIn sc (.and_b X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by, actual⟩ :=
    boolean_run_frame (isOr := false) tx ty wx wy run truth
  subst own
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_b X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_b X Y).keys := fun _ h => List.mem_append_right _ h
  have cx := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have cy := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have boundY : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    intro item h
    rcases List.mem_cons.mp h with rfl | h
    · exact bx
    · exact all item (List.mem_append_right _ h)
  have sx := ix parent env flags pa po left x (right.toInitialStack ++ rest) cx
    (List.pairwise_append.mp nodup).1 all runX actual.1
    (fun checked => free (checkedSignature_mono keysX inX checked))
  have sy := iy parent env flags pa po right x y rest order cy (List.pairwise_append.mp nodup).2.1
    boundY runY actual.2 (fun checked => free (checkedSignature_mono keysY inY checked))
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, sx, sy, rfl⟩

def CompleteVnIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.V, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true → cm.n = true → mm.s = false →
    AmbientUnsignedSatCompleteVIn sc fragment

abbrev CompleteVn := CompleteVnIn .tapscript

theorem completeB_split {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (nf : cm.n = true → AmbientUnsignedSatCompleteBIn sc fragment)
    (remaining : cm.n = false → cm.z = false → mm.s = false → AmbientUnsignedSatCompleteBIn sc fragment) :
    AmbientUnsignedSatCompleteBIn sc fragment := by
  by_cases signed : mm.s = true
  · exact complete_of_signed typed wf mal nm signed
  · have unsigned : mm.s = false := by cases flag : mm.s <;> simp_all
    cases nonzero : cm.n with
    | true => exact nf nonzero
    | false =>
      cases zero : cm.z with
      | true => exact uniform_completeBz fragment cm mm typed wf mal nm zero
      | false => exact remaining nonzero zero unsigned

end LeanMiniscript.Extraction.TapscriptRecovery.NFComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.BnVnComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI WBoolean ThresholdAlt SignedExchange
  UnsignedComplete ZeroComplete NFComplete

def CompleteBnIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true → cm.n = true → mm.s = false →
    AmbientUnsignedSatCompleteBIn sc fragment

abbrev CompleteBn := CompleteBnIn .tapscript

def CompleteBRestIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.n = false → cm.z = false → mm.s = false → AmbientUnsignedSatCompleteBIn sc fragment

abbrev CompleteBRest := CompleteBRestIn .tapscript

inductive UnsignedBnShape : CoreFragment → Prop where
  | sha256 (h : Hash256) : UnsignedBnShape (.sha256 h)
  | hash256 (h : Hash256) : UnsignedBnShape (.hash256 h)
  | ripemd160 (h : Hash160) : UnsignedBnShape (.ripemd160 h)
  | hash160 (h : Hash160) : UnsignedBnShape (.hash160 h)
  | and_v (X Y : CoreFragment) : UnsignedBnShape (.and_v X Y)
  | and_b (X Y : CoreFragment) : UnsignedBnShape (.and_b X Y)
  | d (X : CoreFragment) : UnsignedBnShape (.d X)
  | j (X : CoreFragment) : UnsignedBnShape (.j X)
  | n (X : CoreFragment) : UnsignedBnShape (.n X)

theorem bn_unsigned_shape {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm)
    (nonzero : cm.n = true) (unsigned : mm.s = false) : UnsignedBnShape fragment := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have n : ty.mods.n = true := by rw [← typeEq]; exact nonzero
  cases typed <;> try { cases baseEq }
  case zero => cases n
  case one => cases n
  case older => cases n
  case after => cases n
  case sha256 => exact .sha256 _
  case hash256 => exact .hash256 _
  case ripemd160 => exact .ripemd160 _
  case hash160 => exact .hash160 _
  case and_v => exact .and_v _ _
  case and_b => exact .and_b _ _
  case or_b => cases n
  case or_d => cases n
  case or_i => cases n
  case andor => cases n
  case c_wrap => cases mal; cases unsigned
  case d_wrap => exact .d _
  case j_wrap => exact .j _
  case n_wrap => exact .n _
  case thresh => cases n
  case multi => cases mal; cases unsigned
  case multi_a => cases n

theorem and_v_n_static {X Y : CoreFragment} {base : BaseType}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.and_v X Y) ⟨base, cm⟩)
    (wf : (CoreFragment.and_v X Y).WellFormed sc)
    (mal : HasMalleability sc (.and_v X Y) mm) (nm : mm.nonMalleable = true)
    (nonzero : cm.n = true) (unsigned : mm.s = false) :
    ∃ cx cy mx my, HasType sc X ⟨.V, cx⟩ ∧ HasType sc Y ⟨base, cy⟩ ∧
      X.WellFormed sc ∧ Y.WellFormed sc ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.s = false ∧ my.s = false ∧
      (cx.n = true ∨ cx.z = true ∧ cy.n = true) := by
  generalize typeEq : (⟨base, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  cases typed with
  | and_v tx ty _branch =>
    rename_i cx tyY
    cases tyY with
    | mk actual cy =>
      change base = actual at baseEq
      subst actual
      have n : (cx.n || (cx.z && cy.n)) = true :=
        (congrArg (fun t : MiniType => t.mods.n) typeEq).symm.trans nonzero
      cases mal with
      | and_v hx hy =>
        obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
        obtain ⟨sx, sy⟩ := Bool.or_eq_false_iff.mp unsigned
        exact ⟨cx, cy, _, _, tx, ty, wf.1, wf.2.1, hx, hy, nx, ny, sx, sy,
          by simpa only [Bool.or_eq_true, Bool.and_eq_true] using n⟩

theorem and_b_n_static {X Y : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.and_b X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.and_b X Y).WellFormed sc)
    (mal : HasMalleability sc (.and_b X Y) mm) (nm : mm.nonMalleable = true)
    (nonzero : cm.n = true) (unsigned : mm.s = false) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ HasType sc Y ⟨.W, cy⟩ ∧
      X.WellFormed sc ∧ Y.WellFormed sc ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.s = false ∧ my.s = false ∧ cx.n = true := by
  cases typed with
  | and_b tx ty =>
    have yn := typed_W_n_false ty rfl
    have xn : _ = true := nonzero
    simp only at yn
    simp only [yn, Bool.and_false, Bool.or_false] at xn
    cases mal with
    | and_b hx hy =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      obtain ⟨sx, sy⟩ := Bool.or_eq_false_iff.mp unsigned
      exact ⟨_, _, _, _, tx, ty, wf.1, wf.2.1, hx, hy, nx, ny, sx, sy, xn⟩

theorem completeW_unsigned {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true) (unsigned : mm.s = false)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → ∀ cx mx,
      HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → mx.s = false →
      AmbientUnsignedSatCompleteBIn sc sub) : AmbientUnsignedSatCompleteWIn sc fragment := by
  cases typed_W_shape typed with
  | @a child cx tx =>
    cases mal with
    | a hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm unsigned
      intro parent env flags pa po own saved top rest order context nodup bounded run truth free
      have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact complete parent env flags pa po own top rest
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun truth free
  | @s child cx tx one =>
    cases mal with
    | s hx =>
      have complete := ih child (by simp) cx _ tx wf hx nm unsigned
      intro parent env flags pa po own saved top rest order context nodup bounded run truth free
      obtain ⟨_, childRun⟩ := s_run_child tx one wf run
      apply complete parent env flags pa po own top (saved :: rest)
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup _ childRun truth free
      intro item member
      apply bounded item
      simp only [List.mem_cons, List.mem_append] at member ⊢
      rcases member with member | rfl | member
      · exact Or.inr (Or.inl member)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr member)

theorem completeBn_step {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (nonzero : cm.n = true) (unsigned : mm.s = false)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → CompleteBnIn sc sub ∧ CompleteVnIn sc sub)
    (br : ∀ sub, sizeOf sub < sizeOf fragment → CompleteBRestIn sc sub) :
    AmbientUnsignedSatCompleteBIn sc fragment := by
  have childB : ∀ sub, sizeOf sub < sizeOf fragment → ∀ cx mx,
      HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → mx.s = false →
      AmbientUnsignedSatCompleteBIn sc sub := by
    intro sub smaller cx mx tx wx hx nx sx
    exact completeB_split tx wx hx nx
      (fun nn => (ih sub smaller).1 cx mx tx wx hx nx nn sx)
      (fun nn zz ss => br sub smaller cx mx tx wx hx nx nn zz ss)
  cases bn_unsigned_shape typed wf mal nonzero unsigned with
  | sha256 h => exact complete_sha256 h
  | hash256 h => exact complete_hash256 h
  | ripemd160 h => exact complete_ripemd160 h
  | hash160 h => exact complete_hash160 h
  | and_v X Y =>
    obtain ⟨cx, cy, mx, my, tx, ty, wx, wy, hx, hy, nx, ny, sx, sy, counts⟩ :=
      and_v_n_static typed wf mal nm nonzero unsigned
    apply completeB_and_v tx ty wx wy
    · rcases counts with xn | ⟨xz, _yn⟩
      · exact (ih X (by simp; omega)).2 cx mx tx wx hx nx xn sx
      · exact uniform_completeVz X cx mx tx wx hx nx xz
    · exact childB Y (by simp; omega) cy my ty wy hy ny sy
  | and_b X Y =>
    obtain ⟨cx, cy, mx, my, tx, ty, wx, wy, hx, hy, nx, ny, sx, sy, xn⟩ :=
      and_b_n_static typed wf mal nm nonzero unsigned
    exact completeB_and_b tx ty wx wy
      ((ih X (by simp; omega)).1 cx mx tx wx hx nx xn sx)
      (completeW_unsigned ty wy hy ny sy
        (fun sub smaller => childB sub (Nat.lt_trans smaller (by simp; omega))))
  | d child => exact complete_d_discharged typed wf mal nm
  | j child =>
    cases typed with
    | j_wrap tx nn => cases mal with
      | j hx => exact unsignedSatComplete_j ((ih child (by simp)).1 _ _ tx wf hx nm nn unsigned)
  | n child =>
    cases typed with
    | n_wrap tx => cases mal with
      | n hx => exact unsignedSatComplete_n ((ih child (by simp)).1 _ _ tx wf hx nm nonzero unsigned)

end LeanMiniscript.Extraction.TapscriptRecovery.BnVnComplete
