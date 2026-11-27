import LeanMiniscript.Extraction.TapscriptRecovery.ForcedDissatisfaction

/-! Close the unsigned false and true execution classifications by size induction. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.NonunitZero

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat OrBComplete UnsignedFalse
  OrBFalse AndorUnsignedFalse ForcedLinked

def NonunitShape : CoreFragment → Prop
  | .d _ | .or_d _ _ | .or_i _ _ | .andor _ _ _ | .j _ => True
  | _ => False

theorem nonunit_shape {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (mal : HasMalleability sc fragment mm)
    (u : cm.u = false) (e : mm.e = true) (s : mm.s = false) : NonunitShape fragment := by
  cases unsigned_false_shape typed mal e s <;> try trivial
  · cases typed; cases u
  · cases typed; cases u

theorem decodedZero_or_d {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (completeX : AmbientDsatCompleteIn sc X) (completeY : DecodedZeroDsatCompleteIn sc Y) :
    DecodedZeroDsatCompleteIn sc (.or_d X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run zero free
  obtain ⟨left, right, value, eq, runX, falseX, runY⟩ :=
    or_d_false_run_frame tx ty wx wy run (decoded_zero_false zero)
  subst own
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_right _ h
  have contextX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have dx := completeX parent env flags pa po left value (right.toInitialStack ++ rest)
    contextX (List.pairwise_append.mp nodup).1 bounds runX falseX
    (fun checked => free (checkedSignature_mono keysX inX checked))
  have dy := completeY parent env flags pa po right top rest
    contextY (List.pairwise_append.mp nodup).2.1
    (fun item h => bounds item (List.mem_append_right _ h)) runY zero
    (fun checked => free (checkedSignature_mono keysY inY checked))
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, dx, dy, rfl⟩

theorem or_d_nonunit_guards {X Y : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_d X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_d X Y) mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (u : cm.u = false) (e : mm.e = true) (s : mm.s = false) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧ cy.d = true ∧ cy.u = false ∧
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

theorem nonunit_or_d (X Y : CoreFragment)
    (unit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → UnsignedFalseIn sc sub)
    (nonunit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → UnsignedNonunitZeroIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_d X Y) → SignedDsatCompleteBIn sc sub) :
    UnsignedNonunitZeroIn sc (.or_d X Y) := by
  intro cm mm typed wf mal nm d u e s
  obtain ⟨cx, cy, mx, my, tx, dx, ux, ty, dy, uy, hx, hy, nx, ny, ex, ey, split⟩ :=
    or_d_nonunit_guards typed mal nm d u e s
  apply decodedZero_or_d tx ty wf.1 wf.2
  · exact conditionFalse_of_unsigned_signed (unit X (by simp; omega)) (signed X (by simp; omega))
      cx mx tx wf.1 hx nx dx ux ex
  · rcases split with ⟨_sx, sy⟩ | ⟨_sx, sy⟩
    · exact nonunit Y (by simp; omega) cy my ty wf.2 hy ny dy uy ey sy
    · exact decodedZero_of_ambient (signed Y (by simp; omega) cy my ty wf.2 hy ny dy ey sy)

theorem nonunit_j (X : CoreFragment) : UnsignedNonunitZeroIn sc (.j X) := by
  intro cm mm typed wf mal nm _d _u e _s
  cases typed with
  | j_wrap tx _nonzero =>
    cases mal with
    | j hx =>
      exact decodedZero_of_ambient (ambientDsatComplete_j
        (ambientForcedFalse_of_typed tx wf hx nm e)
        (fun env => (malleabilityCandidateSound env (show X.WellFormed sc from wf) tx hx).forcedDsat e))

theorem andor_d_guards {X Y Z : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, cm⟩) (d : cm.d = true) :
    ∃ cx cy cz, HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧ HasType sc Z ⟨.B, cz⟩ ∧
      cz.d = true ∧ cm.u = (cy.u && cz.u) := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have pd : ty.mods.d = true := by rw [← typeEq]; exact d
  have pu : cm.u = ty.mods.u := congrArg (fun t : MiniType => t.mods.u) typeEq
  cases typed with
  | andor tx dx ux ty tz branch same =>
    rename_i tyY tyZ
    cases tyY with
    | mk byy cy =>
      change BaseType.B = byy at baseEq
      subst byy
      cases tyZ with
      | mk bzz cz =>
        change BaseType.B = bzz at same
        subst bzz
        exact ⟨_, cy, cz, tx, dx, ux, ty, tz, pd, pu⟩

theorem decodedZero_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (selector : ∀ env, (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat)
    (completeX : AmbientDsatCompleteIn sc X) (completeZ : DecodedZeroDsatCompleteIn sc Z)
    (exclude : mx.s = true ∨ AmbientForcedFalseIn sc Y) : DecodedZeroDsatCompleteIn sc (.andor X Y Z) := by
  intro parent env flags pa po own resultTop rest context nodup bounded run zero free
  obtain ⟨left, right, top, eq, runX, falseX, runZ⟩ :=
    andor_false_active tx ty tz wx wy wz hx nx exclude context nodup bounded run (decoded_zero_false zero) free
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys := fun _ h => List.mem_append_right _ h
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
  have ndX := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).1
  have ndZ := (List.pairwise_append.mp nodup).2.1
  have dx := completeX parent env flags pa po left top (right.toInitialStack ++ rest)
    ccX ndX all runX falseX absentX
  have dz := completeZ parent env flags pa po right resultTop rest ccZ ndZ boundZ runZ zero absentZ
  change (satisfactionCandidates (.andor X Y Z) env).dsat.usableWitness? = _
  rw [selector env]
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, dx, dz, rfl⟩

theorem nonunit_andor (X Y Z : CoreFragment)
    (unit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → UnsignedFalseIn sc sub)
    (nonunit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → UnsignedNonunitZeroIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → SignedDsatCompleteBIn sc sub) :
    UnsignedNonunitZeroIn sc (.andor X Y Z) := by
  intro cm mm typed wf mal nm d _u e _s
  obtain ⟨cx, cy, cz, tx, dx, ux, ty, tz, dz, _uEq⟩ := andor_d_guards typed d
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex, ez, route⟩ := andor_expressive_guards mal nm e
  apply decodedZero_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx
    (andor_dsat_selector_expressive typed wf mal nm e)
  · exact conditionFalse_of_unsigned_signed (unit X (by simp; omega)) (signed X (by simp; omega))
      cx mx tx wf.1 hx nx dx ux ex
  · exact decodedZeroB_of_families tz wf.2.2.1 hz nz dz ez
      (unit Z (by simp; omega)) (nonunit Z (by simp; omega)) (signed Z (by simp; omega))
  · exact route.elim Or.inl (fun f => Or.inr (ambientForcedFalse_of_typed ty wf.2.1 hy ny f))

end LeanMiniscript.Extraction.TapscriptRecovery.NonunitZero

namespace LeanMiniscript.Extraction.TapscriptRecovery.FalseUniform

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat OrBComplete UnsignedFalse
  OrBFalse ForcedLinked NonunitZero UnsignedOrI SignedDsat
  VRestComplete

theorem or_i_nonunit_guards {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_i X Y) mm)
    (nm : mm.nonMalleable = true) (u : cm.u = false) (e : mm.e = true) (s : mm.s = false) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ HasType sc Y ⟨.B, cy⟩ ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ (cx.u && cy.u) = false ∧
      ((mx.s = true ∧ my.s = false) ∨ (mx.s = false ∧ my.s = true)) ∧
      ((cx.d = true ∧ mx.e = true ∧ my.f = true) ∨
        (cy.d = true ∧ my.e = true ∧ mx.f = true)) := by
  generalize eq : (⟨.B, cm⟩ : MiniType) = parentType at typed
  cases typed with
  | @or_i X Y tyX tyY tx ty _branch sameBase =>
    have baseEq := congrArg MiniType.base eq
    cases tyX with
    | mk baseX cx =>
      change BaseType.B = baseX at baseEq
      subst baseX
      cases tyY with
      | mk baseY cy =>
        change BaseType.B = baseY at sameBase
        subst baseY
        have units : (cx.u && cy.u) = false :=
          (congrArg (fun t : MiniType => t.mods.u) eq).symm.trans u
        cases mal with
        | @or_i X Y mx my hx hy =>
          obtain ⟨nx, ny, atLeastOne⟩ := (boolAnd3_eq_true _ _ _).mp nm
          have signedness : (mx.s = true ∧ my.s = false) ∨ (mx.s = false ∧ my.s = true) := by
            cases sx : mx.s <;> cases sy : my.s <;> simp_all
          refine ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, units, signedness, ?_⟩
          rcases Bool.or_eq_true_iff.mp e with left | right
          · obtain ⟨ex, fy⟩ := Bool.and_eq_true_iff.mp left
            exact Or.inl ⟨OrIDsat.expressive_implies_d tx hx ex, ex, fy⟩
          · obtain ⟨ey, fx⟩ := Bool.and_eq_true_iff.mp right
            exact Or.inr ⟨OrIDsat.expressive_implies_d ty hy ey, ey, fx⟩

theorem or_i_decoded_children {X Y parent : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness} {value : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (context : ExecutionContextIn sc parent (.or_i X Y) env flags pa po own)
    (nodup : (CoreFragment.or_i X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.or_i X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (value :: rest) []))
    (zero : decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int))
    (free : ¬ CheckedSignature (.or_i X Y) env flags own) :
    (∃ active, own = active ++ [trueElement] ∧
      ExecutionContextIn sc parent X env flags pa po active ∧ X.keys.Nodup ∧
      (∀ item ∈ active.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) ∧
      Eval (compile X) (active.toInitialStack ++ rest) [] flags env.txCtx (.success (value :: rest) []) ∧
      decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      ¬ CheckedSignature X env flags active) ∨
    (∃ active, own = active ++ [falseElement] ∧
      ExecutionContextIn sc parent Y env flags pa po active ∧ Y.keys.Nodup ∧
      (∀ item ∈ active.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) ∧
      Eval (compile Y) (active.toInitialStack ++ rest) [] flags env.txCtx (.success (value :: rest) []) ∧
      decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      ¬ CheckedSignature Y env flags active) := by
  rcases or_i_false_children tx ty wx wy context nodup bounded run (decoded_zero_false zero) free with
    ⟨active, eq, ctx, nd, bound, childRun, _false, absent⟩ |
    ⟨active, eq, ctx, nd, bound, childRun, _false, absent⟩
  · exact Or.inl ⟨active, eq, ctx, nd, bound, childRun, zero, absent⟩
  · exact Or.inr ⟨active, eq, ctx, nd, bound, childRun, zero, absent⟩

theorem or_i_left_decoded_complete {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (raw : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat)
    (signed : ∀ env, (satisfactionCandidates Y env).dsat.Signed)
    (completeX : DecodedZeroDsatCompleteIn sc X) (forcedY : AmbientForcedFalseIn sc Y) :
    DecodedZeroDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po own value rest context nodup bounded run zero free
  rcases or_i_decoded_children tx ty wx wy context nodup bounded run zero free with
    ⟨active, eq, ctx, nd, bound, childRun, childZero, absent⟩ |
    ⟨active, _eq, ctx, nd, bound, childRun, childZero, absent⟩
  · exact (or_i_left_usable_iff (raw env) (signed env)).mpr
      ⟨active, completeX parent env flags pa po active value rest ctx nd bound childRun childZero absent, eq⟩
  · exact (absent (forcedY parent env flags pa po active value rest ctx nd bound childRun
      (decoded_zero_false childZero))).elim

theorem or_i_right_decoded_complete {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (signed : ∀ env, (satisfactionCandidates X env).dsat.Signed)
    (raw : ∀ env, RawUnsigned (satisfactionCandidates Y env).dsat)
    (forcedX : AmbientForcedFalseIn sc X) (completeY : DecodedZeroDsatCompleteIn sc Y) :
    DecodedZeroDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po own value rest context nodup bounded run zero free
  rcases or_i_decoded_children tx ty wx wy context nodup bounded run zero free with
    ⟨active, _eq, ctx, nd, bound, childRun, childZero, absent⟩ |
    ⟨active, eq, ctx, nd, bound, childRun, childZero, absent⟩
  · exact (absent (forcedX parent env flags pa po active value rest ctx nd bound childRun
      (decoded_zero_false childZero))).elim
  · exact (or_i_right_usable_iff (signed env) (raw env)).mpr
      ⟨active, completeY parent env flags pa po active value rest ctx nd bound childRun childZero absent, eq⟩

theorem nonunit_or_i (X Y : CoreFragment)
    (unit : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → UnsignedFalse.UnsignedFalseIn sc child)
    (nonunit : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → UnsignedNonunitZeroIn sc child)
    (signed : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedDsatCompleteBIn sc child) :
    UnsignedNonunitZeroIn sc (.or_i X Y) := by
  intro cm mm typed wf mal nm _d u e s
  obtain ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, _units, _signedness, choice⟩ :=
    or_i_nonunit_guards typed mal nm u e s
  rcases choice with ⟨dx, ex, fy⟩ | ⟨dy, ey, fx⟩
  · exact or_i_left_decoded_complete tx ty wf.1 wf.2
      (expressive_rawUnsigned wf.1 tx hx nx ex)
      (fun env => (malleabilityCandidateSound env wf.2 ty hy).forcedDsat fy)
      (decodedZeroB_of_families tx wf.1 hx nx dx ex
        (unit X (by simp; omega)) (nonunit X (by simp; omega)) (signed X (by simp; omega)))
      (ambientForcedFalse_of_typed ty wf.2 hy ny fy)
  · exact or_i_right_decoded_complete tx ty wf.1 wf.2
      (fun env => (malleabilityCandidateSound env wf.1 tx hx).forcedDsat fx)
      (expressive_rawUnsigned wf.2 ty hy ny ey)
      (ambientForcedFalse_of_typed tx wf.1 hx nx fx)
      (decodedZeroB_of_families ty wf.2 hy ny dy ey
        (unit Y (by simp; omega)) (nonunit Y (by simp; omega)) (signed Y (by simp; omega)))

theorem nonunit_step_closed (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    UnsignedNonunitZeroIn sc fragment := by
  have children : ∀ child, sizeOf child < sizeOf fragment →
      SignedDsatBIn sc child ∧ UnsignedFalse.UnsignedFalseIn sc child := by
    intro child smaller
    exact ForcedAdapter.falseFamilies_from_nonunit child
      (fun inner bound => ih inner (Nat.lt_trans bound smaller))
  have unit : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalse.UnsignedFalseIn sc child :=
    fun child smaller => (children child smaller).2
  have signed : ∀ child, sizeOf child < sizeOf fragment → SignedDsatCompleteBIn sc child :=
    fun child smaller => (children child smaller).1
  intro cm mm typed wf mal nm d u e s
  have shape := nonunit_shape typed mal u e s
  cases fragment <;> try { exact False.elim shape }
  case d X =>
    cases typed with
    | d_wrap tx zero =>
      intro parent env flags pa po own top rest context _nodup _bound run decoded _free
      rw [SignedDsat.d_false_witness tx wf zero context.rules run (decoded_zero_false decoded)]
      rfl
  case or_d X Y => exact nonunit_or_d X Y unit ih signed cm mm typed wf mal nm d u e s
  case or_i X Y => exact nonunit_or_i X Y unit ih signed cm mm typed wf mal nm d u e s
  case andor X Y Z => exact nonunit_andor X Y Z unit ih signed cm mm typed wf mal nm d u e s
  case j X => exact nonunit_j X cm mm typed wf mal nm d u e s

theorem uniform_nonunit (fragment : CoreFragment) : UnsignedNonunitZeroIn sc fragment :=
  nonunit_step_closed fragment (fun child _smaller => uniform_nonunit child)
termination_by sizeOf fragment

theorem uniform_falseFamilies (fragment : CoreFragment) :
    SignedDsatBIn sc fragment ∧ UnsignedFalse.UnsignedFalseIn sc fragment :=
  ForcedAdapter.falseFamilies_from_nonunit fragment (fun child _smaller => uniform_nonunit child)

theorem uniform_signedDsatB (fragment : CoreFragment) : SignedDsatBIn sc fragment :=
  (uniform_falseFamilies fragment).1

theorem uniform_unsignedFalse (fragment : CoreFragment) : UnsignedFalse.UnsignedFalseIn sc fragment :=
  (uniform_falseFamilies fragment).2

theorem uniform_signedDsatCompleteB (fragment : CoreFragment) : SignedDsatCompleteBIn sc fragment :=
  uniform_signedDsatB fragment

theorem uniform_conditionFalseComplete (fragment : CoreFragment) : BConditionFalseCompleteIn sc fragment :=
  ForcedAdapter.conditionFalse_from_nonunit fragment (fun child _smaller => uniform_nonunit child)

theorem decodedZero_complete_of_typed {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc fragment ⟨.B, cm⟩)
    (wf : fragment.WellFormed sc) (mal : HasMalleability sc fragment mm)
    (nm : mm.nonMalleable = true) (d : cm.d = true) (e : mm.e = true) :
    DecodedZeroDsatCompleteIn sc fragment :=
  decodedZeroB_of_families typed wf mal nm d e
    (uniform_unsignedFalse fragment) (uniform_nonunit fragment) (uniform_signedDsatCompleteB fragment)

end LeanMiniscript.Extraction.TapscriptRecovery.FalseUniform

namespace LeanMiniscript.Extraction.TapscriptRecovery.SuccessUniform

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI SignedExchange VRestComplete ThreshComplete
  FalseUniform

theorem uniform_BSuccessComplete (fragment : CoreFragment) : BSuccessCompleteIn sc fragment :=
  completeB_from_false_families fragment
    (fun child _smaller => uniform_conditionFalseComplete child)
    (fun child _smaller => uniform_signedDsatCompleteB child)

theorem uniform_VSuccessComplete (fragment : CoreFragment) : VSuccessCompleteIn sc fragment := by
  intro cm mm typed wf mal nm
  exact completeV_from_false_families typed wf mal nm
    (fun child _smaller => uniform_conditionFalseComplete child)
    (fun child _smaller => uniform_signedDsatCompleteB child)

theorem actual_unsigned_B_satisfy {fragment parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContextIn sc parent fragment env flags pa po own) (nodup : fragment.keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) (free : ¬ CheckedSignature fragment env flags own) :
    satisfy fragment env = some own :=
  uniform_BSuccessComplete fragment cm mm typed wf mal nm parent env flags pa po own top rest
    context nodup bounded run truth free

theorem actual_unsigned_V_satisfy {fragment parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {rest : Stack}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContextIn sc parent fragment env flags pa po own) (nodup : fragment.keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest []))
    (free : ¬ CheckedSignature fragment env flags own) : satisfy fragment env = some own :=
  uniform_VSuccessComplete fragment cm mm typed wf mal nm parent env flags pa po own rest
    context nodup bounded run free

theorem rowCompleteW_of_typed {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc fragment ⟨.W, cm⟩)
    (wf : fragment.WellFormed sc) (mal : HasMalleability sc fragment mm)
    (nm : mm.nonMalleable = true) (d : cm.d = true) (u : cm.u = true) (e : mm.e = true) :
    RowCompleteWIn sc fragment := by
  apply rowCompleteW typed wf mal nm e
  · exact unsignedSatCompleteW_from_smaller_B typed wf mal nm e
      (fun child _smaller cx mx tx wx hx nx _ex => uniform_BSuccessComplete child cx mx tx wx hx nx)
  · exact conditionDsatW_from_smaller_B typed wf mal nm d u e
      (fun child _smaller => uniform_conditionFalseComplete child)

end LeanMiniscript.Extraction.TapscriptRecovery.SuccessUniform

namespace LeanMiniscript.Extraction.TapscriptRecovery.OriginCounts

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI ThresholdRun ThresholdCanonical FalseUniform
  SuccessUniform

theorem row_agreement_noChecked {child parent : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own expected : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType sc child ⟨.B, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (u : cm.u = true) (e : mm.e = true)
    (context : ExecutionContextIn sc parent child env flags pa po own) (nodup : child.keys.Nodup)
    (projection : (rowResult (satisfactionCandidates child env) (castToBool top)).usableWitness? = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (free : ¬ CheckedSignature child env flags own) : own = expected := by
  cases truth : castToBool top with
  | true =>
    have actual := actual_unsigned_B_satisfy typed wf mal nm context nodup bounded run truth free
    have selected : satisfy child env = some expected := by simpa [rowResult, truth, satisfy] using projection
    exact Option.some.inj (actual.symm.trans selected)
  | false =>
    have actual := uniform_conditionFalseComplete child cm mm typed wf mal nm d u e
      parent env flags pa po own top rest context nodup bounded run truth free
    have selected : dissatisfy child env = some expected := by simpa [rowResult, truth, dissatisfy] using projection
    exact Option.some.inj (actual.symm.trans selected)

def CheckedTrueRowAgreementBIn (sc : ScriptContext) (child parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags) (pa po : Witness) : Prop :=
  ∀ own expected top rest, ExecutionContextIn sc parent child env flags pa po own → child.keys.Nodup →
    satisfy child env = some expected →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = true → CheckedSignature child env flags own → own = expected

abbrev CheckedTrueRowAgreementB := CheckedTrueRowAgreementBIn .tapscript

end LeanMiniscript.Extraction.TapscriptRecovery.OriginCounts
