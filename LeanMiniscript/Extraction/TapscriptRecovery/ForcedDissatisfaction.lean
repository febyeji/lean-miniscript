import LeanMiniscript.Extraction.TapscriptRecovery.FalseBranches

/-! Relate forced execution, signed dissatisfaction, and unsigned witnesses. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.UnsignedForced

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat ForcedAndV BExecution WBoolean
  ThresholdAlt ThresholdRows OrBComplete UnsignedFalse OrBFalse
  AndorUnsignedFalse

def ForcedBIn (sc : ScriptContext) (signed : Bool) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    mm.f = true → mm.s = signed → AmbientForcedFalseIn sc fragment

abbrev ForcedB := ForcedBIn .tapscript

inductive UnsignedForcedShape : CoreFragment → Prop where
  | one : UnsignedForcedShape .one
  | older (n : Nat) : UnsignedForcedShape (.older n)
  | after (n : Nat) : UnsignedForcedShape (.after n)
  | and_v (X Y : CoreFragment) : UnsignedForcedShape (.and_v X Y)
  | and_b (X Y : CoreFragment) : UnsignedForcedShape (.and_b X Y)
  | or_d (X Y : CoreFragment) : UnsignedForcedShape (.or_d X Y)
  | or_i (X Y : CoreFragment) : UnsignedForcedShape (.or_i X Y)
  | andor (X Y Z : CoreFragment) : UnsignedForcedShape (.andor X Y Z)
  | n (X : CoreFragment) : UnsignedForcedShape (.n X)

theorem unsigned_forced_shape {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩)
    (mal : HasMalleability sc fragment mm) (f : mm.f = true) (s : mm.s = false) :
    UnsignedForcedShape fragment := by
  cases fragment with
  | zero => cases mal; cases f
  | one => exact .one
  | pk_k key => cases typed
  | pk_h key => cases typed
  | older n => exact .older n
  | after n => exact .after n
  | sha256 h => cases mal; cases f
  | hash256 h => cases mal; cases f
  | ripemd160 h => cases mal; cases f
  | hash160 h => cases mal; cases f
  | and_v X Y => exact .and_v X Y
  | and_b X Y => exact .and_b X Y
  | or_b X Y => cases mal; cases f
  | or_c X Y => cases typed
  | or_d X Y => exact .or_d X Y
  | or_i X Y => exact .or_i X Y
  | andor X Y Z => exact .andor X Y Z
  | a X => cases typed
  | s X => cases typed
  | c X => cases mal; cases s
  | d X => cases mal; cases f
  | v X => cases typed
  | j X => cases mal; cases f
  | n X => exact .n X
  | multi k keys => cases mal; cases f
  | multi_a k keys => cases mal; cases f
  | thresh k children => cases mal; cases f

theorem forcedB_of_polarities {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true) (f : mm.f = true)
    (unsigned : ForcedBIn sc false fragment) (signed : ForcedBIn sc true fragment) : AmbientForcedFalseIn sc fragment := by
  cases s : mm.s
  · exact unsigned cm mm typed wf mal nm f s
  · exact signed cm mm typed wf mal nm f s

theorem forced_older (n : Nat) (valid : validTimelockArg n) : AmbientForcedFalseIn sc (.older n) := by
  intro parent env flags pa po own top rest _context _nodup _bounded run falsehood
  change Eval [.pushNum n, .op .OP_CHECKSEQUENCEVERIFY] _ _ _ _ _ at run
  generalize stackEq : own.toInitialStack ++ rest = input at run
  cases run with
  | pushNum number tail script alt flags ctx result inner =>
    cases inner with
    | checksequenceverify_success operand value tail script alt flags ctx result _decode _nonneg _satisfied final =>
      cases final with
      | empty stack alt flags ctx =>
        have truth := (TimelockExecutionFacts.of_validTimelockArg (flags := flags) valid).positive
        change castToBool (scriptNat n) = false at falsehood
        rw [truth] at falsehood
        cases falsehood
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem forced_after (n : Nat) (valid : validTimelockArg n) : AmbientForcedFalseIn sc (.after n) := by
  intro parent env flags pa po own top rest _context _nodup _bounded run falsehood
  change Eval [.pushNum n, .op .OP_CHECKLOCKTIMEVERIFY] _ _ _ _ _ at run
  generalize stackEq : own.toInitialStack ++ rest = input at run
  cases run with
  | pushNum number tail script alt flags ctx result inner =>
    cases inner with
    | checklocktimeverify_success operand value tail script alt flags ctx result _decode _nonneg _satisfied final =>
      cases final with
      | empty stack alt flags ctx =>
        have truth := (TimelockExecutionFacts.of_validTimelockArg (flags := flags) valid).positive
        change castToBool (scriptNat n) = false at falsehood
        rw [truth] at falsehood
        cases falsehood
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem forced_n {X : CoreFragment} (forced : AmbientForcedFalseIn sc X) : AmbientForcedFalseIn sc (.n X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨value, childRun, zero⟩ := n_false_decoded run falsehood
  exact forced parent env flags pa po own value rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded childRun (decoded_zero_false zero)

theorem forced_or_d {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (forcedY : AmbientForcedFalseIn sc Y) : AmbientForcedFalseIn sc (.or_d X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨left, right, value, eq, _runX, _falseX, runY⟩ := or_d_false_run_frame tx ty wx wy run falsehood
  subst own
  have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_right _ h
  have inside : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  exact checkedSignature_mono keys inside
    (forcedY parent env flags pa po right top rest
      (executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inside)
      (List.pairwise_append.mp nodup).2.1 (fun item h => bounds item (List.mem_append_right _ h)) runY falsehood)

theorem forced_or_i {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (forcedX : AmbientForcedFalseIn sc X) (forcedY : AmbientForcedFalseIn sc Y) : AmbientForcedFalseIn sc (.or_i X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  rcases or_i_run_B tx ty wx wy context.rules run with ⟨active, eq, runX⟩ | ⟨active, eq, runY⟩
  · subst own
    have keys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
    exact checkedSignature_mono keys inside
      (forcedX parent env flags pa po active top rest
        (executionContext_restrict context keys (fun _ h => List.mem_append_left _ h) inside)
        (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) runX falsehood)
  · subst own
    have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
    exact checkedSignature_mono keys inside
      (forcedY parent env flags pa po active top rest
        (executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inside)
        (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) runY falsehood)

theorem booland_single_false {input alt rest : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] input alt flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ a b, input = a :: b :: rest ∧ alt = [] ∧ a.size ≤ maxScriptElementSize ∧ b.size ≤ maxScriptElementSize ∧
      (castToBool a = false ∨ castToBool b = false) := by
  cases run with
  | booland aBytes bBytes a b tail script alt flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      obtain ⟨da, db⟩ := decode_pair_parts decoded
      have zero : a = 0 ∨ b = 0 := by
        by_cases az : a = 0
        · exact Or.inl az
        · exact Or.inr (by simpa [az] using falsehood)
      refine ⟨aBytes, bBytes, rfl, rfl, WBoolean.decoded_size da, WBoolean.decoded_size db, ?_⟩
      rcases zero with rfl | rfl
      · exact Or.inl (decoded_zero_false da)
      · exact Or.inr (decoded_zero_false db)
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem booland_order_false {order : BaseWOutputOrder} {saved value top : StackElement}
    {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] (order.outputs saved value ++ tail) [] flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) : tail = rest ∧
      saved.size ≤ maxScriptElementSize ∧ value.size ≤ maxScriptElementSize ∧
      (castToBool saved = false ∨ castToBool value = false) := by
  obtain ⟨a, b, eq, _, ba, bb, falseChild⟩ := booland_single_false run falsehood
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append, List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, ba, bb, falseChild⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, bb, ba, falseChild.symm⟩

theorem and_b_false_frame {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (run : Eval (compile (.and_b X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder), own = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx (.success (order.outputs x y ++ rest) []) ∧
      x.size ≤ maxScriptElementSize ∧ y.size ≤ maxScriptElementSize ∧
      (castToBool x = false ∨ castToBool y = false) := by
  have combined : Eval (compile X ++ (compile Y ++ [.op .OP_BOOLAND]))
      (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨midX, altX, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ runX
  cases altEqX
  obtain ⟨midY, altY, runY, opRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow Y) tailRun
  obtain ⟨altEqY, effectY⟩ := refinedBaseTypeGuarantee_of_hasType ty wy _ _ _ _ _ runY
  cases altEqY
  obtain ⟨argsX, tailX, x, inputX, outputX, _⟩ := effectX.b_inv
  rw [outputX] at effectY runY
  obtain ⟨argsY, tailY, saved, y, order, inputY, outputY⟩ := effectY.w_inv
  obtain ⟨rfl, tailEq⟩ := List.cons.inj inputY
  rw [outputY] at opRun runY
  obtain ⟨rfl, bx, bySize, falseChild⟩ := booland_order_false opRun falsehood
  have inputEq : own.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : own = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, witnessEq, ?_, ?_, bx, bySize, falseChild⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY

def AmbientForcedWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = false → CheckedSignature fragment env flags own

abbrev AmbientForcedW := AmbientForcedWIn .tapscript

theorem unsignedForcedW_from_B {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (f : mm.f = true) (s : mm.s = false)
    (ih : ∀ sub, sizeOf sub < sizeOf fragment → ForcedBIn sc false sub) : AmbientForcedWIn sc fragment := by
  rcases typed_W_d_children typed with ⟨child, cx, rfl, tx, _deq⟩ | ⟨child, cx, rfl, tx, one, _deq⟩
  · cases mal with
    | a hx =>
      have forced := ih child (by simp) cx _ tx wf hx nm f s
      intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
      have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact forced parent env flags pa po own top rest
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood
  · cases mal with
    | s hx =>
      have forced := ih child (by simp) cx _ tx wf hx nm f s
      intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
      obtain ⟨_, childRun⟩ := s_run_child tx one wf run
      apply forced parent env flags pa po own top (saved :: rest)
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup _ childRun falsehood
      intro item member
      apply bounded item
      simp only [List.mem_cons, List.mem_append] at member ⊢
      rcases member with member | rfl | member
      · exact Or.inr (Or.inl member)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr member)

theorem forced_and_b {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (forcedX : AmbientForcedFalseIn sc X) (forcedY : AmbientForcedWIn sc Y) : AmbientForcedFalseIn sc (.and_b X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by, falseChild⟩ := and_b_false_frame tx ty wx wy run falsehood
  subst own
  have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  rcases falseChild with falseX | falseY
  · have keys : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_b X Y).keys := fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    exact checkedSignature_mono keys inside (forcedX parent env flags pa po left x (right.toInitialStack ++ rest)
      (executionContext_restrict context keys (fun _ h => List.mem_append_left _ h) inside)
      (List.pairwise_append.mp nodup).1 all runX falseX)
  · have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_b X Y).keys := fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have boundY : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact bx
      · exact all item (List.mem_append_right _ member)
    exact checkedSignature_mono keys inside (forcedY parent env flags pa po right x y rest order
      (executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inside)
      (List.pairwise_append.mp nodup).2.1 boundY runY falseY)

theorem forced_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers} {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (route : mx.s = true ∨ AmbientForcedFalseIn sc Y) (forcedZ : AmbientForcedFalseIn sc Z) :
    AmbientForcedFalseIn sc (.andor X Y Z) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  apply Classical.byContradiction
  intro free
  obtain ⟨left, right, value, eq, _runX, _falseX, runZ⟩ :=
    andor_false_active tx ty tz wx wy wz hx nx route context nodup bounded run falsehood free
  subst own
  have keys : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys := fun _ h => List.mem_append_right _ h
  have inside : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  exact free (checkedSignature_mono keys inside
    (forcedZ parent env flags pa po right top rest
      (executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inside)
      (List.pairwise_append.mp nodup).2.1 (fun item h => bounds item (List.mem_append_right _ h)) runZ falsehood))

theorem unsignedForcedB_step (fragment : CoreFragment)
    (unsigned : ∀ sub, sizeOf sub < sizeOf fragment → ForcedBIn sc false sub)
    (signed : ∀ sub, sizeOf sub < sizeOf fragment → ForcedBIn sc true sub) : ForcedBIn sc false fragment := by
  intro cm mm typed wf mal nm f s
  cases unsigned_forced_shape typed mal f s with
  | one => exact ambientForcedFalse_one
  | older n => exact forced_older n wf
  | after n => exact forced_after n wf
  | and_v X Y =>
    cases typed_B_shape typed with
    | remaining impossible => simp [RemainingB] at impossible
    | and_v tx ty =>
      cases mal with
      | @and_v X Y mx my hx hy =>
        obtain ⟨_nx, ny⟩ := Bool.and_eq_true_iff.mp nm
        obtain ⟨sx, sy⟩ := Bool.or_eq_false_iff.mp s
        have fy : my.f = true := by simpa [sx] using f
        exact forced_and_v_of_forced_child tx ty wf.1 wf.2.1
          (unsigned Y (by simp; omega) _ my ty wf.2.1 hy ny fy sy)
  | and_b X Y =>
    cases typed with
    | and_b tx ty =>
      cases mal with
      | @and_b X Y mx my hx hy =>
        obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
        obtain ⟨sx, sy⟩ := Bool.or_eq_false_iff.mp s
        have fs : mx.f = true ∧ my.f = true := by simpa [sx, sy] using f
        exact forced_and_b tx ty wf.1 wf.2.1
          (unsigned X (by simp; omega) _ mx tx wf.1 hx nx fs.1 sx)
          (unsignedForcedW_from_B ty wf.2.1 hy ny fs.2 sy
            (fun sub smaller => unsigned sub (Nat.lt_trans smaller (by simp; omega))))
  | or_d X Y =>
    cases typed with
    | or_d tx _dx _ux ty =>
      cases mal with
      | or_d hx hy =>
        obtain ⟨_nx, ny, _ex, _choice⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
        exact forced_or_d tx ty wf.1 wf.2
          (forcedB_of_polarities ty wf.2 hy ny f
            (unsigned Y (by simp; omega)) (signed Y (by simp; omega)))
  | or_i X Y =>
    cases typed_B_shape typed with
    | remaining impossible => simp [RemainingB] at impossible
    | or_i tx ty =>
      cases mal with
      | or_i hx hy =>
        obtain ⟨nx, ny, _choice⟩ := (boolAnd3_eq_true _ _ _).mp nm
        obtain ⟨fx, fy⟩ := Bool.and_eq_true_iff.mp f
        exact forced_or_i tx ty wf.1 wf.2
          (forcedB_of_polarities tx wf.1 hx nx fx (unsigned X (by simp; omega)) (signed X (by simp; omega)))
          (forcedB_of_polarities ty wf.2 hy ny fy (unsigned Y (by simp; omega)) (signed Y (by simp; omega)))
  | andor X Y Z =>
    cases typed_B_shape typed with
    | remaining impossible => simp [RemainingB] at impossible
    | andor tx _dx _ux ty tz =>
      cases mal with
      | @andor X Y Z mx my mz hx hy hz =>
        obtain ⟨nx, ny, nz, _ex, _choice⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
        obtain ⟨fz, guard⟩ := Bool.and_eq_true_iff.mp f
        apply forced_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx
        · rcases Bool.or_eq_true_iff.mp guard with sx | fy
          · exact Or.inl sx
          · exact Or.inr (forcedB_of_polarities ty wf.2.1 hy ny fy
              (unsigned Y (by simp; omega)) (signed Y (by simp; omega)))
        · exact forcedB_of_polarities tz wf.2.2.1 hz nz fz
            (unsigned Z (by simp; omega)) (signed Z (by simp; omega))
  | n X =>
    cases typed with
    | n_wrap tx =>
      cases mal with
      | n hx => exact forced_n (unsigned X (by simp) _ _ tx wf hx nm f s)

theorem unsignedForcedB_from_signed (fragment : CoreFragment)
    (signed : ∀ sub, sizeOf sub < sizeOf fragment → ForcedBIn sc true sub) : ForcedBIn sc false fragment :=
  unsignedForcedB_step fragment
    (fun sub smaller => unsignedForcedB_from_signed sub
      (fun inner bound => signed inner (Nat.lt_trans bound smaller))) signed
termination_by sizeOf fragment

theorem forcedUnit_of_forcedB {polarity : Bool} {fragment : CoreFragment}
    (forced : ForcedBIn sc polarity fragment) : ForcedUnitBIn sc polarity fragment := by
  intro cm mm typed wf mal nm _u f s
  exact forced cm mm typed wf mal nm f s

end LeanMiniscript.Extraction.TapscriptRecovery.UnsignedForced

namespace LeanMiniscript.Extraction.TapscriptRecovery.SignedLink

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat ForcedAndV SignedV BExecution
  CompoundK WBoolean ThresholdAlt ThresholdRows ThresholdUnit OrBFalse
  UnsignedForced

theorem forced_n_decoded {X : CoreFragment} (forced : AmbientForcedFalseIn sc X) :
    AmbientForcedFalseIn sc (.n X) := UnsignedForced.forced_n forced

theorem forced_and_v_signed_prefix {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx : MalleabilityModifiers} (tx : HasType sc X ⟨.V, cx⟩)
    (ty : HasType sc Y ⟨.B, cy⟩) (wx : X.WellFormed sc)
    (wy : Y.WellFormed sc) (hx : HasMalleability sc X mx)
    (nx : mx.nonMalleable = true) (sx : mx.s = true) : AmbientForcedFalseIn sc (.and_v X Y) :=
  forced_and_v_of_signed_prefix tx ty wx wy
    (uniform_signedV_of_uniform_B uniform_B_execution X cx mx tx wx hx nx sx)

theorem booland_single_false {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] input alt flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ aBytes bBytes a b, input = aBytes :: bBytes :: rest ∧ alt = [] ∧
      decodeScriptNum aBytes flags.minimalData maxArithmeticScriptNumBytes = .ok a ∧
      decodeScriptNum bBytes flags.minimalData maxArithmeticScriptNumBytes = .ok b ∧
      (a = 0 ∨ b = 0) ∧ (castToBool aBytes = false ∨ castToBool bBytes = false) := by
  cases run with
  | booland aBytes bBytes a b tail script alt flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      obtain ⟨da, db⟩ := decode_pair_parts decoded
      have zero : a = 0 ∨ b = 0 := by
        by_cases az : a = 0
        · exact Or.inl az
        · exact Or.inr (by simpa [az] using falsehood)
      refine ⟨aBytes, bBytes, a, b, rfl, rfl, da, db, zero, ?_⟩
      rcases zero with rfl | rfl
      · exact Or.inl (decoded_zero_false da)
      · exact Or.inr (decoded_zero_false db)
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem booland_order_false {order : BaseWOutputOrder}
    {saved result top : StackElement} {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] (order.outputs saved result ++ tail) [] flags ctx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    tail = rest ∧ ∃ x y,
      decodeScriptNum saved flags.minimalData maxArithmeticScriptNumBytes = .ok x ∧
      decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok y ∧
      (x = 0 ∨ y = 0) ∧ (castToBool saved = false ∨ castToBool result = false) := by
  obtain ⟨aBytes, bBytes, a, b, eq, _, da, db, zero, falses⟩ := booland_single_false run falsehood
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append,
    List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, a, b, da, db, zero, falses⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, b, a, db, da, zero.symm, falses.symm⟩

theorem and_b_false_run_frame {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.and_b X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder) (a b : Int),
      own = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs x y ++ rest) []) ∧
      decodeScriptNum x flags.minimalData maxArithmeticScriptNumBytes = .ok a ∧
      decodeScriptNum y flags.minimalData maxArithmeticScriptNumBytes = .ok b ∧
      (a = 0 ∨ b = 0) ∧ (castToBool x = false ∨ castToBool y = false) ∧
      (∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) ∧
      (∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) := by
  have combined : Eval (compile X ++ (compile Y ++ [.op .OP_BOOLAND]))
      (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨midX, altX, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ runX
  cases altEqX
  obtain ⟨midY, altY, runY, opRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow Y) tailRun
  obtain ⟨altEqY, effectY⟩ := refinedBaseTypeGuarantee_of_hasType ty wy _ _ _ _ _ runY
  cases altEqY
  obtain ⟨argsX, tailX, x, inputX, outputX, _⟩ := effectX.b_inv
  rw [outputX] at effectY runY
  obtain ⟨argsY, tailY, saved, y, order, inputY, outputY⟩ := effectY.w_inv
  obtain ⟨rfl, tailEq⟩ := List.cons.inj inputY
  rw [outputY] at opRun runY
  obtain ⟨rfl, a, b, da, db, zero, falses⟩ := booland_order_false opRun falsehood
  have inputEq : own.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : own = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  have bounds : ∀ item ∈ Witness.toInitialStack argsX.reverse ++
      (Witness.toInitialStack argsY.reverse ++ tailY),
      item.size ≤ maxScriptElementSize := by
    simpa only [witnessEq, Witness.toInitialStack_append, List.append_assoc] using bounded
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, a, b, witnessEq, ?_, ?_, da, db, zero, falses,
    bounds, ?_⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY
  · intro item member
    rcases List.mem_cons.mp member with rfl | h
    · exact WBoolean.decoded_size da
    · exact bounds item (List.mem_append_right _ h)

theorem and_b_signed_forced_choice (sx sy fx fy : Bool)
    (signed : (sx || sy) = true)
    (forced : ((fx && fy) || (sx && fx) || (sy && fy)) = true) :
    (sx = true ∧ fx = true) ∨ (sy = true ∧ fy = true) := by
  cases sx <;> cases sy <;> cases fx <;> cases fy <;> simp_all

def AmbientForcedFalseWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = false → CheckedSignature fragment env flags own

abbrev AmbientForcedFalseW := AmbientForcedFalseWIn .tapscript

def SignedForcedBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    mm.s = true → mm.f = true → AmbientForcedFalseIn sc fragment

abbrev SignedForcedB := SignedForcedBIn .tapscript

theorem forcedFalseW_a {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (wx : X.WellFormed sc)
    (forced : AmbientForcedFalseIn sc X) : AmbientForcedFalseWIn sc (.a X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
  have childRun := uniform_savedAltTransfer X _ _ saved flags env.txCtx (a_run_child tx wx run)
  exact forced parent env flags pa po own top rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood

theorem forcedFalseW_s {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (one : cx.o = true) (wx : X.WellFormed sc)
    (forced : AmbientForcedFalseIn sc X) : AmbientForcedFalseWIn sc (.s X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
  obtain ⟨_, childRun⟩ := s_run_child tx one wx run
  apply forced parent env flags pa po own top (saved :: rest)
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup _ childRun falsehood
  intro item member
  apply bounded item
  simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using member

theorem signedForcedW_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc fragment ⟨.W, cm⟩)
    (wf : fragment.WellFormed sc) (mal : HasMalleability sc fragment mm)
    (nm : mm.nonMalleable = true) (s : mm.s = true) (f : mm.f = true)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedForcedBIn sc child) :
    AmbientForcedFalseWIn sc fragment := by
  cases typed_W_shape typed with
  | a tx =>
    cases mal with
    | a hx => exact forcedFalseW_a tx wf (ih _ (by simp) _ _ tx wf hx nm s f)
  | s tx one =>
    cases mal with
    | s hx => exact forcedFalseW_s tx one wf (ih _ (by simp) _ _ tx wf hx nm s f)

theorem forced_and_b_of_signed_false {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (signed : (mx.s || my.s) = true)
    (forced : ((mx.f && my.f) || (mx.s && mx.f) || (my.s && my.f)) = true)
    (falseX : mx.s = true → mx.f = true → AmbientForcedFalseIn sc X)
    (falseY : my.s = true → my.f = true → AmbientForcedFalseWIn sc Y) :
    AmbientForcedFalseIn sc (.and_b X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨left, right, x, y, order, a, b, eq, runX, runY, _da, _db, _zero, _falses, boundsX, boundsY⟩ :=
    and_b_false_run_frame tx ty wx wy bounded run falsehood
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_b X Y).keys :=
    fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_b X Y).keys :=
    fun _ h => List.mem_append_right _ h
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have contextX := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  rcases and_b_signed_forced_choice mx.s my.s mx.f my.f signed forced with ⟨sx, fx⟩ | ⟨sy, fy⟩
  · apply checkedSignature_mono keysX inX
    cases truth : castToBool x with
    | false =>
      exact falseX sx fx parent env flags pa po left x (right.toInitialStack ++ rest)
        contextX (List.pairwise_append.mp nodup).1 boundsX runX truth
    | true =>
      exact signed_consumption_of_malleability wx tx hx sx
        (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left x
          (right.toInitialStack ++ rest) contextX boundsX runX truth)
  · apply checkedSignature_mono keysY inY
    cases truth : castToBool y with
    | false =>
      exact falseY sy fy parent env flags pa po right x y rest order contextY
        (List.pairwise_append.mp nodup).2.1 boundsY runY truth
    | true =>
      exact signed_consumption_of_malleability wy ty hy sy
        (ambientExecutionW_step ty wy hy ny (fun child _ => uniform_B_execution child)
          parent env flags pa po right x y rest order contextY boundsY runY truth)

theorem signedForcedB_and_b_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.and_b X Y) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.and_b X Y) := by
  intro cm mm typed wf mal nm s f
  cases typed with
  | and_b tx ty =>
    cases mal with
    | and_b hx hy =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      exact forced_and_b_of_signed_false tx ty wf.1 wf.2.1 hx hy nx ny s f
        (fun sx fx => ih X (by simp; omega) _ _ tx wf.1 hx nx sx fx)
        (fun sy fy => signedForcedW_from_smaller_B ty wf.2.1 hy ny sy fy
          (fun child smaller => ih child (Nat.lt_trans smaller (by simp; omega))))

theorem signedForcedB_n_step {X : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.n X) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.n X) := by
  intro cm mm typed wf mal nm s f
  cases typed with
  | n_wrap tx =>
    cases mal with
    | n hx => exact forced_n_decoded (ih X (by simp) _ _ tx wf hx nm s f)

def AmbientForcedKIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (keyBytes : StackElement) (rest : Stack),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (keyBytes :: rest) []) → CheckedSignature fragment env flags own

abbrev AmbientForcedK := AmbientForcedKIn .tapscript

def ForcedKIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.K, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    mm.f = true → AmbientForcedKIn sc fragment

abbrev ForcedK := ForcedKIn .tapscript

theorem checksig_false_frame {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIG] input alt flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ keyBytes sig, input = keyBytes :: sig :: rest ∧ alt = [] ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig keyBytes = .ok false := by
  cases run with
  | checksig_success keyBytes sig tail script alt flags ctx result _checked final =>
    cases final with
    | empty stack alt flags ctx => simp [castToBool, trueElement] at falsehood
  | checksig_failure keyBytes sig tail script alt flags ctx result checked final =>
    cases final with
    | empty stack alt flags ctx => exact ⟨keyBytes, sig, rfl, rfl, checked⟩
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem c_false_run_frame {X : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {other : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType sc X ⟨.K, cm⟩) (wf : X.WellFormed sc)
    (run : Eval (compile (.c X)) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    ∃ (own : Witness) (sig keyBytes : StackElement), other = [sig] ++ own ∧
      Eval (compile X) (own.toInitialStack ++ (sig :: rest)) [] flags env.txCtx
        (.success (keyBytes :: sig :: rest) []) ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig keyBytes = .ok false := by
  change Eval (compile X ++ [.op .OP_CHECKSIG]) _ _ _ _ _ at run
  obtain ⟨mid, midAlt, runX, checkRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  obtain ⟨keyBytes, sig, midEq, altEq, checked⟩ := checksig_false_frame checkRun falsehood
  subst midAlt
  rw [midEq] at runX
  obtain ⟨own, inputEq⟩ := typed_K_input_frame typed wf runX
  have stackEq : other.toInitialStack = own.toInitialStack ++ [sig] := by
    apply List.append_cancel_right
    simpa [List.append_assoc] using inputEq
  have otherEq : other = [sig] ++ own := by
    simpa [Witness.toInitialStack] using congrArg List.reverse stackEq
  exact ⟨own, sig, keyBytes, otherEq, by rw [← inputEq]; exact runX, checked⟩

theorem forcedK_and_v {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.V, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (route : mx.s = true ∨ AmbientForcedKIn sc Y) : AmbientForcedKIn sc (.and_v X Y) := by
  intro parent env flags pa po own keyBytes rest context nodup bounded run
  obtain ⟨left, right, eq, runX, runY⟩ := and_v_run_K_frame tx ty wx wy run
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.and_v X Y).keys := fun _ h => List.mem_append_right _ h
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  rcases route with sx | forcedY
  · exact checkedSignature_mono keysX inX
      (uniform_signedV_of_uniform_B uniform_B_execution X cx mx tx wx hx nx sx
        parent env flags pa po left (right.toInitialStack ++ rest)
        (executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX)
        (List.pairwise_append.mp nodup).1 bounds runX)
  · exact checkedSignature_mono keysY inY
      (forcedY parent env flags pa po right keyBytes rest
        (executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY)
        (List.pairwise_append.mp nodup).2.1
        (fun item h => bounds item (List.mem_append_right _ h)) runY)

theorem forcedK_or_i {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.K, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (forcedX : AmbientForcedKIn sc X) (forcedY : AmbientForcedKIn sc Y) : AmbientForcedKIn sc (.or_i X Y) := by
  intro parent env flags pa po own keyBytes rest context nodup bounded run
  rcases or_i_run_K tx ty wx wy context.rules run with ⟨active, eq, runX⟩ | ⟨active, eq, runY⟩
  · subst own
    have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
    exact checkedSignature_mono keysX inside
      (forcedX parent env flags pa po active keyBytes rest
        (executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inside)
        (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) runX)
  · subst own
    have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
    exact checkedSignature_mono keysY inside
      (forcedY parent env flags pa po active keyBytes rest
        (executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inside)
        (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) runY)

theorem forcedK_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.K, cy⟩)
    (tz : HasType sc Z ⟨.K, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (forcedZ : AmbientForcedKIn sc Z) (route : mx.s = true ∨ AmbientForcedKIn sc Y) :
    AmbientForcedKIn sc (.andor X Y Z) := by
  intro parent env flags pa po own keyBytes rest context nodup bounded run
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  rcases andor_run_K_frame tx ty tz wx wy wz run with
    ⟨left, right, top, eq, _runX, _falseX, runZ⟩ | ⟨left, right, top, eq, runX, trueX, runY⟩
  · subst own
    have inside : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    exact checkedSignature_mono keysZ inside
      (forcedZ parent env flags pa po right keyBytes rest
        (executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inside)
        (List.pairwise_append.mp nodup).2.1
        (fun item h => bounds item (List.mem_append_right _ h)) runZ)
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases route with sx | forcedY
    · exact checkedSignature_mono keysX inX (signed_consumption_of_malleability wx tx hx sx
        (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left top
          (right.toInitialStack ++ rest)
          (executionContext_restrict context keysX
            (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX) bounds runX trueX))
    · exact checkedSignature_mono keysY inY
        (forcedY parent env flags pa po right keyBytes rest
          (executionContext_restrict context keysY
            (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY)
          (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).2.1
          (fun item h => bounds item (List.mem_append_right _ h)) runY)

theorem forcedK_constructor_step (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → ForcedKIn sc child) : ForcedKIn sc fragment := by
  intro cm mm typed wf mal nm f
  cases typed_K_shape typed with
  | pk_k key => cases mal; cases f
  | pk_h key => cases mal; cases f
  | and_v tx ty =>
    cases mal with
    | and_v hx hy =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      apply forcedK_and_v tx ty wf.1 wf.2.1 hx nx
      rcases Bool.or_eq_true_iff.mp f with sx | fy
      · exact Or.inl sx
      · exact Or.inr (ih _ (by simp; omega) _ _ ty wf.2.1 hy ny fy)
  | or_i tx ty =>
    cases mal with
    | or_i hx hy =>
      obtain ⟨nx, ny, _⟩ := (boolAnd3_eq_true _ _ _).mp nm
      obtain ⟨fx, fy⟩ := Bool.and_eq_true_iff.mp f
      exact forcedK_or_i tx ty wf.1 wf.2
        (ih _ (by simp; omega) _ _ tx wf.1 hx nx fx)
        (ih _ (by simp; omega) _ _ ty wf.2 hy ny fy)
  | andor tx _d _u ty tz =>
    cases mal with
    | andor hx hy hz =>
      obtain ⟨nx, ny, nz, _ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      obtain ⟨fz, route⟩ := Bool.and_eq_true_iff.mp f
      apply forcedK_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx
        (ih _ (by simp; omega) _ _ tz wf.2.2.1 hz nz fz)
      rcases Bool.or_eq_true_iff.mp route with sx | fy
      · exact Or.inl sx
      · exact Or.inr (ih _ (by simp; omega) _ _ ty wf.2.1 hy ny fy)

theorem uniform_forcedK (fragment : CoreFragment) : ForcedKIn sc fragment :=
  forcedK_constructor_step fragment (fun child _smaller => uniform_forcedK child)
termination_by sizeOf fragment

theorem forced_c_of_K {X : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc X ⟨.K, cm⟩) (wf : X.WellFormed sc)
    (forced : AmbientForcedKIn sc X) : AmbientForcedFalseIn sc (.c X) := by
  intro parent env flags pa po other top rest context nodup bounded run falsehood
  obtain ⟨own, sig, keyBytes, eq, runX, _checkFalse⟩ := c_false_run_frame typed wf run falsehood
  subst other
  have child := executionContext_restrict context (active := X)
    (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_append_right _ h)
  have bounds : ∀ item ∈ own.toInitialStack ++ (sig :: rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_cons, List.append_assoc] using bounded
  exact checkedSignature_mono (fun _ h => h) (fun _ h => List.mem_append_right _ h)
    (forced parent env flags pa po own keyBytes (sig :: rest) child nodup bounds runX)

theorem signedForcedB_c (X : CoreFragment) : SignedForcedBIn sc (.c X) := by
  intro cm mm typed wf mal nm _s f
  cases typed with
  | c_wrap tx =>
    cases mal with
    | c hx => exact forced_c_of_K tx wf (uniform_forcedK X _ _ tx wf hx nm f)

theorem signedForcedB_and_v_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.and_v X Y) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.and_v X Y) := by
  intro cm mm typed wf mal nm s f
  cases typed_B_shape typed with
  | remaining impossible => simp [RemainingB] at impossible
  | and_v tx ty =>
    cases mal with
    | and_v hx hy =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      rcases Bool.or_eq_true_iff.mp s with sx | sy
      · exact forced_and_v_signed_prefix tx ty wf.1 wf.2.1 hx nx sx
      · rcases Bool.or_eq_true_iff.mp f with sx | fy
        · exact forced_and_v_signed_prefix tx ty wf.1 wf.2.1 hx nx sx
        · exact forced_and_v_of_forced_child tx ty wf.1 wf.2.1
            (ih _ (by simp; omega) _ _ ty wf.2.1 hy ny sy fy)

theorem signedForcedB_or_d_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_d X Y) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.or_d X Y) := by
  intro cm mm typed wf mal nm s f
  cases typed with
  | or_d tx _d _u ty =>
    cases mal with
    | or_d hx hy =>
      obtain ⟨_nx, ny, _ex, _⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      obtain ⟨_sx, sy⟩ := Bool.and_eq_true_iff.mp s
      exact forced_or_d tx ty wf.1 wf.2 (ih _ (by simp; omega) _ _ ty wf.2 hy ny sy f)

theorem signedForcedB_or_i_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.or_i X Y) := by
  intro cm mm typed wf mal nm s f
  cases typed_B_shape typed with
  | remaining impossible => simp [RemainingB] at impossible
  | or_i tx ty =>
    cases mal with
    | or_i hx hy =>
      obtain ⟨nx, ny, _⟩ := (boolAnd3_eq_true _ _ _).mp nm
      obtain ⟨sx, sy⟩ := Bool.and_eq_true_iff.mp s
      obtain ⟨fx, fy⟩ := Bool.and_eq_true_iff.mp f
      exact forced_or_i tx ty wf.1 wf.2
        (ih _ (by simp; omega) _ _ tx wf.1 hx nx sx fx)
        (ih _ (by simp; omega) _ _ ty wf.2 hy ny sy fy)

theorem signedForcedB_andor_step {X Y Z : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.andor X Y Z) → SignedForcedBIn sc child) :
    SignedForcedBIn sc (.andor X Y Z) := by
  intro cm mm typed wf mal nm s f
  cases typed_B_shape typed with
  | remaining impossible => simp [RemainingB] at impossible
  | andor tx _d _u ty tz =>
    cases mal with
    | @andor X Y Z mx my mz hx hy hz =>
      obtain ⟨nx, ny, nz, _ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      obtain ⟨sz, signedChoice⟩ := Bool.and_eq_true_iff.mp s
      obtain ⟨fz, forcedChoice⟩ := Bool.and_eq_true_iff.mp f
      have forcedZ := ih Z (by simp; omega) _ mz tz wf.2.2.1 hz nz sz fz
      have route : mx.s = true ∨ AmbientForcedFalseIn sc Y := by
        rcases Bool.or_eq_true_iff.mp signedChoice with sx | sy
        · exact Or.inl sx
        · rcases Bool.or_eq_true_iff.mp forcedChoice with sx | fy
          · exact Or.inl sx
          · exact Or.inr (ih Y (by simp; omega) _ my ty wf.2.1 hy ny sy fy)
      intro parent env flags pa po own top rest context nodup bounded run falsehood
      have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
        fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
      have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
        fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
      have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
        fun _ h => List.mem_append_right _ h
      rcases andor_run_B_frame tx ty tz wf.1 wf.2.1 wf.2.2.1 run with
        ⟨left, right, value, eq, _runX, _falseX, runZ⟩ | ⟨left, right, value, eq, runX, trueX, runY⟩
      · subst own
        have inside : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
        have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
            item.size ≤ maxScriptElementSize := by
          simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
        exact checkedSignature_mono keysZ inside
          (forcedZ parent env flags pa po right top rest
            (executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inside)
            (List.pairwise_append.mp nodup).2.1
            (fun item h => bounds item (List.mem_append_right _ h)) runZ falsehood)
      · subst own
        have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
        have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
        have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
            item.size ≤ maxScriptElementSize := by
          simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
        rcases route with sx | forcedY
        · exact checkedSignature_mono keysX inX (signed_consumption_of_malleability wf.1 tx hx sx
            (uniform_B_execution X _ mx tx wf.1 hx nx parent env flags pa po left value
              (right.toInitialStack ++ rest)
              (executionContext_restrict context keysX
                (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX) bounds runX trueX))
        · exact checkedSignature_mono keysY inY
            (forcedY parent env flags pa po right top rest
              (executionContext_restrict context keysY
                (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY)
              (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).2.1
              (fun item h => bounds item (List.mem_append_right _ h)) runY falsehood)

theorem signedForcedB_constructor_step (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedForcedBIn sc child) :
    SignedForcedBIn sc fragment := by
  intro cm mm typed wf mal nm s f
  cases fragment with
  | zero => cases mal; cases f
  | one => cases mal; cases s
  | pk_k key => cases typed
  | pk_h key => cases typed
  | older n => cases mal; cases s
  | after n => cases mal; cases s
  | sha256 h => cases mal; cases s
  | hash256 h => cases mal; cases s
  | ripemd160 h => cases mal; cases s
  | hash160 h => cases mal; cases s
  | and_v X Y => exact signedForcedB_and_v_step ih cm mm typed wf mal nm s f
  | and_b X Y => exact signedForcedB_and_b_step ih cm mm typed wf mal nm s f
  | or_b X Y => cases mal; cases f
  | or_c X Y => cases typed
  | or_d X Y => exact signedForcedB_or_d_step ih cm mm typed wf mal nm s f
  | or_i X Y => exact signedForcedB_or_i_step ih cm mm typed wf mal nm s f
  | andor X Y Z => exact signedForcedB_andor_step ih cm mm typed wf mal nm s f
  | a X => cases typed
  | s X => cases typed
  | c X => exact signedForcedB_c X cm mm typed wf mal nm s f
  | d X => cases mal; cases f
  | v X => cases typed
  | j X => cases mal; cases f
  | n X => exact signedForcedB_n_step ih cm mm typed wf mal nm s f
  | multi k keys => cases mal; cases f
  | multi_a k keys => cases mal; cases f
  | thresh k children => cases mal; cases f

theorem uniform_signedForcedB (fragment : CoreFragment) : SignedForcedBIn sc fragment :=
  signedForcedB_constructor_step fragment (fun child _smaller => uniform_signedForcedB child)
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.SignedLink

namespace LeanMiniscript.Extraction.TapscriptRecovery.ForcedLinked

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Dsat AndorUnsignedFalse UnsignedForced

theorem signed_contract_iff (fragment : CoreFragment) :
    SignedLink.SignedForcedBIn sc fragment ↔ ForcedBIn sc true fragment := by
  constructor
  · intro proved cm mm typed wf mal nm f s
    exact proved cm mm typed wf mal nm s f
  · intro proved cm mm typed wf mal nm s f
    exact proved cm mm typed wf mal nm f s

theorem uniform_signedB (fragment : CoreFragment) : ForcedBIn sc true fragment :=
  (signed_contract_iff fragment).mp (SignedLink.uniform_signedForcedB fragment)

theorem uniform_unsignedB (fragment : CoreFragment) : ForcedBIn sc false fragment :=
  unsignedForcedB_from_signed fragment (fun child _smaller => uniform_signedB child)

theorem uniform_forcedB (polarity : Bool) (fragment : CoreFragment) : ForcedBIn sc polarity fragment := by
  cases polarity
  · exact uniform_unsignedB fragment
  · exact uniform_signedB fragment

theorem uniform_forcedUnitB (polarity : Bool) (fragment : CoreFragment) : ForcedUnitBIn sc polarity fragment :=
  forcedUnit_of_forcedB (uniform_forcedB polarity fragment)

theorem ambientForcedFalse_of_typed {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (f : mm.f = true) : AmbientForcedFalseIn sc fragment :=
  uniform_forcedB mm.s fragment cm mm typed wf mal nm f rfl

end LeanMiniscript.Extraction.TapscriptRecovery.ForcedLinked

namespace LeanMiniscript.Extraction.TapscriptRecovery.ForcedAdapter

open LeanMiniscript.Miniscript LeanMiniscript.Extraction SignedDsat UnsignedFalse
  AndorUnsignedFalse OrBFalse VRestComplete UnsignedOrI

theorem smaller_forcedUnit_false (fragment : CoreFragment) :
    ∀ child, sizeOf child < sizeOf fragment → ForcedUnitBIn sc false child :=
  fun child _smaller => ForcedLinked.uniform_forcedUnitB false child

theorem falseFamilies_from_nonunit (fragment : CoreFragment)
    (nonunit : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    SignedDsatBIn sc fragment ∧ UnsignedFalseIn sc fragment :=
  falseFamilies_from_boundaries fragment (smaller_forcedUnit_false fragment) nonunit

theorem conditionFalse_from_nonunit (fragment : CoreFragment)
    (nonunit : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    BConditionFalseCompleteIn sc fragment :=
  conditionFalse_from_boundaries fragment (smaller_forcedUnit_false fragment) nonunit

end LeanMiniscript.Extraction.TapscriptRecovery.ForcedAdapter
