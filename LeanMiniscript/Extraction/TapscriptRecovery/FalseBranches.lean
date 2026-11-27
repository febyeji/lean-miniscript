import LeanMiniscript.Extraction.TapscriptRecovery.UnsignedThreshold

/-! Propagate unsigned false-execution evidence through boolean branches and selectors. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrBFalse

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat WBoolean ThresholdAlt
  ThresholdRows OrBComplete UnsignedFalse

theorem byte_zero_of_toNat_zero {b : UInt8} (zero : b.toNat = 0) : b = 0 := by
  exact UInt8.toNat.inj zero

theorem byte_zero_or_sign_of_mod_zero {b : UInt8} (zero : b.toNat % 128 = 0) : b = 0 ∨ b = 128 := by
  have bound := b.toNat_lt
  have split : b.toNat = 0 ∨ b.toNat = 128 := by omega
  rcases split with zero | sign
  · exact Or.inl (UInt8.toNat.inj zero)
  · exact Or.inr (UInt8.toNat.inj sign)

theorem decoded_zero_false {operand : StackElement} {minimal : Bool}
    (decoded : decodeScriptNum operand minimal maxArithmeticScriptNumBytes = .ok (0 : Int)) :
    castToBool operand = false := by
  have bound : operand.size ≤ 4 := by
    by_cases bounded : operand.size ≤ 4
    · exact bounded
    · have large : operand.size > 4 := by omega
      simp [decodeScriptNum, maxArithmeticScriptNumBytes, large] at decoded
  have magnitude : decodeUnsignedLEAux (clearScriptNumSignBit operand.data.toList) 1 = 0 := by
    unfold decodeScriptNum at decoded
    split at decoded
    · contradiction
    · split at decoded
      · contradiction
      · dsimp only at decoded
        split at decoded <;> simpa using decoded
  rcases operand with ⟨data⟩
  have repr : (⟨data⟩ : ByteArray) = ⟨data.toList.toArray⟩ := by simp
  generalize bytesEq : data.toList = bytes at repr
  rw [repr] at magnitude bound ⊢
  change bytes.length ≤ 4 at bound
  rcases bytes with _ | ⟨a, tail⟩
  · rfl
  rcases tail with _ | ⟨b, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    have az := byte_zero_or_sign_of_mod_zero (b := a) (by omega)
    rcases az with rfl | rfl <;> decide
  rcases tail with _ | ⟨c, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    obtain ⟨az, bz⟩ := magnitude
    have az := byte_zero_of_toNat_zero az
    have bz := byte_zero_or_sign_of_mod_zero (b := b) (by omega)
    rcases bz with bz | bz <;> subst a <;> subst b <;> decide
  rcases tail with _ | ⟨d, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    obtain ⟨az, bz, cz⟩ := magnitude
    have az := byte_zero_of_toNat_zero az
    have bz := byte_zero_of_toNat_zero (b := b) (by omega)
    have cz := byte_zero_or_sign_of_mod_zero (b := c) (by omega)
    rcases cz with cz | cz <;> subst a <;> subst b <;> subst c <;> decide
  rcases tail with _ | ⟨e, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    obtain ⟨az, bz, cz, dz⟩ := magnitude
    have az := byte_zero_of_toNat_zero az
    have bz := byte_zero_of_toNat_zero (b := b) (by omega)
    have cz := byte_zero_of_toNat_zero (b := c) (by omega)
    have dz := byte_zero_or_sign_of_mod_zero (b := d) (by omega)
    rcases dz with dz | dz <;> subst a <;> subst b <;> subst c <;> subst d <;> decide
  simp at bound

theorem boolor_single_false {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLOR] input alt flags ctx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ a b, input = a :: b :: rest ∧ alt = [] ∧
      decodeScriptNum a flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      decodeScriptNum b flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) := by
  cases run with
  | boolor aBytes bBytes a b tail script alt flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      obtain ⟨da, db⟩ := decode_pair_parts decoded
      have both : a = 0 ∧ b = 0 := by simpa using falsehood
      exact ⟨aBytes, bBytes, rfl, rfl, both.1 ▸ da, both.2 ▸ db⟩
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem boolor_order_false {order : BaseWOutputOrder}
    {saved result top : StackElement} {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLOR] (order.outputs saved result ++ tail) [] flags ctx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    tail = rest ∧
      decodeScriptNum saved flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) := by
  obtain ⟨a, b, eq, _, da, db⟩ := boolor_single_false run falsehood
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append, List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, da, db⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, db, da⟩

theorem or_b_false_frame {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (run : Eval (compile (.or_b X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder),
      own = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs x y ++ rest) []) ∧
      decodeScriptNum x flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      decodeScriptNum y flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) ∧
      x.size ≤ maxScriptElementSize ∧ y.size ≤ maxScriptElementSize ∧
      castToBool x = false ∧ castToBool y = false := by
  have combined : Eval (compile X ++ (compile Y ++ [.op .OP_BOOLOR]))
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
  obtain ⟨rfl, dx, dy⟩ := boolor_order_false opRun falsehood
  have inputEq : own.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : own = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, witnessEq, ?_, ?_, dx, dy,
    WBoolean.decoded_size dx, WBoolean.decoded_size dy, decoded_zero_false dx, decoded_zero_false dy⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY

def DecodedZeroDsatCompleteWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved value : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved value ++ rest) []) →
    decodeScriptNum value flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) →
    ¬ CheckedSignature fragment env flags own → dissatisfy fragment env = some own

abbrev DecodedZeroDsatCompleteW := DecodedZeroDsatCompleteWIn .tapscript

theorem decodedZero_of_ambient {fragment : CoreFragment} (complete : AmbientDsatCompleteIn sc fragment) :
    DecodedZeroDsatCompleteIn sc fragment := by
  intro parent env flags pa po own value rest context nodup bounds run zero free
  exact complete parent env flags pa po own value rest context nodup bounds run (decoded_zero_false zero) free

theorem ambientDsatComplete_or_b_decoded {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (completeX : DecodedZeroDsatCompleteIn sc X) (completeY : DecodedZeroDsatCompleteWIn sc Y) :
    AmbientDsatCompleteIn sc (.or_b X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  obtain ⟨left, right, x, y, order, eq, runX, runY, zeroX, zeroY, bx, _by, _fx, _fy⟩ :=
    or_b_false_frame tx ty wx wy run falsehood
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_right _ h
  have locksX : ∀ lock ∈ X.hashLocks, lock ∈ (CoreFragment.or_b X Y).hashLocks := fun _ h => List.mem_append_left _ h
  have locksY : ∀ lock ∈ Y.hashLocks, lock ∈ (CoreFragment.or_b X Y).hashLocks := fun _ h => List.mem_append_right _ h
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have contextX := executionContext_restrict context keysX locksX inX
  have contextY := executionContext_restrict context keysY locksY inY
  have nodupXY : (X.keys ++ Y.keys).Nodup := nodup
  have boundsX : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  have boundsY : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact bx
    · exact boundsX item (List.mem_append_right _ member)
  have freeX : ¬ CheckedSignature X env flags left := fun h => free (checkedSignature_mono keysX inX h)
  have freeY : ¬ CheckedSignature Y env flags right := fun h => free (checkedSignature_mono keysY inY h)
  have dx := completeX parent env flags pa po left x (right.toInitialStack ++ rest)
    contextX (List.pairwise_append.mp nodupXY).1 boundsX runX zeroX freeX
  have dy := completeY parent env flags pa po right x y rest order
    contextY (List.pairwise_append.mp nodupXY).2.1 boundsY runY zeroY freeY
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, dx, dy, rfl⟩

theorem or_b_unsigned_guards {X Y : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_b X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_b X Y) mm) (nm : mm.nonMalleable = true)
    (s : mm.s = false) :
    cm.d = true ∧ cm.u = true ∧ mm.e = true ∧
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧
      HasType sc Y ⟨.W, cy⟩ ∧ cy.d = true ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ mx.e = true ∧ my.e = true ∧
      ((mx.s = true ∧ my.s = false) ∨ (mx.s = false ∧ my.s = true)) := by
  cases typed with
  | or_b tx dx ty dy =>
    cases mal with
    | or_b hx hy =>
      obtain ⟨nx, ny, ex, ey, signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      refine ⟨rfl, rfl, rfl, _, _, _, _, tx, dx, ty, dy, hx, hy, nx, ny, ex, ey, ?_⟩
      have split : ∀ a b : Bool, (a || b) = true → (a && b) = false →
          ((a = true ∧ b = false) ∨ (a = false ∧ b = true)) := by
        intro a b
        cases a <;> cases b <;> simp
      exact split _ _ signed s

def UnsignedNonunitZeroIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.d = true → cm.u = false → mm.e = true → mm.s = false → DecodedZeroDsatCompleteIn sc fragment

abbrev UnsignedNonunitZero := UnsignedNonunitZeroIn .tapscript

theorem decodedZeroB_of_families {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (e : mm.e = true)
    (unit : UnsignedFalseIn sc fragment) (nonunit : UnsignedNonunitZeroIn sc fragment)
    (signed : SignedDsatCompleteBIn sc fragment) : DecodedZeroDsatCompleteIn sc fragment := by
  cases s : mm.s with
  | true => exact decodedZero_of_ambient (signed cm mm typed wf mal nm d e s)
  | false =>
    cases u : cm.u with
    | true => exact decodedZero_of_ambient (unit cm mm typed wf mal nm d u e s)
    | false => exact nonunit cm mm typed wf mal nm d u e s

theorem decodedZeroW_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.W, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (e : mm.e = true)
    (unit : ∀ sub, sizeOf sub < sizeOf fragment → UnsignedFalseIn sc sub)
    (nonunit : ∀ sub, sizeOf sub < sizeOf fragment → UnsignedNonunitZeroIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf fragment → SignedDsatCompleteBIn sc sub) : DecodedZeroDsatCompleteWIn sc fragment := by
  rcases typed_W_d_children typed with ⟨child, cx, rfl, tx, deq⟩ | ⟨child, cx, rfl, tx, one, deq⟩
  · have cd : cx.d = true := deq.symm.trans d
    cases mal with
    | a hx =>
      have complete := decodedZeroB_of_families tx wf hx nm cd e
        (unit child (by simp)) (nonunit child (by simp)) (signed child (by simp))
      intro parent env flags pa po own saved top rest order context nodup bounded run zero free
      have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact complete parent env flags pa po own top rest
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun zero free
  · have cd : cx.d = true := deq.symm.trans d
    cases mal with
    | s hx =>
      have complete := decodedZeroB_of_families tx wf hx nm cd e
        (unit child (by simp)) (nonunit child (by simp)) (signed child (by simp))
      intro parent env flags pa po own saved top rest order context nodup bounded run zero free
      obtain ⟨_, childRun⟩ := s_run_child tx one wf run
      apply complete parent env flags pa po own top (saved :: rest)
        (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup _ childRun zero free
      intro item member
      apply bounded item
      simp only [List.mem_cons, List.mem_append] at member ⊢
      rcases member with member | rfl | member
      · exact Or.inr (Or.inl member)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr member)

theorem unsignedFalse_or_b (X Y : CoreFragment)
    (unit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_b X Y) → UnsignedFalseIn sc sub)
    (nonunit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_b X Y) → UnsignedNonunitZeroIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_b X Y) → SignedDsatCompleteBIn sc sub) :
    UnsignedFalseIn sc (.or_b X Y) := by
  intro cm mm typed wf mal nm _d _u _e s
  obtain ⟨_, _, _, cx, cy, mx, my, tx, dx, ty, dy, hx, hy, nx, ny, ex, ey, _split⟩ :=
    or_b_unsigned_guards typed mal nm s
  apply ambientDsatComplete_or_b_decoded tx ty wf.1 wf.2
  · exact decodedZeroB_of_families tx wf.1 hx nx dx ex
      (unit X (by simp; omega)) (nonunit X (by simp; omega)) (signed X (by simp; omega))
  · exact decodedZeroW_from_smaller_B ty wf.2 hy ny dy ey
      (fun sub smaller => unit sub (Nat.lt_trans smaller (by simp; omega)))
      (fun sub smaller => nonunit sub (Nat.lt_trans smaller (by simp; omega)))
      (fun sub smaller => signed sub (Nat.lt_trans smaller (by simp; omega)))

theorem unsignedFalse_n (child : CoreFragment) (unit : UnsignedFalseIn sc child)
    (nonunit : UnsignedNonunitZeroIn sc child) : UnsignedFalseIn sc (.n child) := by
  intro cm mm typed wf mal nm d _u e s
  cases typed with
  | @n_wrap _ cx tx =>
    cases mal with
    | n hx =>
      apply ambientDsatComplete_n_of_decodedZero
      cases cu : cx.u with
      | true => exact decodedZero_of_ambient (unit cx _ tx wf hx nm d cu e s)
      | false => exact nonunit cx _ tx wf hx nm d cu e s

end LeanMiniscript.Extraction.TapscriptRecovery.OrBFalse

namespace LeanMiniscript.Extraction.TapscriptRecovery.AndorUnsignedFalse

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat BExecution ThresholdUnit
  OrBComplete UnsignedFalse

theorem andor_type_guards {X Y Z : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, cm⟩) (d : cm.d = true) (u : cm.u = true) :
    ∃ cx cy cz, HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧ cy.u = true ∧
      HasType sc Z ⟨.B, cz⟩ ∧ cz.d = true ∧ cz.u = true := by
  generalize typeEq : (⟨.B, cm⟩ : MiniType) = ty at typed
  have baseEq := congrArg MiniType.base typeEq
  have pd : ty.mods.d = true := by rw [← typeEq]; exact d
  have pu : ty.mods.u = true := by rw [← typeEq]; exact u
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
        obtain ⟨uy, uz⟩ := Bool.and_eq_true_iff.mp pu
        exact ⟨_, cy, cz, tx, dx, ux, ty, uy, tz, pd, uz⟩

theorem andor_expressive_guards {X Y Z : CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (e : mm.e = true) :
    ∃ mx my mz, HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      HasMalleability sc Z mz ∧ mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      mz.nonMalleable = true ∧ mx.e = true ∧ mz.e = true ∧ (mx.s = true ∨ my.f = true) := by
  cases mal with
  | andor hx hy hz =>
    obtain ⟨nx, ny, nz, ex, _signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    obtain ⟨ez, guard⟩ := Bool.and_eq_true_iff.mp e
    exact ⟨_, _, _, hx, hy, hz, nx, ny, nz, ex, ez, Bool.or_eq_true_iff.mp guard⟩

theorem andor_unsigned_guards {X Y Z : CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (e : mm.e = true) (s : mm.s = false) :
    ∃ mx my mz, HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      HasMalleability sc Z mz ∧ mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      mz.nonMalleable = true ∧ mx.e = true ∧ mz.e = true ∧
      ((mx.s = true ∧ mz.s = false) ∨
       (mx.s = false ∧ my.f = true ∧
        ((my.s = true ∧ mz.s = false) ∨ (my.s = false ∧ mz.s = true)))) := by
  cases mal with
  | andor hx hy hz =>
    obtain ⟨nx, ny, nz, ex, signed⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    obtain ⟨ez, guard⟩ := Bool.and_eq_true_iff.mp e
    refine ⟨_, _, _, hx, hy, hz, nx, ny, nz, ex, ez, ?_⟩
    have split : ∀ a b c f : Bool, ((a || b) || c) = true →
        (a || f) = true → (c && (a || b)) = false →
        ((a = true ∧ c = false) ∨
         (a = false ∧ f = true ∧ ((b = true ∧ c = false) ∨ (b = false ∧ c = true)))) := by
      intro a b c f
      cases a <;> cases b <;> cases c <;> cases f <;> simp
    exact split _ _ _ _ signed guard s

theorem andor_dsat_selector {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx my mz : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (hz : HasMalleability sc Z mz) (nx : mx.nonMalleable = true) (nz : mz.nonMalleable = true)
    (ex : mx.e = true) (ez : mz.e = true) (guard : mx.s = true ∨ my.f = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  have raw := unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env)
    (expressive_rawUnsigned wz tz hz nz ez env)
  apply rawUnsigned_select_signed_eq raw
  rcases guard with sx | fy
  · exact ((malleabilityCandidateSound env wx tx hx).signedSat sx).combine_left.markNonCanonical
  · exact ((malleabilityCandidateSound env wy ty hy).forcedDsat fy).combine_right.markNonCanonical

theorem andor_dsat_selector_expressive {X Y Z : CoreFragment} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (e : mm.e = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  obtain ⟨cx, cy, cz, tx, _dx, _ux, ty, tz⟩ := andor_B_typed_children typed
  obtain ⟨mx, my, mz, hx, hy, hz, nx, _ny, nz, ex, ez, guard⟩ := andor_expressive_guards mal nm e
  exact andor_dsat_selector tx ty tz wf.1 wf.2.1 wf.2.2.1 hx hy hz nx nz ex ez guard env

theorem andor_false_active {X Y Z parent : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {resultTop : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (exclude : mx.s = true ∨ AmbientForcedFalseIn sc Y)
    (context : ExecutionContextIn sc parent (.andor X Y Z) env flags pa po own)
    (nodup : (CoreFragment.andor X Y Z).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.andor X Y Z)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (resultTop :: rest) [])) (resultFalse : castToBool resultTop = false)
    (free : ¬ CheckedSignature (.andor X Y Z) env flags own) :
    ∃ left right top, own = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (top :: (right.toInitialStack ++ rest)) []) ∧ castToBool top = false ∧
      Eval (compile Z) (right.toInitialStack ++ rest) [] flags env.txCtx (.success (resultTop :: rest) []) := by
  rcases andor_run_B_frame tx ty tz wx wy wz run with active | ⟨left, right, top, eq, runX, truth, runY⟩
  · exact active
  · subst own
    have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
      fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
    have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
      fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have ccX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have ccY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have all : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    rcases exclude with sx | forcedY
    · exact (free (checkedSignature_mono keysX inX (signed_consumption_of_malleability wx tx hx sx
        (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left top
          (right.toInitialStack ++ rest) ccX all runX truth)))).elim
    · have ndY := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).2.1
      have boundY : ∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize :=
        fun item h => all item (List.mem_append_right _ h)
      exact (free (checkedSignature_mono keysY inY
        (forcedY parent env flags pa po right resultTop rest ccY ndY boundY runY resultFalse))).elim

theorem ambientDsatComplete_andor {X Y Z : CoreFragment} {cx cy cz : CorrectnessModifiers}
    {mx : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (tz : HasType sc Z ⟨.B, cz⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc) (wz : Z.WellFormed sc)
    (hx : HasMalleability sc X mx) (nx : mx.nonMalleable = true)
    (selector : ∀ env, (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat)
    (completeX : AmbientDsatCompleteIn sc X) (completeZ : AmbientDsatCompleteIn sc Z)
    (exclude : mx.s = true ∨ AmbientForcedFalseIn sc Y) : AmbientDsatCompleteIn sc (.andor X Y Z) := by
  intro parent env flags pa po own resultTop rest context nodup bounded run resultFalse free
  obtain ⟨left, right, top, eq, runX, falseX, runZ⟩ :=
    andor_false_active tx ty tz wx wy wz hx nx exclude context nodup bounded run resultFalse free
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
  have dz := completeZ parent env flags pa po right resultTop rest ccZ ndZ boundZ runZ resultFalse absentZ
  change (satisfactionCandidates (.andor X Y Z) env).dsat.usableWitness? = _
  rw [selector env]
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, dx, dz, rfl⟩

def ForcedUnitBIn (sc : ScriptContext) (signed : Bool) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.u = true → mm.f = true → mm.s = signed → AmbientForcedFalseIn sc fragment

abbrev ForcedUnitB := ForcedUnitBIn .tapscript

theorem unsignedForcedNu_of_unit {fragment : CoreFragment} (forced : ForcedUnitBIn sc false fragment) :
    UnsignedForcedNuIn sc fragment := by
  intro cm mm typed wf mal nm _n u f s
  exact forced cm mm typed wf mal nm u f s

theorem unsignedFalse_andor (X Y Z : CoreFragment)
    (unit : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → UnsignedFalseIn sc sub)
    (signed : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → SignedDsatCompleteBIn sc sub)
    (forcedSigned : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → ForcedUnitBIn sc true sub)
    (forcedUnsigned : ∀ sub, sizeOf sub < sizeOf (CoreFragment.andor X Y Z) → ForcedUnitBIn sc false sub) :
    UnsignedFalseIn sc (.andor X Y Z) := by
  intro cm mm typed wf mal nm d u e s
  obtain ⟨cx, cy, cz, tx, dx, ux, ty, uy, tz, dz, uz⟩ := andor_type_guards typed d u
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex, ez, split⟩ := andor_unsigned_guards mal nm e s
  have completeX := conditionFalse_of_unsigned_signed (unit X (by simp; omega))
    (signed X (by simp; omega)) cx mx tx wf.1 hx nx dx ux ex
  have completeZ := conditionFalse_of_unsigned_signed (unit Z (by simp; omega))
    (signed Z (by simp; omega)) cz mz tz wf.2.2.1 hz nz dz uz ez
  apply ambientDsatComplete_andor tx ty tz wf.1 wf.2.1 wf.2.2.1 hx nx
    (andor_dsat_selector_expressive typed wf mal nm e) completeX completeZ
  rcases split with ⟨sx, _sz⟩ | ⟨_sx, fy, branch⟩
  · exact Or.inl sx
  · apply Or.inr
    rcases branch with ⟨sy, _sz⟩ | ⟨sy, _sz⟩
    · exact forcedSigned Y (by simp; omega) cy my ty wf.2.1 hy ny uy fy sy
    · exact forcedUnsigned Y (by simp; omega) cy my ty wf.2.1 hy ny uy fy sy

end LeanMiniscript.Extraction.TapscriptRecovery.AndorUnsignedFalse

namespace LeanMiniscript.Extraction.TapscriptRecovery.UnsignedOrI

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat ForcedK SignedDsat OrIDsat
  CompoundKDsat OrBComplete UnsignedFalse OrBFalse AndorUnsignedFalse

theorem forcedSignedUnit (fragment : CoreFragment) : ForcedUnitBIn sc true fragment := by
  intro cm mm typed wf mal nm _u f s
  exact uniform_signedForcedB fragment cm mm typed wf mal nm s f

theorem or_i_unsigned_guards {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_i X Y) mm)
    (nm : mm.nonMalleable = true) (u : cm.u = true) (e : mm.e = true) (s : mm.s = false) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ HasType sc Y ⟨.B, cy⟩ ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ cx.u = true ∧ cy.u = true ∧
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
        obtain ⟨ux, uy⟩ := Bool.and_eq_true_iff.mp
          ((congrArg (fun t : MiniType => t.mods.u) eq).symm.trans u)
        cases mal with
        | @or_i X Y mx my hx hy =>
          obtain ⟨nx, ny, atLeastOne⟩ := (boolAnd3_eq_true _ _ _).mp nm
          have signedness : (mx.s = true ∧ my.s = false) ∨ (mx.s = false ∧ my.s = true) := by
            cases sx : mx.s <;> cases sy : my.s <;> simp_all
          refine ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, ux, uy, signedness, ?_⟩
          rcases Bool.or_eq_true_iff.mp e with left | right
          · obtain ⟨ex, fy⟩ := Bool.and_eq_true_iff.mp left
            exact Or.inl ⟨expressive_implies_d tx hx ex, ex, fy⟩
          · obtain ⟨ey, fx⟩ := Bool.and_eq_true_iff.mp right
            exact Or.inr ⟨expressive_implies_d ty hy ey, ey, fx⟩

theorem or_i_false_children {X Y parent : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (context : ExecutionContextIn sc parent (.or_i X Y) env flags pa po own)
    (nodup : (CoreFragment.or_i X Y).keys.Nodup)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.or_i X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false)
    (free : ¬ CheckedSignature (.or_i X Y) env flags own) :
    (∃ active, own = active ++ [trueElement] ∧
      ExecutionContextIn sc parent X env flags pa po active ∧ X.keys.Nodup ∧
      (∀ item ∈ active.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) ∧
      Eval (compile X) (active.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = false ∧ ¬ CheckedSignature X env flags active) ∨
    (∃ active, own = active ++ [falseElement] ∧
      ExecutionContextIn sc parent Y env flags pa po active ∧ Y.keys.Nodup ∧
      (∀ item ∈ active.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) ∧
      Eval (compile Y) (active.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) ∧
      castToBool top = false ∧ ¬ CheckedSignature Y env flags active) := by
  rcases or_i_run_B tx ty wx wy context.rules run with
    ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have keys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_left _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [trueElement] :=
      fun _ h => List.mem_append_left _ h
    exact Or.inl ⟨active, rfl,
      executionContext_restrict context keys (fun _ h => List.mem_append_left _ h) inside,
      (List.pairwise_append.mp nodup).1, bounded_without_selector bounded, childRun, falsehood,
      fun evidence => free (checkedSignature_mono keys inside evidence)⟩
  · subst own
    have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys :=
      fun _ h => List.mem_append_right _ h
    have inside : ∀ item ∈ active, item ∈ active ++ [falseElement] :=
      fun _ h => List.mem_append_left _ h
    exact Or.inr ⟨active, rfl,
      executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inside,
      (List.pairwise_append.mp nodup).2.1, bounded_without_selector bounded, childRun, falsehood,
      fun evidence => free (checkedSignature_mono keys inside evidence)⟩

theorem or_i_left_usable_iff {X Y : CoreFragment} {env : SatEnv} {own : Witness}
    (raw : RawUnsigned (satisfactionCandidates X env).dsat)
    (forced : (satisfactionCandidates Y env).dsat.Signed) :
    dissatisfy (.or_i X Y) env = some own ↔
      ∃ active, dissatisfy X env = some active ∧ own = active ++ [trueElement] := by
  change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = _ ↔ _
  rw [dsat_or_i_left_eq raw forced]
  exact CandidateResult.withSelector_usableWitness_iff

theorem or_i_right_usable_iff {X Y : CoreFragment} {env : SatEnv} {own : Witness}
    (forced : (satisfactionCandidates X env).dsat.Signed)
    (raw : RawUnsigned (satisfactionCandidates Y env).dsat) :
    dissatisfy (.or_i X Y) env = some own ↔
      ∃ active, dissatisfy Y env = some active ∧ own = active ++ [falseElement] := by
  change (satisfactionCandidates (.or_i X Y) env).dsat.usableWitness? = _ ↔ _
  rw [dsat_or_i_right_eq forced raw]
  exact CandidateResult.withSelector_usableWitness_iff

theorem or_i_left_false_complete {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (raw : ∀ env, RawUnsigned (satisfactionCandidates X env).dsat)
    (signed : ∀ env, (satisfactionCandidates Y env).dsat.Signed)
    (completeX : AmbientDsatCompleteIn sc X) (forcedY : AmbientForcedFalseIn sc Y) :
    AmbientDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  rcases or_i_false_children tx ty wx wy context nodup bounded run falsehood free with
    ⟨active, eq, ctx, nd, bound, childRun, childFalse, absent⟩ |
    ⟨active, _eq, ctx, nd, bound, childRun, childFalse, absent⟩
  · exact (or_i_left_usable_iff (raw env) (signed env)).mpr
      ⟨active, completeX parent env flags pa po active top rest ctx nd bound childRun childFalse absent, eq⟩
  · exact (absent (forcedY parent env flags pa po active top rest ctx nd bound childRun childFalse)).elim

theorem or_i_right_false_complete {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (signed : ∀ env, (satisfactionCandidates X env).dsat.Signed)
    (raw : ∀ env, RawUnsigned (satisfactionCandidates Y env).dsat)
    (forcedX : AmbientForcedFalseIn sc X) (completeY : AmbientDsatCompleteIn sc Y) :
    AmbientDsatCompleteIn sc (.or_i X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  rcases or_i_false_children tx ty wx wy context nodup bounded run falsehood free with
    ⟨active, _eq, ctx, nd, bound, childRun, childFalse, absent⟩ |
    ⟨active, eq, ctx, nd, bound, childRun, childFalse, absent⟩
  · exact (absent (forcedX parent env flags pa po active top rest ctx nd bound childRun childFalse)).elim
  · exact (or_i_right_usable_iff (signed env) (raw env)).mpr
      ⟨active, completeY parent env flags pa po active top rest ctx nd bound childRun childFalse absent, eq⟩

theorem forcedUnit_of_unsigned {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc fragment ⟨.B, cm⟩)
    (wf : fragment.WellFormed sc) (mal : HasMalleability sc fragment mm)
    (nm : mm.nonMalleable = true) (u : cm.u = true) (f : mm.f = true)
    (unsigned : ForcedUnitBIn sc false fragment) : AmbientForcedFalseIn sc fragment := by
  cases s : mm.s with
  | false => exact unsigned cm mm typed wf mal nm u f s
  | true => exact forcedSignedUnit fragment cm mm typed wf mal nm u f s

theorem unsignedFalse_or_i (X Y : CoreFragment)
    (unit : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → UnsignedFalseIn sc child)
    (signed : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedDsatCompleteBIn sc child)
    (forced : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → ForcedUnitBIn sc false child) :
    UnsignedFalseIn sc (.or_i X Y) := by
  intro cm mm typed wf mal nm _d u e s
  obtain ⟨cx, cy, mx, my, tx, ty, hx, hy, nx, ny, ux, uy, _signedness, choice⟩ :=
    or_i_unsigned_guards typed mal nm u e s
  rcases choice with ⟨dx, ex, fy⟩ | ⟨dy, ey, fx⟩
  · exact or_i_left_false_complete tx ty wf.1 wf.2
      (expressive_rawUnsigned wf.1 tx hx nx ex)
      (fun env => (malleabilityCandidateSound env wf.2 ty hy).forcedDsat fy)
      (conditionFalse_of_unsigned_signed (unit X (by simp; omega))
        (signed X (by simp; omega)) cx mx tx wf.1 hx nx dx ux ex)
      (forcedUnit_of_unsigned ty wf.2 hy ny uy fy (forced Y (by simp; omega)))
  · exact or_i_right_false_complete tx ty wf.1 wf.2
      (fun env => (malleabilityCandidateSound env wf.1 tx hx).forcedDsat fx)
      (expressive_rawUnsigned wf.2 ty hy ny ey)
      (forcedUnit_of_unsigned tx wf.1 hx nx ux fx (forced X (by simp; omega)))
      (conditionFalse_of_unsigned_signed (unit Y (by simp; omega))
        (signed Y (by simp; omega)) cy my ty wf.2 hy ny dy uy ey)

theorem unsignedFalse_constructor_step (fragment : CoreFragment)
    (unit : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child)
    (signed : ∀ child, sizeOf child < sizeOf fragment → SignedDsatCompleteBIn sc child)
    (forced : ∀ child, sizeOf child < sizeOf fragment → ForcedUnitBIn sc false child)
    (nonunit : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    UnsignedFalseIn sc fragment := by
  intro cm mm typed wf mal nm d u e s
  cases unsigned_false_shape typed mal e s with
  | d child => exact unsignedFalse_d child cm mm typed wf mal nm d u e s
  | j child =>
    exact unsignedFalse_j child (unsignedForcedNu_of_unit (forced child (by simp)))
      cm mm typed wf mal nm d u e s
  | or_d X Y => exact unsignedFalse_or_d X Y unit signed cm mm typed wf mal nm d u e s
  | or_b X Y => exact unsignedFalse_or_b X Y unit nonunit signed cm mm typed wf mal nm d u e s
  | n child =>
    exact unsignedFalse_n child (unit child (by simp)) (nonunit child (by simp))
      cm mm typed wf mal nm d u e s
  | or_i X Y => exact unsignedFalse_or_i X Y unit signed forced cm mm typed wf mal nm d u e s
  | andor X Y Z =>
    exact unsignedFalse_andor X Y Z unit signed (fun child _ => forcedSignedUnit child) forced
      cm mm typed wf mal nm d u e s

theorem falseFamilies_from_boundaries (fragment : CoreFragment)
    (forced : ∀ child, sizeOf child < sizeOf fragment → ForcedUnitBIn sc false child)
    (nonunit : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    SignedDsatBIn sc fragment ∧ UnsignedFalseIn sc fragment := by
  have ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child ∧ UnsignedFalseIn sc child := by
    intro child smaller
    exact falseFamilies_from_boundaries child
      (fun sub bound => forced sub (Nat.lt_trans bound smaller))
      (fun sub bound => nonunit sub (Nat.lt_trans bound smaller))
  constructor
  · exact signedDsatB_constructor_step_from_unsigned fragment
      (fun child smaller => (ih child smaller).1) (fun child smaller => (ih child smaller).2)
  · exact unsignedFalse_constructor_step fragment
      (fun child smaller => (ih child smaller).2) (fun child smaller => (ih child smaller).1)
      forced nonunit
termination_by sizeOf fragment

theorem conditionFalse_from_boundaries (fragment : CoreFragment)
    (forced : ∀ child, sizeOf child < sizeOf fragment → ForcedUnitBIn sc false child)
    (nonunit : ∀ child, sizeOf child < sizeOf fragment → UnsignedNonunitZeroIn sc child) :
    VRestComplete.BConditionFalseCompleteIn sc fragment := by
  obtain ⟨signed, unsigned⟩ := falseFamilies_from_boundaries fragment forced nonunit
  exact conditionFalse_of_unsigned_signed unsigned signed

end LeanMiniscript.Extraction.TapscriptRecovery.UnsignedOrI
