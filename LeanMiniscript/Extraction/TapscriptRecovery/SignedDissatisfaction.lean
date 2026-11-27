import LeanMiniscript.Extraction.TapscriptRecovery.ForcedExecution

/-! Locate checked signatures on false executions, including multi_a slots. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.SignedDsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Active OrI OrDC Dsat BExecution
  WBoolean ThresholdAlt ThresholdUnit AndorForced AndBForced
  OrDFalseFamily ForcedK

def SignedDsatBIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType sc fragment ⟨.B, cm⟩ → fragment.WellFormed sc →
    HasMalleability sc fragment mm → mm.nonMalleable = true →
    cm.d = true → mm.e = true → mm.s = true → AmbientDsatCompleteIn sc fragment

abbrev SignedDsatB := SignedDsatBIn .tapscript

def AmbientDsatCompleteWIn (sc : ScriptContext) (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContextIn sc parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) → castToBool top = false →
    ¬ CheckedSignature fragment env flags own → dissatisfy fragment env = some own

abbrev AmbientDsatCompleteW := AmbientDsatCompleteWIn .tapscript

theorem dsatCompleteW_a {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (wx : X.WellFormed sc)
    (complete : AmbientDsatCompleteIn sc X) : AmbientDsatCompleteWIn sc (.a X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood free
  have childRun := uniform_savedAltTransfer X _ _ saved flags env.txCtx (a_run_child tx wx run)
  exact complete parent env flags pa po own top rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood free

theorem dsatCompleteW_s {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (one : cx.o = true) (wx : X.WellFormed sc)
    (complete : AmbientDsatCompleteIn sc X) : AmbientDsatCompleteWIn sc (.s X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood free
  obtain ⟨_, childRun⟩ := s_run_child tx one wx run
  apply complete parent env flags pa po own top (saved :: rest)
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup _ childRun falsehood free
  intro item member
  apply bounded item
  simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using member

theorem signedDsatW_step {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc fragment ⟨.W, cm⟩)
    (wf : fragment.WellFormed sc) (mal : HasMalleability sc fragment mm)
    (nm : mm.nonMalleable = true) (d : cm.d = true) (e : mm.e = true) (s : mm.s = true)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child) :
    AmbientDsatCompleteWIn sc fragment := by
  cases typed_W_shape typed with
  | a _tx =>
    cases typed with
    | a_wrap tx =>
      cases mal with
      | a hx => exact dsatCompleteW_a tx wf (ih _ (by simp) _ _ tx wf hx nm d e s)
  | s _tx _one =>
    cases typed with
    | s_wrap tx one =>
      cases mal with
      | s hx => exact dsatCompleteW_s tx one wf (ih _ (by simp) _ _ tx wf hx nm d e s)

theorem dsatComplete_n {X : CoreFragment} (complete : AmbientDsatCompleteIn sc X) :
    AmbientDsatCompleteIn sc (.n X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood free
  obtain ⟨value, childRun, childFalse⟩ := n_false_child_decoded run falsehood
  exact complete parent env flags pa po own value rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded childRun childFalse free

theorem signedDsatB_n_step {X : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.n X) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.n X) := by
  intro cm mm typed wf mal nm d e s
  cases typed with
  | n_wrap tx =>
    cases mal with
    | n hx => exact dsatComplete_n (ih X (by simp) _ _ tx wf hx nm d e s)

theorem signedDsatB_or_d_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_d X Y) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.or_d X Y) := by
  intro cm mm typed wf mal nm d e s
  cases typed with
  | or_d tx dx _ux ty =>
    cases mal with
    | or_d hx hy =>
      obtain ⟨nx, ny, ex, _⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      obtain ⟨sx, sy⟩ := Bool.and_eq_true_iff.mp s
      exact ambientDsatComplete_or_d tx ty wf.1 wf.2
        (ih _ (by simp; omega) _ _ tx wf.1 hx nx dx ex sx)
        (ih _ (by simp; omega) _ _ ty wf.2 hy ny d e sy)

theorem andor_Bd_children {X Y Z : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.B, cm⟩) (d : cm.d = true) :
    ∃ cx cy cz, HasType sc X ⟨.B, cx⟩ ∧ cx.d = true ∧ cx.u = true ∧
      HasType sc Y ⟨.B, cy⟩ ∧ HasType sc Z ⟨.B, cz⟩ ∧ cz.d = true := by
  generalize eq : (⟨.B, cm⟩ : MiniType) = parentType at typed
  cases typed with
  | @andor X Y Z cx tyY tyZ tx dx ux ty tz _branch sameBase =>
    have baseEq := congrArg MiniType.base eq
    cases tyY with
    | mk baseY cy =>
      change BaseType.B = baseY at baseEq
      subst baseY
      cases tyZ with
      | mk baseZ cz =>
        change BaseType.B = baseZ at sameBase
        subst baseZ
        exact ⟨cx, cy, cz, tx, dx, ux, ty, tz,
          (congrArg (fun t : MiniType => t.mods.d) eq).symm.trans d⟩

theorem signedDsatB_andor_step {X Y Z : CoreFragment}
    (ihSigned : ∀ child, sizeOf child < sizeOf (CoreFragment.andor X Y Z) → SignedDsatBIn sc child)
    (ihUnsigned : ∀ child, sizeOf child < sizeOf (CoreFragment.andor X Y Z) → UnsignedFalseIn sc child) :
    SignedDsatBIn sc (.andor X Y Z) := by
  intro cm mm typed wf mal nm d e s
  obtain ⟨cx, cy, cz, tx, dx, ux, ty, tz, dz⟩ := andor_Bd_children typed d
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex, ez, sz, choice⟩ :=
    andor_malleability_split mal nm e s
  have completeZ := ihSigned Z (by simp; omega) cz mz tz wf.2.2.1 hz nz dz ez sz
  rcases choice with sx | ⟨sx, sy, fy⟩
  · exact ambientDsatComplete_andor_signed tx ty tz wf.1 wf.2.1 wf.2.2.1 hx hz nx nz ex ez sx
      (ihSigned X (by simp; omega) cx mx tx wf.1 hx nx dx ex sx) completeZ
  · exact ambientDsatComplete_andor_forced_middle typed wf mal nm e
      (ihUnsigned X (by simp; omega) cx mx tx wf.1 hx nx dx ux ex sx) completeZ
      (uniform_signedForcedB Y cy my ty wf.2.1 hy ny sy fy)

theorem j_run_false_cases {X : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {own : Witness} {top : StackElement} {rest : Stack}
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.j X)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    own = [falseElement] ∨
      Eval (compile X) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
  change Eval ([.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
    _ _ _ _ _ at run
  generalize inputEq : own.toInitialStack ++ rest = input at run
  cases run with
  | size operand tail alt script flags ctx result inner =>
    cases inner with
    | zeroNotEqual sizeBytes value tail' alt' script' flags' ctx' result' decoded conditionalRun =>
      have bound := bounded operand (by rw [inputEq]; simp)
      have canonical := decodeScriptNum_scriptNat_of_le_maxScriptElementSize bound flags.minimalData
      rw [canonical] at decoded
      cases decoded
      have conditional : Eval ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF])
          (boolToElement ((operand.size : Int) != 0) :: operand :: tail) [] flags env.txCtx
          (.success (top :: rest) []) := by simpa [List.append_assoc] using conditionalRun
      rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditional with
        ⟨falsehood, outEq, _⟩ | ⟨_selected, childRun⟩
      · have sizeZero : operand.size = 0 := by simpa using falsehood
        have empty : operand = falseElement := ByteArray.size_eq_zero_iff.mp sizeZero
        obtain ⟨_topEq, tailEq⟩ := List.cons.inj outEq
        subst tail
        left
        have stackEq : own.toInitialStack = [falseElement] := List.append_cancel_right
          (show own.toInitialStack ++ rest = [falseElement] ++ rest by simpa [empty] using inputEq)
        exact witness_eq_singleton_of_toInitialStack stackEq
      · exact Or.inr childRun
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem signedDsatB_j (X : CoreFragment) : SignedDsatBIn sc (.j X) := by
  intro cm mm typed wf mal nm _d e s
  cases typed with
  | j_wrap tx _n =>
    cases mal with
    | j hx =>
      intro parent env flags pa po own top rest context nodup bounded run falsehood free
      rcases j_run_false_cases bounded run with eq | childRun
      · subst own
        change ((CandidateResult.usable [falseElement] false).select
          ((satisfactionCandidates X env).dsat.requireNonemptyRuntimeTop.markNonCanonical)).usableWitness? = _
        rw [rawUnsigned_select_signed_eq
          (show RawUnsigned (CandidateResult.usable [falseElement] false) from ⟨_, rfl, rfl⟩)
          ((malleabilityCandidateSound env (show X.WellFormed sc from wf) tx hx).forcedDsat e).requireNonemptyRuntimeTop.markNonCanonical]
        rfl
      · have checked := uniform_signedForcedB X _ _ tx wf hx nm s e parent env flags pa po own top rest
          (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
          nodup bounded childRun falsehood
        exact (free checked).elim

theorem boolean_single_bounds {isOr : Bool} {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] input alt flags ctx (.success (top :: rest) [])) :
    ∃ a b, input = a :: b :: rest ∧ alt = [] ∧
      a.size ≤ maxScriptElementSize ∧ b.size ≤ maxScriptElementSize := by
  cases isOr
  · change Eval [.op .OP_BOOLAND] _ _ _ _ _ at run
    cases run with
    | booland aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx =>
        obtain ⟨da, db⟩ := decode_pair_parts decoded
        exact ⟨aBytes, bBytes, rfl, rfl, WBoolean.decoded_size da, WBoolean.decoded_size db⟩
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  · change Eval [.op .OP_BOOLOR] _ _ _ _ _ at run
    cases run with
    | boolor aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx =>
        obtain ⟨da, db⟩ := decode_pair_parts decoded
        exact ⟨aBytes, bBytes, rfl, rfl, WBoolean.decoded_size da, WBoolean.decoded_size db⟩
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem boolean_order_bounds {isOr : Bool} {order : BaseWOutputOrder}
    {saved result top : StackElement} {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] (order.outputs saved result ++ tail) [] flags ctx
      (.success (top :: rest) [])) :
    tail = rest ∧ saved.size ≤ maxScriptElementSize ∧ result.size ≤ maxScriptElementSize := by
  obtain ⟨a, b, eq, _, ba, bb⟩ := boolean_single_bounds run
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append, List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, ba, bb⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, bb, ba⟩

theorem boolean_run_frame_any {isOr : Bool} {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (run : Eval (compile (booleanNode isOr X Y)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder),
      own = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs x y ++ rest) []) ∧
      x.size ≤ maxScriptElementSize ∧ y.size ≤ maxScriptElementSize := by
  have combined : Eval (compile X ++ (compile Y ++ [.op (booleanOpcode isOr)]))
      (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    cases isOr <;> simpa [booleanNode, booleanOpcode, compile, compileWithKeyHash, List.append_assoc] using run
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
  obtain ⟨rfl, bx, bySize⟩ := boolean_order_bounds opRun
  have inputEq : own.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : own = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, witnessEq, ?_, ?_, bx, bySize⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY

theorem boolean_dsat_selector_signed {isOr : Bool} {X Y : CoreFragment}
    {cx cy : CorrectnessModifiers} {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (ex : mx.e = true) (ey : my.e = true) (sx : mx.s = true) (sy : my.s = true) (env : SatEnv) :
    (satisfactionCandidates (booleanNode isOr X Y) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).dsat := by
  cases isOr with
  | true => rfl
  | false =>
    have raw := unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env)
      (expressive_rawUnsigned wy ty hy ny ey env)
    have signedY : ((satisfactionCandidates X env).dsat.combine
        (satisfactionCandidates Y env).sat).markOvercomplete.Signed :=
      ((malleabilityCandidateSound env wy ty hy).signedSat sy).combine_right.markOvercomplete
    have sel := rawUnsigned_select_signed_eq raw signedY
    change CandidateResult.select (CandidateResult.select _ _) _ = _
    rw [sel]
    exact rawUnsigned_select_signed_eq raw
      ((malleabilityCandidateSound env wx tx hx).signedSat sx).combine_left.markOvercomplete

theorem dsatComplete_boolean_signed {isOr : Bool} {X Y : CoreFragment}
    {cx cy : CorrectnessModifiers} {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.W, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (ex : mx.e = true) (ey : my.e = true) (sx : mx.s = true) (sy : my.s = true)
    (completeX : AmbientDsatCompleteIn sc X) (completeY : AmbientDsatCompleteWIn sc Y) :
    AmbientDsatCompleteIn sc (booleanNode isOr X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run _falsehood free
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by⟩ := boolean_run_frame_any tx ty wx wy run
  subst own
  have keysX : ∀ key ∈ X.keys, key ∈ (booleanNode isOr X Y).keys := by
    cases isOr <;> exact fun _ h => List.mem_append_left _ h
  have keysY : ∀ key ∈ Y.keys, key ∈ (booleanNode isOr X Y).keys := by
    cases isOr <;> exact fun _ h => List.mem_append_right _ h
  have locksX : ∀ lock ∈ X.hashLocks, lock ∈ (booleanNode isOr X Y).hashLocks := by
    cases isOr <;> exact fun _ h => List.mem_append_left _ h
  have locksY : ∀ lock ∈ Y.hashLocks, lock ∈ (booleanNode isOr X Y).hashLocks := by
    cases isOr <;> exact fun _ h => List.mem_append_right _ h
  have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have contextX := executionContext_restrict context keysX locksX inX
  have contextY := executionContext_restrict context keysY locksY inY
  have nodupXY : (X.keys ++ Y.keys).Nodup := by cases isOr <;> exact nodup
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
  have falseX : castToBool x = false := by
    cases truth : castToBool x with
    | false => rfl
    | true => exact (freeX (signed_consumption_of_malleability wx tx hx sx
        (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left x
          (right.toInitialStack ++ rest) contextX boundsX runX truth))).elim
  have falseY : castToBool y = false := by
    cases truth : castToBool y with
    | false => rfl
    | true => exact (freeY (signed_consumption_of_malleability wy ty hy sy
        (ambientExecutionW_step ty wy hy ny (fun child _ => uniform_B_execution child)
          parent env flags pa po right x y rest order contextY boundsY runY truth))).elim
  have dx := completeX parent env flags pa po left x (right.toInitialStack ++ rest)
    contextX (List.pairwise_append.mp nodupXY).1 boundsX runX falseX freeX
  have dy := completeY parent env flags pa po right x y rest order
    contextY (List.pairwise_append.mp nodupXY).2.1 boundsY runY falseY freeY
  change (satisfactionCandidates (booleanNode isOr X Y) env).dsat.usableWitness? = _
  rw [boolean_dsat_selector_signed tx ty wx wy hx hy nx ny ex ey sx sy env]
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨left, right, dx, dy, rfl⟩

theorem signedDsatB_and_b_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.and_b X Y) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.and_b X Y) := by
  intro cm mm typed wf mal nm d e _s
  cases typed with
  | and_b tx ty =>
    cases mal with
    | and_b hx hy =>
      obtain ⟨nx, ny⟩ := Bool.and_eq_true_iff.mp nm
      obtain ⟨dx, dy⟩ := Bool.and_eq_true_iff.mp d
      obtain ⟨ex, ey, sx, sy⟩ := (boolAnd4_eq_true _ _ _ _).mp e
      exact dsatComplete_boolean_signed (isOr := false) tx ty wf.1 wf.2.1 hx hy nx ny ex ey sx sy
        (ih _ (by simp; omega) _ _ tx wf.1 hx nx dx ex sx)
        (signedDsatW_step ty wf.2.1 hy ny dy ey sy
          (fun child smaller => ih child (Nat.lt_trans smaller (by simp; omega))))

theorem signedDsatB_or_b_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_b X Y) → SignedDsatBIn sc child) :
    SignedDsatBIn sc (.or_b X Y) := by
  intro cm mm typed wf mal nm _d _e s
  cases typed with
  | or_b tx dx ty dy =>
    cases mal with
    | or_b hx hy =>
      obtain ⟨nx, ny, ex, ey, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
      obtain ⟨sx, sy⟩ := Bool.and_eq_true_iff.mp s
      exact dsatComplete_boolean_signed (isOr := true) tx ty wf.1 wf.2 hx hy nx ny ex ey sx sy
        (ih _ (by simp; omega) _ _ tx wf.1 hx nx dx ex sx)
        (signedDsatW_step ty wf.2 hy ny dy ey sy
          (fun child smaller => ih child (Nat.lt_trans smaller (by simp; omega))))

theorem ifThen_minimal {body : Script} {selector : StackElement}
    {rest alt out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval ([.op .OP_IF] ++ body ++ [.op .OP_ENDIF]) (selector :: rest) alt flags ctx
      (.success out outAlt)) : minimalIfSatisfied flags ctx.sigVersion selector := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try assumption
  case upgradeableNop => simp_all [Opcode.isUpgradeableNop]
  all_goals cases resultEq

theorem d_false_witness {X : CoreFragment} {cx : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (tx : HasType sc X ⟨.V, cx⟩) (wx : X.WellFormed sc) (zero : cx.z = true)
    (version : Active.WitnessRules flags env.txCtx)
    (run : Eval (compile (.d X)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (falsehood : castToBool top = false) : own = [falseElement] := by
  have combined : Eval ([.op .OP_DUP] ++ ([.op .OP_IF] ++ compile X ++ [.op .OP_ENDIF]))
      (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    simpa [compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨mid, midAlt, dupRun, conditionalRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (.atom (by simp [NonConditional])) combined
  generalize inputEq : own.toInitialStack ++ rest = input at dupRun
  cases input with
  | nil =>
    have failed := Eval.fixedArityStackUnderflow_result
      (opcode := .OP_DUP) (required := 1) (arity := rfl) (underflow := by simp) dupRun
    contradiction
  | cons selector tail =>
    have canonical : Eval [.op .OP_DUP] (selector :: tail) [] flags env.txCtx
        (.success (selector :: selector :: tail) []) := Eval.dup selector tail [] [] flags env.txCtx _ Eval.done
    have eq := Eval.result_unique dupRun canonical
    cases eq
    have minimal := Active.minimal_selector_of_rules version (ifThen_minimal conditionalRun)
    rcases LeanMiniscript.Miniscript.Eval.ifThen_success_cases (compile_balancedControlFlow X) conditionalRun with
      ⟨selectorFalse, outputEq, _⟩ | ⟨selectorTrue, childRun⟩
    · have empty : selector = falseElement := by
        rcases minimal with empty | truth
        · exact empty
        · simp [truth, castToBool, trueElement] at selectorFalse
      obtain ⟨_topEq, tailEq⟩ := List.cons.inj outputEq
      subst tail
      have stackEq : own.toInitialStack = [falseElement] := List.append_cancel_right
        (show own.toInitialStack ++ rest = [falseElement] ++ rest by simpa [empty] using inputEq)
      exact witness_eq_singleton_of_toInitialStack stackEq
    · obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType tx wx _ _ _ _ _ childRun
      obtain ⟨args, input, matchesArgs⟩ := effect.v_inv
      have lengthZero := matchesArgs.1 zero
      have argsEmpty : args = [] := List.length_eq_zero_iff.mp lengthZero
      have topEq : selector = top := (List.cons.inj (by simpa [argsEmpty] using input)).1
      rw [topEq, falsehood] at selectorTrue
      contradiction

theorem signedDsatB_d (X : CoreFragment) : SignedDsatBIn sc (.d X) := by
  intro cm mm typed wf _mal _nm _d _e _s
  cases typed with
  | d_wrap tx zero =>
    intro parent env flags pa po own top rest context _nodup _bounded run falsehood _free
    rw [d_false_witness tx wf zero context.rules run falsehood]
    rfl

theorem signedDsat_or_i_left {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (dx : cx.d = true) (ex : mx.e = true) (sx : mx.s = true)
    (sy : my.s = true) (fy : my.f = true)
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedDsatBIn sc child) :
    AmbientDsatCompleteIn sc (.or_i X Y) :=
  ambientDsatComplete_or_i_left tx ty wx wy
    (fun env => expressive_rawUnsigned wx tx hx nx ex env)
    (fun env => (malleabilityCandidateSound env wy ty hy).forcedDsat fy)
    (ih X (by simp; omega) cx mx tx wx hx nx dx ex sx)
    (uniform_signedForcedB Y cy my ty wy hy ny sy fy)

theorem signedDsat_or_i_right {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx my : MalleabilityModifiers}
    (tx : HasType sc X ⟨.B, cx⟩) (ty : HasType sc Y ⟨.B, cy⟩)
    (wx : X.WellFormed sc) (wy : Y.WellFormed sc)
    (hx : HasMalleability sc X mx) (hy : HasMalleability sc Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (dy : cy.d = true) (ey : my.e = true) (sy : my.s = true)
    (sx : mx.s = true) (fx : mx.f = true)
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedDsatBIn sc child) :
    AmbientDsatCompleteIn sc (.or_i X Y) :=
  ambientDsatComplete_or_i_right tx ty wx wy
    (fun env => expressive_rawUnsigned wy ty hy ny ey env)
    (fun env => (malleabilityCandidateSound env wx tx hx).forcedDsat fx)
    (ih Y (by simp; omega) cy my ty wy hy ny dy ey sy)
    (uniform_signedForcedB X cx mx tx wx hx nx sx fx)

def RemainingSignedDsat : CoreFragment → Prop
  | .or_i _ _ | .c (.or_i _ _) | .c (.andor _ _ _) | .thresh _ _ | .multi_a _ _ => True
  | _ => False

theorem signedDsatB_c_step (X : CoreFragment)
    (residual : RemainingSignedDsat (.c X) → SignedDsatBIn sc (.c X)) : SignedDsatBIn sc (.c X) := by
  intro cm mm typed wf mal nm d e s
  have original := typed
  cases typed with
  | c_wrap tx =>
    cases typed_K_shape tx with
    | pk_k key => exact ambientDsatComplete_c_pk_k key
    | pk_h key => exact ambientDsatComplete_c_pk_h key
    | and_v _tx _ty =>
      cases mal with
      | c hx => cases hx; cases e
    | or_i _tx _ty => exact residual trivial _ mm original wf mal nm d e s
    | andor _tx _dx _ux _ty _tz => exact residual trivial _ mm original wf mal nm d e s

theorem signedDsatB_constructor_step (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child)
    (residual : RemainingSignedDsat fragment → SignedDsatBIn sc fragment) : SignedDsatBIn sc fragment := by
  intro cm mm typed wf mal nm d e s
  cases fragment with
  | zero => exact ambientDsatComplete_zero
  | one => cases typed; cases d
  | pk_k key => cases typed
  | pk_h key => cases typed
  | older n => cases mal; cases s
  | after n => cases mal; cases s
  | sha256 h => cases mal; cases s
  | hash256 h => cases mal; cases s
  | ripemd160 h => cases mal; cases s
  | hash160 h => cases mal; cases s
  | and_v X Y => cases mal; cases e
  | and_b X Y => exact signedDsatB_and_b_step ih cm mm typed wf mal nm d e s
  | or_b X Y => exact signedDsatB_or_b_step ih cm mm typed wf mal nm d e s
  | or_c X Y => cases typed
  | or_d X Y => exact signedDsatB_or_d_step ih cm mm typed wf mal nm d e s
  | or_i X Y => exact residual trivial cm mm typed wf mal nm d e s
  | andor X Y Z => exact signedDsatB_andor_step ih unsigned cm mm typed wf mal nm d e s
  | a X => cases typed
  | s X => cases typed
  | c X => exact signedDsatB_c_step X residual cm mm typed wf mal nm d e s
  | d X => exact signedDsatB_d X cm mm typed wf mal nm d e s
  | v X => cases typed
  | j X => exact signedDsatB_j X cm mm typed wf mal nm d e s
  | n X => exact signedDsatB_n_step ih cm mm typed wf mal nm d e s
  | multi k keys =>
    cases sc with
    | tapscript => exact wf.1.elim
    | p2wsh =>
      intro parent env flags pa po own top rest context _ _ run neg _
      exact P2WSHRecovery.multi_false wf context.modeled run neg
  | multi_a k keys => exact residual trivial cm mm typed wf mal nm d e s
  | thresh k children => exact residual trivial cm mm typed wf mal nm d e s

theorem or_i_residual_static {X Y : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (mal : HasMalleability sc (.or_i X Y) mm)
    (nm : mm.nonMalleable = true) (d : cm.d = true) (e : mm.e = true) (s : mm.s = true) :
    ∃ cx cy mx my, HasType sc X ⟨.B, cx⟩ ∧ HasType sc Y ⟨.B, cy⟩ ∧
      HasMalleability sc X mx ∧ HasMalleability sc Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧
      (cx.d = true ∨ cy.d = true) ∧ mx.s = true ∧ my.s = true ∧
      ((mx.e = true ∧ my.f = true) ∨ (my.e = true ∧ mx.f = true)) := by
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
        have childrenD := Bool.or_eq_true_iff.mp ((congrArg (fun t : MiniType => t.mods.d) eq).symm.trans d)
        cases mal with
        | @or_i X Y mx my hx hy =>
          obtain ⟨nx, ny, _⟩ := (boolAnd3_eq_true _ _ _).mp nm
          obtain ⟨sx, sy⟩ := Bool.and_eq_true_iff.mp s
          have choice : (mx.e = true ∧ my.f = true) ∨ (my.e = true ∧ mx.f = true) := by
            simpa only [Bool.or_eq_true, Bool.and_eq_true] using e
          exact ⟨cx, cy, _, _, tx, ty, hx, hy, nx, ny, childrenD, sx, sy, choice⟩

end LeanMiniscript.Extraction.TapscriptRecovery.SignedDsat

namespace LeanMiniscript.Extraction.TapscriptRecovery.MultiADsat

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction MultiA OrI OrDC AndorForced SignedDsat

theorem multiA_tail_balanced (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
    exact .append (.append (.atom (by simp [NonConditional]))
      (.atom (by simp [NonConditional]))) ih

theorem multiA_finish_comparison
    {k : Nat} {firstKey : PubKey} {keys : List PubKey}
    {flags : ScriptFlags} {txCtx : TxContext} {input rest altStack : Stack}
    {sig top : StackElement} {finalAlt : Stack}
    {headCount : Nat} {rest' : Stack}
    (version : txCtx.sigVersion = .tapscript)
    (threshold : validThreshold k (keys.length + 1))
    (keyBound : keys.length + 1 ≤ MAX_PUBKEYS_PER_MULTI_A)
    (stackEq : input = sig :: rest')
    (headSlot : sigSlot flags txCtx sig firstKey)
    (headVC : (if sig = falseElement then 0 else 1) = headCount)
    (inner : Eval (compileCheckSigAddTail keys ++ [.pushNum ↑k, .op .OP_NUMEQUAL])
      (scriptNat headCount :: rest') altStack flags txCtx (.success (top :: rest) finalAlt)) :
    ∃ sigs, input = sigs ++ rest ∧ sigs.length = keys.length + 1 ∧
      (∀ slot ∈ List.zip sigs (firstKey :: keys), sigSlot flags txCtx slot.1 slot.2) ∧
      top = boolToElement ((k : Int) == (validCount sigs : Int)) := by
  have maxBound : MAX_PUBKEYS_PER_MULTI_A < maxArithmeticScriptNatExclusive := by decide
  obtain ⟨_thresholdLow, thresholdHigh⟩ := threshold
  have headBound : headCount ≤ 1 := by
    rw [← headVC]
    by_cases empty : sig = falseElement <;> simp [empty]
  obtain ⟨mid, midAlt, tailRun, finalRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
      (multiA_tail_balanced keys) inner
  obtain ⟨tailArgs, tailRest, restEq, finalEq, lengthEq, slots⟩ :=
    checkSigAddTail_slots version (by omega) tailRun
  rw [finalEq] at finalRun
  cases finalRun with
  | pushNum n rest0 script0 altStack0 flags0 ctx0 result0 inner3 =>
    cases inner3 with
    | numequal aBytes bBytes a b rest2 script2 altStack2 flags2 ctx2 result2 decodePair inner4 =>
      cases inner4 with
      | empty lastStack lastAlt lastFlags lastCtx =>
        have vcLe : validCount tailArgs ≤ tailArgs.length := List.length_filter_le _ _
        have decodeBelow : decodeScriptNum
            (scriptNat (headCount + validCount tailArgs)) flags.minimalData
            maxArithmeticScriptNumBytes = .ok ((headCount + validCount tailArgs : Nat) : Int) :=
          decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
        have decodeTop : decodeScriptNum (scriptNum (↑k : Int)) flags.minimalData
            maxArithmeticScriptNumBytes = .ok (k : Int) :=
          decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
        unfold decodeBinaryScriptNums at decodePair
        simp only [decodeBelow, decodeTop, bind, Except.bind, pure, Except.pure] at decodePair
        cases decodePair
        have vcTotal : validCount (sig :: tailArgs) = headCount + validCount tailArgs := by
          rw [← headVC]
          by_cases empty : sig = falseElement
          · rw [empty]
            simp only [validCount]
            rw [List.filter_cons_of_neg (a := falseElement) (by decide)]
            simp
          · simp only [validCount]
            rw [List.filter_cons_of_pos (a := sig) (by simp [empty])]
            simp [empty, Nat.add_comm]
        refine ⟨sig :: tailArgs, ?_, ?_, ?_, ?_⟩
        · rw [stackEq, restEq]
          simp
        · simp [lengthEq]
        · intro slot member
          simp only [List.zip_cons_cons, List.mem_cons] at member
          rcases member with head | tail
          · rw [head]
            exact headSlot
          · exact slots slot tail
        · rw [vcTotal]
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
      simp [Opcode.isUpgradeableNop] at upgradable

theorem multiA_run_comparison
    (k : Nat) (keys : List PubKey)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (flags : ScriptFlags) (txCtx : TxContext)
    {input rest altStack finalAlt : Stack} {top : StackElement}
    (version : txCtx.sigVersion = .tapscript)
    (executed : Eval (compile (.multi_a k keys)) input altStack flags txCtx
      (.success (top :: rest) finalAlt)) :
    ∃ sigs, input = sigs ++ rest ∧ sigs.length = keys.length ∧
      (∀ slot ∈ List.zip sigs keys, sigSlot flags txCtx slot.1 slot.2) ∧
      top = boolToElement ((k : Int) == (validCount sigs : Int)) := by
  have sigVersion : txCtx.sigVersion = .tapscript := version
  generalize stackEq : input = stack at executed
  cases keys with
  | nil =>
    obtain ⟨one, zero⟩ := threshold
    simp only [List.length_nil] at zero
    omega
  | cons firstKey keys =>
    have scriptEq : compile (.multi_a k (firstKey :: keys)) =
        ([.pushData firstKey.bytes, .op .OP_CHECKSIG] ++ compileCheckSigAddTail keys) ++
          [.pushNum ↑k, .op .OP_NUMEQUAL] := by
      simp [compile, compileWithKeyHash, compileCheckSigAdd]
    rw [scriptEq] at executed
    cases executed with
    | pushData data rest initStack altStack flags ctx result inner =>
      cases inner with
      | checksig_success pubkey sig rest' script' altStack' flags' ctx' result' sigOK inner2 =>
        have accOne : (trueElement : StackElement) = scriptNat 1 := rfl
        rw [accOne] at inner2
        rw [← stackEq]
        exact multiA_finish_comparison sigVersion threshold keyCount stackEq
          (Or.inr sigOK)
          (by simp [MultiA.nonempty_of_checkSigWithEncoding_true sigVersion sigOK]) inner2
      | checksig_failure pubkey sig rest' script' altStack' flags' ctx' result' sigFalse inner2 =>
        have accZero : (falseElement : StackElement) = scriptNat 0 := rfl
        rw [accZero] at inner2
        rw [← stackEq]
        exact multiA_finish_comparison sigVersion threshold keyCount stackEq
          (Or.inl (eq_falseElement_of_checkSigWithEncoding_false sigVersion sigFalse))
          (by simp [eq_falseElement_of_checkSigWithEncoding_false sigVersion sigFalse]) inner2
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
        simp [Opcode.isUpgradeableNop] at upgradable

theorem slots_eq_replicate {flags : ScriptFlags} {ctx : TxContext}
    {sigs : List StackElement} {keys : List PubKey}
    (lengths : sigs.length = keys.length)
    (slots : ∀ slot ∈ List.zip sigs keys, sigSlot flags ctx slot.1 slot.2)
    (free : ∀ sig ∈ sigs, ∀ key ∈ keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key.bytes ≠ .ok true) :
    sigs = List.replicate keys.length falseElement := by
  induction keys generalizing sigs with
  | nil => simpa using List.eq_nil_of_length_eq_zero lengths
  | cons key keys ih =>
    cases sigs with
    | nil => simp at lengths
    | cons sig sigs =>
      have first : sigSlot flags ctx sig key := slots (sig, key) (by simp)
      have empty : sig = falseElement := first.resolve_right
        (free sig (by simp) key (by simp))
      have tail := ih (by simpa using lengths)
        (fun slot member => slots slot (by simp [member]))
        (fun slot member k km => free slot (by simp [member]) k (by simp [km]))
      simp [empty, tail, List.replicate_succ]

theorem multiA_unsigned_witness {k : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {rest alt finalAlt : Stack}
    {top : StackElement} (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (version : env.txCtx.sigVersion = .tapscript)
    (run : Eval (compile (.multi_a k keys)) (own.toInitialStack ++ rest) alt flags env.txCtx
      (.success (top :: rest) finalAlt))
    (free : ¬ CheckedSignature (.multi_a k keys) env flags own) :
    own = List.replicate keys.length falseElement ∧ top = falseElement := by
  obtain ⟨sigs, shape, lengths, slots, comparison⟩ :=
    multiA_run_comparison k keys threshold keyCount flags env.txCtx version run
  have initEq : own.toInitialStack = sigs := List.append_cancel_right shape
  have empty : sigs = List.replicate keys.length falseElement :=
    slots_eq_replicate lengths slots (by
      intro sig member key km checked
      apply free
      refine ⟨sig, ?_, key, ?_, checked⟩
      · rw [← initEq] at member
        simpa [Witness.toInitialStack] using member
      · exact km)
  have ownEq : own = List.replicate keys.length falseElement := by
    have reversed := congrArg List.reverse (initEq.trans empty)
    simpa [Witness.toInitialStack] using reversed
  refine ⟨ownEq, ?_⟩
  have countZero : validCount sigs = 0 := by simp [empty, validCount]
  rw [countZero] at comparison
  have positive : k ≠ 0 := by have := threshold.1; omega
  simpa [positive, boolToElement] using comparison

theorem multiA_candidate_guard {k : Nat} {keys : List PubKey}
    (wf : (CoreFragment.multi_a k keys).WellFormed sc) :
    candidateThresholdValid k keys.length := by
  obtain ⟨positive, upper⟩ : validThreshold k keys.length := wf.2.1
  have keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A := wf.2.2.1
  have maxBound : MAX_PUBKEYS_PER_MULTI_A < maxArithmeticScriptNatExclusive := by decide
  exact ⟨by omega, upper, ArithmeticScriptNatSafe.of_lt (by omega)⟩

theorem multiA_dsat_projection {k : Nat} {keys : List PubKey} {env : SatEnv}
    (valid : candidateThresholdValid k keys.length) :
    dissatisfy (.multi_a k keys) env = some (List.replicate keys.length falseElement) := by
  simp [dissatisfy, multiACandidates, valid, CandidateResult.usableWitness?, CandidateResult.usable]

theorem ambientDsatComplete_multi_a {k : Nat} {keys : List PubKey}
    (wf : (CoreFragment.multi_a k keys).WellFormed sc) :
    AmbientDsatCompleteIn sc (.multi_a k keys) := by
  intro parent env flags pa po own top rest context _nodup _bounded run _falsehood free
  obtain rfl : sc = .tapscript := by cases sc <;> first | rfl | exact wf.1.elim
  have actual := multiA_unsigned_witness wf.2.1 wf.2.2.1 context.version run free
  rw [actual.1]
  exact multiA_dsat_projection (multiA_candidate_guard wf)

theorem signedDsatB_multi_a (k : Nat) (keys : List PubKey) : SignedDsatBIn sc (.multi_a k keys) := by
  intro _cm _mm _typed wf _mal _nm _d _e _s
  exact ambientDsatComplete_multi_a wf

def RemainingSignedDsatAfterMultiA : CoreFragment → Prop
  | .or_i _ _ | .c (.or_i _ _) | .c (.andor _ _ _) | .thresh _ _ => True
  | _ => False

theorem signedDsatB_constructor_step_after_multi_a (fragment : CoreFragment)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedDsatBIn sc child)
    (unsigned : ∀ child, sizeOf child < sizeOf fragment → UnsignedFalseIn sc child)
    (residual : RemainingSignedDsatAfterMultiA fragment → SignedDsatBIn sc fragment) :
    SignedDsatBIn sc fragment := by
  apply signedDsatB_constructor_step fragment ih unsigned
  intro remaining
  cases fragment <;> try { exact signedDsatB_multi_a _ _ } <;> try { exact residual trivial }
  case c X => cases X <;> first | exact residual trivial | exact False.elim remaining
  all_goals exact False.elim remaining

end LeanMiniscript.Extraction.TapscriptRecovery.MultiADsat
