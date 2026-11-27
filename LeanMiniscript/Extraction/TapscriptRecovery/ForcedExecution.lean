import LeanMiniscript.Extraction.TapscriptRecovery.UnsignedCandidates

/-! Transport execution evidence through and_b and compound K fragments. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.AndBForced

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat WBoolean ThresholdAlt ThresholdUnit

theorem byte_zero_or_sign {byte : UInt8} (h : byte.toNat % 128 = 0) :
    byte = 0 ∨ byte = 128 := by
  have bound := byte.toNat_lt
  have values : byte.toNat = 0 ∨ byte.toNat = 128 := by omega
  rcases values with h | h
  · left; exact UInt8.toNat_inj.mp h
  · right; exact UInt8.toNat_inj.mp h

theorem decoded_zero_false {operand : StackElement} {minimal : Bool}
    (decoded : decodeScriptNum operand minimal maxArithmeticScriptNumBytes = .ok 0) :
    castToBool operand = false := by
  have bound : operand.size ≤ 4 := by
    by_cases bounded : operand.size ≤ 4
    · exact bounded
    · have large : operand.size > 4 := by omega
      simp [decodeScriptNum, maxArithmeticScriptNumBytes, large] at decoded
  rcases operand with ⟨data⟩
  have repr : (⟨data⟩ : ByteArray) = ⟨data.toList.toArray⟩ := by simp
  generalize bytesEq : data.toList = bytes at repr
  rw [repr] at decoded bound ⊢
  change bytes.length ≤ 4 at bound
  change decodeScriptNum ⟨bytes.toArray⟩ minimal 4 = .ok 0 at decoded
  have magnitude : decodeUnsignedLEAux (clearScriptNumSignBit bytes) 1 = 0 := by
    simp only [decodeScriptNum] at decoded
    split at decoded <;> try contradiction
    split at decoded <;> try contradiction
    split at decoded <;> simpa using decoded
  rcases bytes with _ | ⟨a, tail⟩
  · rfl
  rcases tail with _ | ⟨b, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    rcases byte_zero_or_sign (byte := a) (by omega) with rfl | rfl <;> decide
  rcases tail with _ | ⟨c, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    have az : a = 0 := UInt8.toNat_inj.mp (show a.toNat = 0 from by omega)
    have bz : b.toNat % 128 = 0 := by omega
    subst a
    rcases byte_zero_or_sign bz with rfl | rfl <;> decide
  rcases tail with _ | ⟨d, tail⟩
  · simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    have az : a = 0 := UInt8.toNat_inj.mp (show a.toNat = 0 from by omega)
    have bz : b = 0 := UInt8.toNat_inj.mp (show b.toNat = 0 from by omega)
    have cz : c.toNat % 128 = 0 := by omega
    subst a; subst b
    rcases byte_zero_or_sign cz with rfl | rfl <;> decide
  cases tail with
  | cons _ _ => simp at bound
  | nil =>
    simp [clearScriptNumSignBit, decodeUnsignedLEAux] at magnitude
    have az : a = 0 := UInt8.toNat_inj.mp (show a.toNat = 0 from by omega)
    have bz : b = 0 := UInt8.toNat_inj.mp (show b.toNat = 0 from by omega)
    have cz : c = 0 := UInt8.toNat_inj.mp (show c.toNat = 0 from by omega)
    have dz : d.toNat % 128 = 0 := by omega
    subst a; subst b; subst c
    rcases byte_zero_or_sign dz with rfl | rfl <;> decide

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
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.W, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
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

def AmbientForcedFalseW (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContext parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = false → CheckedSignature fragment env flags own

def SignedForcedB (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType .tapscript fragment ⟨.B, cm⟩ → fragment.WellFormed .tapscript →
    HasMalleability .tapscript fragment mm → mm.nonMalleable = true →
    mm.s = true → mm.f = true → AmbientForcedFalse fragment

theorem forcedFalseW_a {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (wx : X.WellFormed .tapscript)
    (forced : AmbientForcedFalse X) : AmbientForcedFalseW (.a X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
  have childRun := uniform_savedAltTransfer X _ _ saved flags env.txCtx (a_run_child tx wx run)
  exact forced parent env flags pa po own top rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun falsehood

theorem forcedFalseW_s {X : CoreFragment} {cx : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (one : cx.o = true) (wx : X.WellFormed .tapscript)
    (forced : AmbientForcedFalse X) : AmbientForcedFalseW (.s X) := by
  intro parent env flags pa po own saved top rest order context nodup bounded run falsehood
  obtain ⟨_, childRun⟩ := s_run_child tx one wx run
  apply forced parent env flags pa po own top (saved :: rest)
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup _ childRun falsehood
  intro item member
  apply bounded item
  simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using member

theorem signedForcedW_from_smaller_B {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType .tapscript fragment ⟨.W, cm⟩)
    (wf : fragment.WellFormed .tapscript) (mal : HasMalleability .tapscript fragment mm)
    (nm : mm.nonMalleable = true) (s : mm.s = true) (f : mm.f = true)
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedForcedB child) :
    AmbientForcedFalseW fragment := by
  cases typed_W_shape typed with
  | a tx =>
    cases mal with
    | a hx => exact forcedFalseW_a tx wf (ih _ (by simp) _ _ tx wf hx nm s f)
  | s tx one =>
    cases mal with
    | s hx => exact forcedFalseW_s tx one wf (ih _ (by simp) _ _ tx wf hx nm s f)

theorem forced_and_b_of_signed_false {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx my : MalleabilityModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.W, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (hy : HasMalleability .tapscript Y my)
    (nx : mx.nonMalleable = true) (ny : my.nonMalleable = true)
    (signed : (mx.s || my.s) = true)
    (forced : ((mx.f && my.f) || (mx.s && mx.f) || (my.s && my.f)) = true)
    (falseX : mx.s = true → mx.f = true → AmbientForcedFalse X)
    (falseY : my.s = true → my.f = true → AmbientForcedFalseW Y) :
    AmbientForcedFalse (.and_b X Y) := by
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
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.and_b X Y) → SignedForcedB child) :
    SignedForcedB (.and_b X Y) := by
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

theorem n_false_child_decoded {X : CoreFragment}
    {env : SatEnv} {flags : ScriptFlags} {input rest : Stack} {top : StackElement}
    (run : Eval (compile (.n X)) input [] flags env.txCtx (.success (top :: rest) []))
    (falsehood : castToBool top = false) :
    ∃ value, Eval (compile X) input [] flags env.txCtx (.success (value :: rest) []) ∧
      castToBool value = false := by
  change Eval (compile X ++ [.op .OP_0NOTEQUAL]) input [] flags env.txCtx (.success (top :: rest) []) at run
  obtain ⟨mid, alt, childRun, normalize⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) run
  cases normalize with
  | zeroNotEqual operand value tail alt script flags ctx result decoded final =>
    cases final with
    | empty stack alt flags ctx =>
      have zero : value = 0 := by simpa using falsehood
      subst value
      exact ⟨operand, childRun, decoded_zero_false decoded⟩
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem forced_n_decoded {X : CoreFragment} (forced : AmbientForcedFalse X) :
    AmbientForcedFalse (.n X) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨value, childRun, childFalse⟩ := n_false_child_decoded run falsehood
  exact forced parent env flags pa po own value rest
    (executionContext_restrict context (active := X) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded childRun childFalse

theorem signedForcedB_n_step {X : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.n X) → SignedForcedB child) :
    SignedForcedB (.n X) := by
  intro cm mm typed wf mal nm s f
  cases typed with
  | n_wrap tx =>
    cases mal with
    | n hx => exact forced_n_decoded (ih X (by simp) _ _ tx wf hx nm s f)

end LeanMiniscript.Extraction.TapscriptRecovery.AndBForced

namespace LeanMiniscript.Extraction.TapscriptRecovery.ForcedK

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat ForcedAndV SignedV BExecution
  CompoundK ThresholdUnit ForcedMiddle AndBForced

def AmbientForcedK (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (keyBytes : StackElement) (rest : Stack),
    ExecutionContext parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (keyBytes :: rest) []) → CheckedSignature fragment env flags own

def ForcedK (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType .tapscript fragment ⟨.K, cm⟩ → fragment.WellFormed .tapscript →
    HasMalleability .tapscript fragment mm → mm.nonMalleable = true →
    mm.f = true → AmbientForcedK fragment

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
    (typed : HasType .tapscript X ⟨.K, cm⟩) (wf : X.WellFormed .tapscript)
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
    (tx : HasType .tapscript X ⟨.V, cx⟩) (ty : HasType .tapscript Y ⟨.K, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (nx : mx.nonMalleable = true)
    (route : mx.s = true ∨ AmbientForcedK Y) : AmbientForcedK (.and_v X Y) := by
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
    (tx : HasType .tapscript X ⟨.K, cx⟩) (ty : HasType .tapscript Y ⟨.K, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (forcedX : AmbientForcedK X) (forcedY : AmbientForcedK Y) : AmbientForcedK (.or_i X Y) := by
  intro parent env flags pa po own keyBytes rest context nodup bounded run
  rcases or_i_run_K tx ty wx wy context.version run with ⟨active, eq, runX⟩ | ⟨active, eq, runY⟩
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
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.K, cy⟩)
    (tz : HasType .tapscript Z ⟨.K, cz⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript) (wz : Z.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (nx : mx.nonMalleable = true)
    (forcedZ : AmbientForcedK Z) (route : mx.s = true ∨ AmbientForcedK Y) :
    AmbientForcedK (.andor X Y Z) := by
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
    (ih : ∀ child, sizeOf child < sizeOf fragment → ForcedK child) : ForcedK fragment := by
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

theorem uniform_forcedK (fragment : CoreFragment) : ForcedK fragment :=
  forcedK_constructor_step fragment (fun child _smaller => uniform_forcedK child)
termination_by sizeOf fragment

theorem forced_c_of_K {X : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType .tapscript X ⟨.K, cm⟩) (wf : X.WellFormed .tapscript)
    (forced : AmbientForcedK X) : AmbientForcedFalse (.c X) := by
  intro parent env flags pa po other top rest context nodup bounded run falsehood
  obtain ⟨own, sig, keyBytes, eq, runX, _checkFalse⟩ := c_false_run_frame typed wf run falsehood
  subst other
  have child := executionContext_restrict context (active := X)
    (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_append_right _ h)
  have bounds : ∀ item ∈ own.toInitialStack ++ (sig :: rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_cons, List.append_assoc] using bounded
  exact checkedSignature_mono (fun _ h => h) (fun _ h => List.mem_append_right _ h)
    (forced parent env flags pa po own keyBytes (sig :: rest) child nodup bounds runX)

theorem signedForcedB_c (X : CoreFragment) : SignedForcedB (.c X) := by
  intro cm mm typed wf mal nm _s f
  cases typed with
  | c_wrap tx =>
    cases mal with
    | c hx => exact forced_c_of_K tx wf (uniform_forcedK X _ _ tx wf hx nm f)

theorem signedForcedB_and_v_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.and_v X Y) → SignedForcedB child) :
    SignedForcedB (.and_v X Y) := by
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
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_d X Y) → SignedForcedB child) :
    SignedForcedB (.or_d X Y) := by
  intro cm mm typed wf mal nm s f
  cases typed with
  | or_d tx _d _u ty =>
    cases mal with
    | or_d hx hy =>
      obtain ⟨_nx, ny, _ex, _⟩ := (boolAnd4_eq_true _ _ _ _).mp nm
      obtain ⟨_sx, sy⟩ := Bool.and_eq_true_iff.mp s
      exact forced_or_d tx ty wf.1 wf.2 (ih _ (by simp; omega) _ _ ty wf.2 hy ny sy f)

theorem signedForcedB_or_i_step {X Y : CoreFragment}
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.or_i X Y) → SignedForcedB child) :
    SignedForcedB (.or_i X Y) := by
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
    (ih : ∀ child, sizeOf child < sizeOf (CoreFragment.andor X Y Z) → SignedForcedB child) :
    SignedForcedB (.andor X Y Z) := by
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
      have route : mx.s = true ∨ AmbientForcedFalse Y := by
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
    (ih : ∀ child, sizeOf child < sizeOf fragment → SignedForcedB child) :
    SignedForcedB fragment := by
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

theorem uniform_signedForcedB (fragment : CoreFragment) : SignedForcedB fragment :=
  signedForcedB_constructor_step fragment (fun child _smaller => uniform_signedForcedB child)
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.ForcedK
