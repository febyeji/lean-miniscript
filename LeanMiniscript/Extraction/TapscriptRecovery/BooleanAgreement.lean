import LeanMiniscript.Extraction.TapscriptRecovery.RowAgreement

/-! Recover the selected canonical witness across boolean operators and wrappers. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.BChoiceMaterial

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OriginCounts SlotLocal CompositeRows

theorem checkedMaterial_canonical_root {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} (path : SlotPath child root) (nodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable) :
    CheckedMaterial child root env flags pa po := by
  intro own expected context canonical sig member key keyMem checked
  have scope : TapscriptWitness.SignatureScope root child env pa po :=
    ⟨context.sound, context.keySizes, context.childKeys, context.thirdParty⟩
  exact scope.signature_in_satisfaction context.version path nodup rootCanonical context.canonical canonical
    (context.consumedIn sig member) keyMem checked

theorem checked_or_i_canonical_root {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.or_i X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_i X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_i X Y) root) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ih : SmallerCheckedB (.or_i X Y) root env flags pa po) :
    CheckedTrueRowAgreementB (.or_i X Y) root env flags pa po :=
  checked_or_i_of_material typed wf mal nm path (checkedMaterial_canonical_root path rootNodup rootCanonical) ih

end LeanMiniscript.Extraction.TapscriptRecovery.BChoiceMaterial

namespace LeanMiniscript.Extraction.TapscriptRecovery.BooleanRows

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport OrI OrDC WBoolean ThresholdAlt
  ThresholdUnit OriginCounts SlotLocal CompositeRows VRows VConditions
  BChoiceMaterial DsatMaterial OrBFalse OrBComplete FalseUniform
  BWrappers

def TrueRowAgreementW (child root : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) : Prop :=
  ∀ own expected saved top rest (order : BaseWOutputOrder),
    ExecutionContext root child env flags pa po own → child.keys.Nodup →
    satisfy child env = some expected →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile child) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = true → own = expected

theorem agree_W_from_smaller_B {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript child ⟨.W, cm⟩) (wf : child.WellFormed .tapscript)
    (mal : HasMalleability .tapscript child mm) (nm : mm.nonMalleable = true)
    (path : SlotPath child root) (ih : SmallerCheckedB child root env flags pa po) :
    TrueRowAgreementW child root env flags pa po := by
  cases typed_W_shape typed with
  | @a body cx tx =>
    cases mal with
    | a hx =>
      have checked := ih body (by simp) cx _ tx wf hx nm (path_trans (.wrapper .a .here) path)
      intro own expected saved top rest order context nodup canonical bounded run truth
      have childRun := uniform_savedAltTransfer body _ _ saved flags env.txCtx (a_run_child tx wf run)
      exact agree_B tx wf hx nm checked
        (executionContext_restrict context (active := body) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup canonical (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun truth
  | @s body cx tx one =>
    cases mal with
    | s hx =>
      have checked := ih body (by simp) cx _ tx wf hx nm (path_trans (.wrapper .s .here) path)
      intro own expected saved top rest order context nodup canonical bounded run truth
      obtain ⟨_singleton, childRun⟩ := s_run_child tx one wf run
      apply agree_B tx wf hx nm checked
        (executionContext_restrict context (active := body) (fun _ h => h) (fun _ h => h) (fun _ h => h))
        nodup canonical _ childRun truth
      intro item member
      apply bounded item
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using member

theorem checked_and_b_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.and_b X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.and_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.and_b X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.and_b X Y) root)
    (ih : SmallerCheckedB (.and_b X Y) root env flags pa po) :
    CheckedTrueRowAgreementB (.and_b X Y) root env flags pa po := by
  obtain ⟨cx, cy, mx, my, tx, ty, wx, wy, hx, hy, nx, ny⟩ := and_b_static typed wf mal nm
  have ix := ih X (by simp; omega) cx mx tx wx hx nx (path_trans (.left .and_b .here) path)
  have iy := agree_W_from_smaller_B ty wy hy ny (path_trans (.right .and_b .here) path)
    (env := env) (flags := flags) (pa := pa) (po := po) (by
      intro sub small ci mi ti wi hi ni subPath
      exact ih sub (Nat.lt_trans small (by simp; omega)) ci mi ti wi hi ni subPath)
  intro own expected top rest context nodup canonical bounded run truth _checked
  obtain ⟨sx, sy, satX, satY, expectedEq⟩ := CandidateResult.combine_usableWitness_iff.mp canonical
  obtain ⟨left, right, x, y, order, eq, runX, runY, bx, _by, actual⟩ :=
    boolean_run_frame (isOr := false) tx ty wx wy run truth
  subst own
  obtain ⟨ccx, ccy, boundX, boundY⟩ := split_contexts context
    (X := X) (Y := Y) (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) bounded
  have ex := agree_B tx wx hx nx ix ccx (List.pairwise_append.mp nodup).1 satX boundX runX actual.1
  have ey := iy right sy x y rest order ccy (List.pairwise_append.mp nodup).2.1 satY
    (by intro item h; rcases List.mem_cons.mp h with rfl | h; exact bx; exact boundY item h) runY actual.2
  rw [expectedEq, ex, ey]
  rfl

theorem boolean_single_decoded {isOr : Bool} {input alt rest : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] input alt flags ctx (.success (top :: rest) [])) :
    ∃ a b na nb, input = a :: b :: rest ∧ alt = [] ∧
      decodeScriptNum a flags.minimalData maxArithmeticScriptNumBytes = .ok na ∧
      decodeScriptNum b flags.minimalData maxArithmeticScriptNumBytes = .ok nb := by
  cases isOr
  · change Eval [.op .OP_BOOLAND] _ _ _ _ _ at run
    cases run with
    | booland aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx => exact ⟨_, _, _, _, rfl, rfl, decode_pair_parts decoded⟩
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable
  · change Eval [.op .OP_BOOLOR] _ _ _ _ _ at run
    cases run with
    | boolor aBytes bBytes a b tail script alt flags ctx result decoded final =>
      cases final with
      | empty stack alt flags ctx => exact ⟨_, _, _, _, rfl, rfl, decode_pair_parts decoded⟩
    | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem boolean_order_decoded {isOr : Bool} {order : BaseWOutputOrder}
    {saved result top : StackElement} {tail rest : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op (booleanOpcode isOr)] (order.outputs saved result ++ tail) [] flags ctx
      (.success (top :: rest) [])) :
    ∃ ns nr, decodeScriptNum saved flags.minimalData maxArithmeticScriptNumBytes = .ok ns ∧
      decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok nr := by
  obtain ⟨a, b, na, nb, eq, _, da, db⟩ := boolean_single_decoded run
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append, List.nil_append,
    List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨na, nb, da, db⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨nb, na, db, da⟩

theorem boolean_run_frame_decoded {isOr : Bool} {X Y : CoreFragment} {mx my : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {consumed : Witness} {top : StackElement} {rest : Stack}
    (typedX : HasType .tapscript X ⟨.B, mx⟩) (typedY : HasType .tapscript Y ⟨.W, my⟩)
    (wfX : X.WellFormed .tapscript) (wfY : Y.WellFormed .tapscript)
    (run : Eval (compile (booleanNode isOr X Y)) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) :
    ∃ (left right : Witness) (x y : StackElement) (order : BaseWOutputOrder) (nx ny : Int),
      consumed = right ++ left ∧
      Eval (compile X) (left.toInitialStack ++ (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (x :: (right.toInitialStack ++ rest)) []) ∧
      Eval (compile Y) (x :: (right.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs x y ++ rest) []) ∧
      x.size ≤ maxScriptElementSize ∧ y.size ≤ maxScriptElementSize ∧ BooleanTruth isOr x y ∧
      decodeScriptNum x flags.minimalData maxArithmeticScriptNumBytes = .ok nx ∧
      decodeScriptNum y flags.minimalData maxArithmeticScriptNumBytes = .ok ny := by
  have combined : Eval (compile X ++ (compile Y ++ [.op (booleanOpcode isOr)]))
      (consumed.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) := by
    cases isOr <;> simpa [booleanNode, booleanOpcode, compile, compileWithKeyHash, List.append_assoc] using run
  obtain ⟨midX, altX, runX, tailRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow X) combined
  obtain ⟨altEqX, effectX⟩ := refinedBaseTypeGuarantee_of_hasType typedX wfX _ _ _ _ _ runX
  cases altEqX
  obtain ⟨midY, altY, runY, opRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow Y) tailRun
  obtain ⟨altEqY, effectY⟩ := refinedBaseTypeGuarantee_of_hasType typedY wfY _ _ _ _ _ runY
  cases altEqY
  obtain ⟨argsX, tailX, x, inputX, outputX, _⟩ := effectX.b_inv
  rw [outputX] at effectY runY
  obtain ⟨argsY, tailY, saved, y, order, inputY, outputY⟩ := effectY.w_inv
  obtain ⟨rfl, tailEq⟩ := List.cons.inj inputY
  rw [outputY] at opRun runY
  obtain ⟨nx, ny, dx, dy⟩ := boolean_order_decoded opRun
  obtain ⟨rfl, bx, bySize, boolTruth⟩ := boolean_order_truth opRun truth
  have inputEq : consumed.toInitialStack = argsX ++ argsY := by
    apply List.append_cancel_right
    simpa [tailEq, List.append_assoc] using inputX
  have witnessEq : consumed = argsY.reverse ++ argsX.reverse := by
    simpa [Witness.toInitialStack] using congrArg List.reverse inputEq
  refine ⟨argsX.reverse, argsY.reverse, x, y, order, nx, ny, witnessEq, ?_, ?_, bx, bySize, boolTruth, dx, dy⟩
  · rw [inputX, outputX, tailEq] at runX
    simpa [Witness.toInitialStack] using runX
  · rw [tailEq] at runY
    simpa [Witness.toInitialStack] using runY

theorem or_b_candidate_rows {X Y : CoreFragment} {env : SatEnv} {expected : Witness}
    (canonical : satisfy (.or_b X Y) env = some expected) :
    (∃ sx dy, expected = dy ++ sx ∧ satisfy X env = some sx ∧ dissatisfy Y env = some dy ∧
      ¬ RawUnsigned ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Y env).sat)) ∨
    (∃ dx sy, expected = sy ++ dx ∧ dissatisfy X env = some dx ∧ satisfy Y env = some sy ∧
      ¬ RawUnsigned ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).dsat)) := by
  rcases CandidateResult.select_usableWitness_cases canonical with selected | unusable
  · rcases select_usable_rows selected with ⟨left, excluded⟩ | ⟨right, excluded⟩
    · obtain ⟨sx, dy, cx, cy, eq⟩ := CandidateResult.combine_usableWitness_iff.mp left
      exact Or.inl ⟨sx, dy, eq, cx, cy, excluded⟩
    · obtain ⟨dx, sy, cx, cy, eq⟩ := CandidateResult.combine_usableWitness_iff.mp right
      exact Or.inr ⟨dx, sy, eq, cx, cy, excluded⟩
  · cases resultEq : (satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat <;>
      simp [resultEq, CandidateResult.markOvercomplete, CandidateResult.usableWitness?, SatisfactionCandidate.markOvercomplete] at unusable

theorem dsat_sources_any {condition target : CoreFragment} {env : SatEnv} {actual dsat : Witness}
    {ty : MiniType} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript condition ty) (wf : condition.WellFormed .tapscript)
    (mal : HasMalleability .tapscript condition mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sound : env.Sound) (sizes : ∀ key ∈ condition.keys, key.bytes.size = 32)
    (canonical : dissatisfy condition env = some dsat) : Items (LocalSlot target env actual []) dsat := by
  intro item member
  have small := expressive_dsat_items_small typed wf mal nm e sound sizes canonical item member
  exact localSlot_short (by omega)

theorem checked_or_b_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.or_b X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_b X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_b X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_b X Y) root) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ih : SmallerCheckedB (.or_b X Y) root env flags pa po) :
    CheckedTrueRowAgreementB (.or_b X Y) root env flags pa po := by
  obtain ⟨cx, cy, mx, my, tx, dx, ty, dy, wx, wy, hx, hy, nx, ny, ex, ey, _signed⟩ :=
    or_b_static typed wf mal nm
  have material := checkedMaterial_canonical_root path rootNodup rootCanonical
    (flags := flags) (pa := pa) (po := po)
  have ix := ih X (by simp; omega) cx mx tx wx hx nx (path_trans (.left .or_b .here) path)
  have iy := agree_W_from_smaller_B ty wy hy ny (path_trans (.right .or_b .here) path)
    (env := env) (flags := flags) (pa := pa) (po := po) (by
      intro sub small ci mi ti wi hi ni subPath
      exact ih sub (Nat.lt_trans small (by simp; omega)) ci mi ti wi hi ni subPath)
  have falseX := decodedZero_complete_of_typed tx wx hx nx dx ex
  have falseY := decodedZeroW_from_smaller_B ty wy hy ny dy ey
    (fun sub _ => uniform_unsignedFalse sub) (fun sub _ => uniform_nonunit sub)
    (fun sub _ => uniform_signedDsatCompleteB sub)
  intro own expected top rest context nodup canonical bounded run truth _checked
  obtain ⟨left, right, x, y, order, numX, numY, ownEq, runX, runY, bx, _by, actual, decX, decY⟩ :=
    boolean_run_frame_decoded (isOr := true) tx ty wx wy run truth
  subst own
  have kx : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_left _ h
  have ky : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_b X Y).keys := fun _ h => List.mem_append_right _ h
  obtain ⟨ccx, ccy, boundX, boundY⟩ := split_contexts context kx ky
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) bounded
  have boundW : ∀ item ∈ x :: (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    intro item h
    rcases List.mem_cons.mp h with rfl | h
    · exact bx
    · exact boundY item h
  have ndx := (List.pairwise_append.mp nodup).1
  have ndy := (List.pairwise_append.mp nodup).2.1
  have separate := (List.pairwise_append.mp nodup).2.2
  rcases or_b_candidate_rows canonical with ⟨sx, dy, eq, satX, dsatY, excluded⟩ | ⟨dx, sy, eq, dsatX, satY, excluded⟩
  · have sources : Items (LocalSlot Y env right []) expected := by
      rw [eq]
      exact items_combine
        ((foreign_pair ccy (fun key member => context.childKeys key (kx key member))
          (fun key hk other ho => Ne.symm (separate other ho key hk))).1 sx satX)
        (dsat_sources_any ty wy hy ny ey context.sound
          (fun key member => context.keySizes key (context.childKeys key (ky key member))) dsatY)
    have freeY := free_of_sources material context canonical ky (fun _ h => List.mem_append_left _ h) sources
    have falsehood : castToBool y = false := by
      cases h : castToBool y
      · rfl
      · exact (excluded (unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env)
          (unsigned_W_run ty wy hy ny ccy boundW runY h freeY))).elim
    have trueX : castToBool x = true := by simpa [BooleanTruth, falsehood] using actual
    have zeroY : decodeScriptNum y flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) := by
      simpa [decode_false_zero4 decY falsehood] using decY
    have actualY := falseY root env flags pa po right x y rest order ccy ndy boundW runY zeroY freeY
    have eqY : right = dy := Option.some.inj (actualY.symm.trans dsatY)
    have eqX := agree_B tx wx hx nx ix ccx ndx satX boundX runX trueX
    rw [eq, eqX, eqY]
  · have freeX := fallback_noChecked material context ccx tx wx hx nx ex canonical eq
      dsatX satY kx ky (fun _ h => List.mem_append_right _ h) separate
    have falsehood : castToBool x = false := by
      cases h : castToBool x
      · rfl
      · have raw := execution_without_checked_signature
          (uniform_B_execution X cx mx tx wx hx nx root env flags pa po left x (right.toInitialStack ++ rest)
            ccx boundX runX h) freeX
        exact (excluded (unsigned_combine raw (expressive_rawUnsigned wy ty hy ny ey env))).elim
    have trueY : castToBool y = true := by simpa [BooleanTruth, falsehood] using actual
    have zeroX : decodeScriptNum x flags.minimalData maxArithmeticScriptNumBytes = .ok (0 : Int) := by
      simpa [decode_false_zero4 decX falsehood] using decX
    have actualX := falseX root env flags pa po left x (right.toInitialStack ++ rest) ccx ndx boundX runX zeroX freeX
    have eqX : left = dx := Option.some.inj (actualX.symm.trans dsatX)
    have eqY := iy right sy x y rest order ccy ndy satY boundW runY trueY
    rw [eq, eqX, eqY]

def BPendingWithoutBoolean (fragment : CoreFragment) : Prop :=
  fragment.keys ≠ [] ∧ match fragment with
    | .c (.pk_k _) | .c (.pk_h _) | .multi_a _ _ | .and_v _ _ | .or_i _ _ | .and_b _ _ | .or_b _ _ | .j _ | .n _ => False
    | _ => True

theorem checkedB_without_boolean_step {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootWF : root.WellFormed .tapscript) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB fragment root env flags pa po)
    (ihV : SmallerCheckedV fragment root env flags pa po)
    (rest : BPendingWithoutBoolean fragment → CheckedTrueRowAgreementB fragment root env flags pa po) :
    CheckedTrueRowAgreementB fragment root env flags pa po := by
  cases fragment with
  | or_i X Y => exact checked_or_i_canonical_root typed wf mal nm path rootNodup rootCanonical ihB
  | and_b X Y => exact checked_and_b_step typed wf mal nm path ihB
  | or_b X Y => exact checked_or_b_step typed wf mal nm path rootNodup rootCanonical ihB
  | c child =>
    apply checkedB_step typed wf mal nm path rootWF rootNodup ihB ihV
    intro pending
    apply rest
    cases child <;> simp_all [BPendingWithoutBoolean, BPending]
  | _ =>
    apply checkedB_step typed wf mal nm path rootWF rootNodup ihB ihV
    intro pending
    apply rest
    simp_all [BPendingWithoutBoolean, BPending]

end LeanMiniscript.Extraction.TapscriptRecovery.BooleanRows

namespace LeanMiniscript.Extraction.TapscriptRecovery.BConditions

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport OrI OrDC SignedV BExecution
  ThresholdUnit OriginCounts SlotLocal CompositeRows VConditions
  BChoiceMaterial BooleanRows

theorem checkedB_or_d_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.or_d X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_d X Y).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_d X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_d X Y) root) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedB (.or_d X Y) root env flags pa po)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable) :
    CheckedTrueRowAgreementB (.or_d X Y) root env flags pa po := by
  have material := checkedMaterial_canonical_root path rootNodup rootCanonical (env := env) (flags := flags) (pa := pa) (po := po)
  obtain ⟨mx, my, hx, hy, nx, ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := true) mal nm
  cases typed_B_shape typed with
  | or_d tx d u ty =>
    have ix := ihB X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .or_d .here) path)
    have iy := ihB Y (by simp; omega) _ _ ty wf.2 hy ny (path_trans (.right .or_d .here) path)
    have rawD := expressive_rawUnsigned wf.1 tx hx nx ex env
    intro own expected resultTop rest context nodup canonical bounded run resultTruth _checked
    have kx : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_left _ h
    have ky : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_right _ h
    have lx : ∀ lock ∈ X.hashLocks, lock ∈ (CoreFragment.or_d X Y).hashLocks := fun _ h => List.mem_append_left _ h
    have ly : ∀ lock ∈ Y.hashLocks, lock ∈ (CoreFragment.or_d X Y).hashLocks := fun _ h => List.mem_append_right _ h
    have ndx := (List.pairwise_append.mp nodup).1
    have ndy := (List.pairwise_append.mp nodup).2.1
    have separate := (List.pairwise_append.mp nodup).2.2
    rcases shortCircuit_run_frame (keep := true) (top := resultTop) tx ty wf.1 wf.2 run with
        ⟨value, runX, truth⟩ | ⟨ox, oy, value, ownEq, runX, falsehood, runY⟩
    · have ccx := executionContext_restrict context kx lx (fun _ h => h)
      have evidence := uniform_B_execution X _ _ tx wf.1 hx nx root env flags pa po own value rest ccx bounded runX truth
      rcases shortCircuit_candidate_cases true canonical with ⟨satX, _⟩ | ⟨dx, sy, expectedEq, dsatX, satY, excluded⟩
      · exact agree_B tx wf.1 hx nx ix ccx ndx satX bounded runX truth
      · have sources : Items (LocalSlot X env own []) expected := by
          rw [expectedEq]
          exact items_combine (dsat_sources tx wf.1 hx nx ex context.sound
            (fun key member => context.keySizes key (context.childKeys key (kx key member))) dsatX)
            ((foreign_pair ccx (fun key member => context.childKeys key (ky key member)) separate).1 sy satY)
        have free := free_of_sources material context canonical kx (fun _ h => h) sources
        exact evidence.elim (fun raw => (excluded raw).elim) (fun sig => (free sig).elim)
    · subst own
      obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts context kx ky lx ly bounded
      have evidenceY := uniform_B_execution Y _ _ ty wf.2 hy ny
        root env flags pa po oy resultTop rest ccy byBound runY resultTruth
      rcases shortCircuit_candidate_cases true canonical with ⟨satX, excluded⟩ | ⟨dx, sy, expectedEq, dsatX, satY, _⟩
      · have sources : Items (LocalSlot Y env oy []) expected :=
          (foreign_pair ccy (fun key member => context.childKeys key (kx key member))
            (fun key hk other ho => Ne.symm (separate other ho key hk))).1 expected satX
        have freeY := free_of_sources material context canonical ky (fun _ h => List.mem_append_left _ h) sources
        exact evidenceY.elim (fun raw => (excluded (unsigned_combine rawD raw)).elim)
          (fun sig => (freeY sig).elim)
      · have freeX := fallback_noChecked material context ccx tx wf.1 hx nx ex canonical expectedEq
          dsatX satY kx ky (fun _ h => List.mem_append_right _ h) separate
        have eqX := false_agreement tx wf.1 hx nx d u ex ccx ndx dsatX bx runX falsehood freeX
        have eqY := agree_B ty wf.2 hy ny iy ccy ndy satY byBound runY resultTruth
        rw [expectedEq, eqX, eqY]
  | remaining impossible => cases impossible

theorem checkedB_andor_step {X Y Z root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.andor X Y Z) ⟨.B, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.andor X Y Z) root) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedB (.andor X Y Z) root env flags pa po)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable) :
    CheckedTrueRowAgreementB (.andor X Y Z) root env flags pa po := by
  have material := checkedMaterial_canonical_root path rootNodup rootCanonical (env := env) (flags := flags) (pa := pa) (po := po)
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
  cases typed_B_shape typed with
  | andor tx d u ty tz =>
    have ix := ihB X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.condition .here) path)
    have iy := ihB Y (by simp; omega) _ _ ty wf.2.1 hy ny (path_trans (.thenBranch .here) path)
    have iz := ihB Z (by simp; omega) _ _ tz wf.2.2.1 hz nz (path_trans (.elseBranch .here) path)
    have rawD := expressive_rawUnsigned wf.1 tx hx nx ex env
    intro own expected resultTop rest context nodup canonical bounded run resultTruth _checked
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
    rcases andor_run_B_frame tx ty tz wf.1 wf.2.1 wf.2.2.1 run with
        ⟨ox, oz, value, ownEq, runX, falsehood, runZ⟩ | ⟨ox, oy, value, ownEq, runX, truth, runY⟩
    · subst own
      obtain ⟨ccx, ccz, bx, bz⟩ := split_contexts context kx kz lx lz bounded
      have evidenceZ := uniform_B_execution Z _ _ tz wf.2.2.1 hz nz
        root env flags pa po oz resultTop rest ccz bz runZ resultTruth
      rcases andor_candidate_rows canonical with
          ⟨sx, sy, expectedEq, satX, satY, excluded⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, _⟩
      · have sourcesZ : Items (LocalSlot Z env oz []) expected := by
          rw [expectedEq]
          exact items_combine
            ((foreign_pair ccz (fun key member => context.childKeys key (kx key member))
              (fun key hk other ho => Ne.symm (sepXZ other ho key hk))).1 sx satX)
            ((foreign_pair ccz (fun key member => context.childKeys key (ky key member))
              (fun key hk other ho => Ne.symm (sepYZ other ho key hk))).1 sy satY)
        have freeZ := free_of_sources material context canonical kz (fun _ h => List.mem_append_left _ h) sourcesZ
        exact evidenceZ.elim (fun raw => (excluded (unsigned_combine rawD raw)).elim)
          (fun sig => (freeZ sig).elim)
      · have freeX := fallback_noChecked material context ccx tx wf.1 hx nx ex canonical expectedEq
          dsatX satZ kx kz (fun _ h => List.mem_append_right _ h) sepXZ
        have eqX := false_agreement tx wf.1 hx nx d u ex ccx ndx dsatX bx runX falsehood freeX
        have eqZ := agree_B tz wf.2.2.1 hz nz iz ccz ndz satZ bz runZ resultTruth
        rw [expectedEq, eqX, eqZ]
    · subst own
      obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts context kx ky lx ly bounded
      have evidenceX := uniform_B_execution X _ _ tx wf.1 hx nx root env flags pa po ox value
        (oy.toInitialStack ++ rest) ccx bx runX truth
      have evidenceY := uniform_B_execution Y _ _ ty wf.2.1 hy ny
        root env flags pa po oy resultTop rest ccy byBound runY resultTruth
      rcases andor_candidate_rows canonical with
          ⟨sx, sy, expectedEq, satX, satY, _⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, excluded⟩
      · have eqX := agree_B tx wf.1 hx nx ix ccx ndx satX bx runX truth
        have eqY := agree_B ty wf.2.1 hy ny iy ccy ndy satY byBound runY resultTruth
        rw [expectedEq, eqX, eqY]
      · have sourcesX : Items (LocalSlot X env ox []) expected := by
          rw [expectedEq]
          exact items_combine (dsat_sources tx wf.1 hx nx ex context.sound
            (fun key member => context.keySizes key (context.childKeys key (kx key member))) dsatX)
            ((foreign_pair ccx (fun key member => context.childKeys key (kz key member)) sepXZ).1 sz satZ)
        have sourcesY : Items (LocalSlot Y env oy []) expected := by
          rw [expectedEq]
          exact items_combine (dsat_sources tx wf.1 hx nx ex context.sound
            (fun key member => context.keySizes key (context.childKeys key (kx key member))) dsatX)
            ((foreign_pair ccy (fun key member => context.childKeys key (kz key member)) sepYZ).1 sz satZ)
        have freeX := free_of_sources material context canonical kx (fun _ h => List.mem_append_right _ h) sourcesX
        have freeY := free_of_sources material context canonical ky (fun _ h => List.mem_append_left _ h) sourcesY
        rcases evidenceX with rawX | sigX
        · rcases evidenceY with rawY | sigY
          · exact (excluded (unsigned_combine rawX rawY)).elim
          · exact (freeY sigY).elim
        · exact (freeX sigX).elim
  | remaining impossible => cases impossible

def BPendingWithoutConditions (fragment : CoreFragment) : Prop :=
  fragment.keys ≠ [] ∧ match fragment with
    | .c (.pk_k _) | .c (.pk_h _) | .multi_a _ _ | .and_v _ _ | .or_i _ _ | .and_b _ _ | .or_b _ _ | .j _ | .n _ | .or_d _ _ | .andor _ _ _ => False
    | _ => True

theorem checkedB_without_conditions_step {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootWF : root.WellFormed .tapscript) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB fragment root env flags pa po)
    (ihV : SmallerCheckedV fragment root env flags pa po)
    (rest : BPendingWithoutConditions fragment → CheckedTrueRowAgreementB fragment root env flags pa po) :
    CheckedTrueRowAgreementB fragment root env flags pa po := by
  cases fragment with
  | or_d X Y => exact checkedB_or_d_step typed wf mal nm path rootNodup ihB rootCanonical
  | andor X Y Z => exact checkedB_andor_step typed wf mal nm path rootNodup ihB rootCanonical
  | c child =>
    apply checkedB_without_boolean_step typed wf mal nm path rootWF rootNodup rootCanonical ihB ihV
    intro pending
    apply rest
    cases child <;> simp_all [BPendingWithoutConditions, BPendingWithoutBoolean]
  | _ =>
    apply checkedB_without_boolean_step typed wf mal nm path rootWF rootNodup rootCanonical ihB ihV
    intro pending
    apply rest
    simp_all [BPendingWithoutConditions, BPendingWithoutBoolean]

end LeanMiniscript.Extraction.TapscriptRecovery.BConditions

namespace LeanMiniscript.Extraction.TapscriptRecovery.DAgreement

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI BWrappers ThresholdUnit UnsignedComplete
  ZeroComplete OriginCounts SlotLocal CompositeRows VRows BConditions

theorem d_true_zero_frame {child : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript child ⟨.V, cm⟩) (wf : child.WellFormed .tapscript)
    (zero : cm.z = true) (version : env.txCtx.sigVersion = .tapscript)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.d child)) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    top = trueElement ∧ own = [trueElement] ∧
      Eval (compile child) (trueElement :: rest) [] flags env.txCtx (.success (trueElement :: rest) []) := by
  have topEq := unit_d typed wf zero env flags _ rest top version bounded run truth
  obtain ⟨active, ownEq, childRun⟩ := d_run_frame typed wf run truth
  have empty := zero_V_consumed typed wf zero childRun
  refine ⟨topEq, ?_, ?_⟩
  · simpa [empty, topEq] using ownEq
  · simpa [empty, topEq, Witness.toInitialStack] using childRun

theorem d_true_child_projection {child root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript child ⟨.V, cm⟩) (wf : child.WellFormed .tapscript)
    (mal : HasMalleability .tapscript child mm) (nm : mm.nonMalleable = true) (zero : cm.z = true)
    (context : ExecutionContext root (.d child) env flags pa po own)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.d child)) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    top = trueElement ∧ own = [trueElement] ∧ satisfy child env = some [] ∧
      (satisfactionCandidates child env).dsat = .impossible ∧
      ExecutionContext root child env flags pa po [] ∧
      (∀ item ∈ trueElement :: rest, item.size ≤ maxScriptElementSize) ∧
      Eval (compile child) (trueElement :: rest) [] flags env.txCtx (.success (trueElement :: rest) []) := by
  obtain ⟨topEq, ownEq, childRun⟩ := d_true_zero_frame typed wf zero context.version bounded run truth
  have cc : ExecutionContext root child env flags pa po [] :=
    executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h)
      (by intro item member; cases member)
  have bound : ∀ item ∈ trueElement :: rest, item.size ≤ maxScriptElementSize := by
    simpa [ownEq, Witness.toInitialStack] using bounded
  have selected := zero_V_success_projection typed wf mal nm zero cc bound childRun
  exact ⟨topEq, ownEq, selected.2, typedV_dsat_impossible typed env, cc, bound, childRun⟩

theorem d_true_available {child root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript (.d child) ⟨.B, cm⟩) (wf : (CoreFragment.d child).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.d child) mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContext root (.d child) env flags pa po own)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.d child)) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    top = trueElement ∧ own = [trueElement] ∧ satisfy (.d child) env = some own := by
  obtain ⟨cx, mx, tx, zx, wx, hx, nx⟩ := d_static typed wf mal nm
  obtain ⟨topEq, ownEq, selected, _dsat, _cc, _bound, _childRun⟩ :=
    d_true_child_projection tx wx hx nx zx context bounded run truth
  refine ⟨topEq, ownEq, ?_⟩
  apply CandidateResult.withSelector_usableWitness_iff.mpr
  exact ⟨[], selected, by simpa [Witness.withSelector] using ownEq⟩

theorem d_true_agreement {child root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po own expected : Witness}
    {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript (.d child) ⟨.B, cm⟩) (wf : (CoreFragment.d child).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.d child) mm) (nm : mm.nonMalleable = true)
    (context : ExecutionContext root (.d child) env flags pa po own)
    (canonical : satisfy (.d child) env = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.d child)) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) : own = expected := by
  have selected := (d_true_available typed wf mal nm context bounded run truth).2.2
  exact Option.some.inj (selected.symm.trans canonical)

theorem checked_d_step {child root : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {pa po : Witness}
    (typed : HasType .tapscript (.d child) ⟨.B, cm⟩) (wf : (CoreFragment.d child).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.d child) mm) (nm : mm.nonMalleable = true) :
    CheckedTrueRowAgreementB (.d child) root env flags pa po := by
  intro own expected top rest context _nodup canonical bounded run truth _checked
  exact d_true_agreement typed wf mal nm context canonical bounded run truth

def BPendingWithoutD (fragment : CoreFragment) : Prop :=
  fragment.keys ≠ [] ∧ match fragment with
    | .c (.pk_k _) | .c (.pk_h _) | .multi_a _ _ | .and_v _ _ | .or_i _ _ | .and_b _ _ | .or_b _ _ | .j _ | .n _ | .or_d _ _ | .andor _ _ _ | .d _ => False
    | _ => True

theorem checkedB_without_d_step {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootWF : root.WellFormed .tapscript) (rootNodup : root.keys.Nodup)
    (rootCanonical : (satisfactionCandidates root env).sat.CanonicalWhenUsable)
    (ihB : SmallerCheckedB fragment root env flags pa po)
    (ihV : SmallerCheckedV fragment root env flags pa po)
    (rest : BPendingWithoutD fragment → CheckedTrueRowAgreementB fragment root env flags pa po) :
    CheckedTrueRowAgreementB fragment root env flags pa po := by
  cases fragment with
  | d child => exact checked_d_step typed wf mal nm
  | c child =>
    apply checkedB_without_conditions_step typed wf mal nm path rootWF rootNodup rootCanonical ihB ihV
    intro pending
    apply rest
    cases child <;> simp_all [BPendingWithoutD, BPendingWithoutConditions]
  | _ =>
    apply checkedB_without_conditions_step typed wf mal nm path rootWF rootNodup rootCanonical ihB ihV
    intro pending
    apply rest
    simp_all [BPendingWithoutD, BPendingWithoutConditions]

end LeanMiniscript.Extraction.TapscriptRecovery.DAgreement
