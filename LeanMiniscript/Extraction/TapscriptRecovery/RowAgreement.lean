import LeanMiniscript.Extraction.TapscriptRecovery.SignatureSlots

/-! Prove witness agreement for compound B and V rows from smaller child frames. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

variable {sc : LeanMiniscript.Miniscript.ScriptContext}

namespace LeanMiniscript.Extraction.TapscriptRecovery.CompositeRows

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport Active OrI ForcedAndV BExecution
  ThresholdUnit DsatMaterial SuccessUniform OriginCounts SlotLocal

theorem path_trans {target middle root : CoreFragment}
    (inner : SlotPath target middle) (outer : SlotPath middle root) : SlotPath target root := by
  induction outer with
  | here => exact inner
  | wrapper op _ ih => exact .wrapper op ih
  | left op _ ih => exact .left op ih
  | right op _ ih => exact .right op ih
  | condition _ ih => exact .condition ih
  | thenBranch _ ih => exact .thenBranch ih
  | elseBranch _ ih => exact .elseBranch ih
  | threshold k before after _ ih => exact .threshold k before after ih

def CheckedTrueRowAgreementVIn (sc : ScriptContext) (child root : CoreFragment) (env : SatEnv)
    (flags : ScriptFlags) (pa po : Witness) : Prop :=
  ∀ own expected rest, ExecutionContextIn sc root child env flags pa po own → child.keys.Nodup →
    satisfy child env = some expected →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) →
    CheckedSignature child env flags own → own = expected

abbrev CheckedTrueRowAgreementV := CheckedTrueRowAgreementVIn .tapscript

theorem agree_B {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} {top : StackElement} {rest : Stack}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc child ⟨.B, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true)
    (checked : CheckedTrueRowAgreementBIn sc child root env flags pa po)
    (context : ExecutionContextIn sc root child env flags pa po own) (nodup : child.keys.Nodup)
    (canonical : satisfy child env = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) : own = expected := by
  by_cases sig : CheckedSignature child env flags own
  · exact checked own expected top rest context nodup canonical bounded run truth sig
  · exact Option.some.inj ((actual_unsigned_B_satisfy typed wf mal nm context nodup bounded run truth sig).symm.trans canonical)

theorem agree_V {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} {rest : Stack} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc child ⟨.V, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true)
    (checked : CheckedTrueRowAgreementVIn sc child root env flags pa po)
    (context : ExecutionContextIn sc root child env flags pa po own) (nodup : child.keys.Nodup)
    (canonical : satisfy child env = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) : own = expected := by
  by_cases sig : CheckedSignature child env flags own
  · exact checked own expected rest context nodup canonical bounded run sig
  · exact Option.some.inj ((actual_unsigned_V_satisfy typed wf mal nm context nodup bounded run sig).symm.trans canonical)

theorem checkedV_verify {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} (checked : CheckedTrueRowAgreementBIn sc child root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.v child) root env flags pa po := by
  intro own expected rest context nodup canonical bounded run sig
  have cc := executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  have unfused := LeanMiniscript.Miniscript.Eval.compileVerify_success_inverse (compile_balancedControlFlow child) run
  obtain ⟨mid, alt, childRun, verifyRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow child) unfused
  cases verifyRun with
  | verify_success top rest' script alt flags ctx result truth final =>
    cases final with
    | empty stack alt flags ctx =>
      exact checked own expected top rest cc nodup (by simpa using canonical) bounded childRun truth sig
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem checkedV_verify_step {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.v child) ⟨.V, cm⟩) (wf : (CoreFragment.v child).WellFormed sc)
    (mal : HasMalleability sc (.v child) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.v child) root)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.v child) → ∀ cx mx,
      HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
      CheckedTrueRowAgreementBIn sc sub root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.v child) root env flags pa po := by
  cases typed with
  | v_wrap tx => cases mal with
    | v hx => exact checkedV_verify (ih child (by simp) _ _ tx wf hx nm
        (path_trans (.wrapper .v .here) path))

theorem checked_and_v_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.and_v X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.and_v X Y).WellFormed sc)
    (mal : HasMalleability sc (.and_v X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.and_v X Y) root)
    (ihB : ∀ sub, sizeOf sub < sizeOf (CoreFragment.and_v X Y) → ∀ cx mx,
      HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
      CheckedTrueRowAgreementBIn sc sub root env flags pa po)
    (ihV : ∀ sub, sizeOf sub < sizeOf (CoreFragment.and_v X Y) → ∀ cx mx,
      HasType sc sub ⟨.V, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
      CheckedTrueRowAgreementVIn sc sub root env flags pa po) :
    CheckedTrueRowAgreementBIn sc (.and_v X Y) root env flags pa po := by
  obtain ⟨cx, cy, tx, ty⟩ := and_v_B_typed_children typed
  obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
  have ix := ihV X (by simp; omega) cx mx tx wf.1 hx nx (path_trans (.left .and_v .here) path)
  have iy := ihB Y (by simp; omega) cy my ty wf.2.1 hy ny (path_trans (.right .and_v .here) path)
  intro own expected top rest context nodup canonical bounded run truth _checked
  obtain ⟨wx, wy, ox, oy, expectedEq, ownEq, satX, satY, runX, runY⟩ :=
    and_v_decompose tx ty wf.1 wf.2.1 canonical run
  subst own
  obtain ⟨ccx, ccy, ndx, ndy, bx, boundY⟩ := and_v_false_contexts context nodup bounded
  have ex := agree_V tx wf.1 hx nx ix ccx ndx satX bx runX
  have ey := agree_B ty wf.2.1 hy ny iy ccy ndy satY boundY runY truth
  rw [expectedEq, ex, ey]

def CheckedMaterialIn (sc : ScriptContext) (child root : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) : Prop :=
  ∀ own expected, ExecutionContextIn sc root child env flags pa po own → satisfy child env = some expected →
    ∀ sig ∈ own, ∀ key ∈ child.keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true → sig ∈ expected

abbrev CheckedMaterial := CheckedMaterialIn .tapscript

theorem checkedMaterial_self (child : CoreFragment) (env : SatEnv) (flags : ScriptFlags) (pa po : Witness) :
    CheckedMaterialIn sc child child env flags pa po := by
  intro own expected context canonical sig member key keyMem checked
  have eq : pa = expected := Option.some.inj (context.canonical.symm.trans canonical)
  rw [← eq]
  exact context.thirdParty.2.1 sig (context.consumedIn sig member) key keyMem
    (MultiA.verifySigFor_of_checkSigWithEncoding checked)

theorem expressive_pair {child : CoreFragment} {env : SatEnv} {own expected : Witness}
    {ty : MiniType} {mm : MalleabilityModifiers}
    (typed : HasType sc child ty) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sound : env.Sound) (sizes : ∀ key ∈ child.keys, key.bytes.size = 32)
    (canonical : satisfy child env = some expected) :
    PairItems (LocalSlot child env own expected) (satisfactionCandidates child env) := by
  constructor
  · intro witness projection item member _actual _key _keyMem _valid _size
    have eq : witness = expected := Option.some.inj (projection.symm.trans canonical)
    simpa [eq] using member
  · intro witness projection item member
    have small := expressive_dsat_items_small typed wf mal nm e sound sizes projection item member
    exact localSlot_short (by omega)

theorem checkedMaterial_expressive {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {ty : MiniType} {mm : MalleabilityModifiers}
    (typed : HasType sc child ty) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (path : SlotPath child root) (nodup : root.keys.Nodup) : CheckedMaterialIn sc child root env flags pa po := by
  intro own expected context canonical sig member key keyMem checked
  cases sc with
  | p2wsh =>
    obtain ⟨_, rfl, frame⟩ := context.saneFrame
    exact P2WSHRecovery.signature_in_satisfaction frame path canonical (frame.items _ member) keyMem checked
  | tapscript =>
    have sizes := fun key hk => context.keySizes key (context.childKeys key hk)
    have supported := path_pair path context
      (expressive_pair typed wf mal nm e context.sound sizes canonical) (fun _ h => h) nodup
    have valid := MultiA.verifySigFor_of_checkSigWithEncoding checked
    have disclosed := context.thirdParty.2.1 sig (context.consumedIn sig member)
      key (context.childKeys key keyMem) valid
    exact supported.1 pa context.canonical sig disclosed member key keyMem valid
      (successful_slot_size context.version (sizes key keyMem) checked)

theorem excluded_checked {choice active selected root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected consumed selectedArgs : Witness} {selector : StackElement}
    (material : CheckedMaterialIn sc choice root env flags pa po)
    (context : ExecutionContextIn sc root choice env flags pa po own)
    (canonical : satisfy choice env = some expected)
    (canonicalSelected : satisfy selected env = some selectedArgs)
    (expectedEq : expected = selectedArgs ++ [selector]) (selectorValue : selector = falseElement ∨ selector = trueElement)
    (inOwn : ∀ item ∈ consumed, item ∈ own)
    (activeKeys : ∀ key ∈ active.keys, key ∈ choice.keys)
    (selectedKeys : ∀ key ∈ selected.keys, key ∈ choice.keys)
    (selectedLocks : ∀ lock ∈ selected.hashLocks, lock ∈ choice.hashLocks)
    (distinct : ∀ key ∈ active.keys, ∀ other ∈ selected.keys, key ≠ other) :
    ¬ CheckedSignature active env flags consumed := by
  rintro ⟨sig, member, key, keyMem, checked⟩
  have localized := material own expected context canonical sig (inOwn sig member) key (activeKeys key keyMem) checked
  rw [expectedEq] at localized
  rcases List.mem_append.mp localized with selectedMem | selectorMem
  · cases sc with
    | p2wsh =>
      obtain ⟨sane, rfl, frame⟩ := context.saneFrame
      have origin := P2WSHRecovery.checked_source_signature sane frame.sound frame.version frame.modeled
        frame.thirdParty frame.recover.2 (frame.items _ (inOwn _ member)) (frame.keys _ (activeKeys _ keyMem))
        (fun k h => frame.keys _ (selectedKeys k h)) (fun l h => frame.locks _ (selectedLocks l h))
        (satisfy_material canonicalSelected sig selectedMem) checked
      exact distinct key keyMem key origin.1 rfl
    | tapscript =>
      have size := checked_slot_size context (activeKeys _ keyMem) checked rfl
      obtain ⟨other, otherMem, signature⟩ := material_signature_of_size context.sound
        (fun k hk => context.keySizes k (context.childKeys k (selectedKeys k hk)))
        (satisfy_material canonicalSelected sig selectedMem) size
      exact context.thirdParty.1 sig (context.consumedIn sig (inOwn sig member))
        key (context.childKeys key (activeKeys key keyMem)) other (context.childKeys other (selectedKeys other otherMem))
        (distinct key keyMem other otherMem) (MultiA.verifySigFor_of_checkSigWithEncoding checked)
        (context.sound.signatureValid signature)
  · obtain rfl := List.mem_singleton.mp selectorMem
    rcases selectorValue with rfl | rfl
    · have valid := MultiA.verifySigFor_of_checkSigWithEncoding checked
      rw [context.sound.emptySignatureInvalid] at valid
      contradiction
    · cases sc with
      | p2wsh =>
        exact P2WSHNonMalleabilityKeyChoice.checked_signature_ne_true context.modeled.2.2.2.2
          context.version checked rfl
      | tapscript =>
        have size := checked_slot_size context (activeKeys _ keyMem) checked rfl
        exact (by decide : ¬ (trueElement.size = 64 ∨ trueElement.size = 65)) size

theorem or_i_selected_left {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected consumed : Witness}
    (material : CheckedMaterialIn sc (.or_i X Y) root env flags pa po)
    (context : ExecutionContextIn sc root (.or_i X Y) env flags pa po own)
    (nodup : (CoreFragment.or_i X Y).keys.Nodup)
    (canonical : satisfy (.or_i X Y) env = some expected)
    (inOwn : ∀ item ∈ consumed, item ∈ own) (evidence : ExecutionEvidence X env flags consumed) :
    ∃ selected, satisfy X env = some selected ∧ expected = selected ++ [trueElement] := by
  rcases or_i_candidate_cases canonical with h | ⟨selected, satY, eq⟩
  · exact h
  · rcases evidence with unsigned | checked
    · rw [eq] at canonical
      exact (or_i_right_excludes_unsigned_left canonical unsigned).elim
    · exact (excluded_checked material context canonical satY eq (.inl rfl) inOwn
        (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
        (List.pairwise_append.mp nodup).2.2 checked).elim

theorem or_i_selected_right {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected consumed : Witness}
    (material : CheckedMaterialIn sc (.or_i X Y) root env flags pa po)
    (context : ExecutionContextIn sc root (.or_i X Y) env flags pa po own)
    (nodup : (CoreFragment.or_i X Y).keys.Nodup)
    (canonical : satisfy (.or_i X Y) env = some expected)
    (inOwn : ∀ item ∈ consumed, item ∈ own) (evidence : ExecutionEvidence Y env flags consumed) :
    ∃ selected, satisfy Y env = some selected ∧ expected = selected ++ [falseElement] := by
  rcases or_i_candidate_cases canonical with ⟨selected, satX, eq⟩ | h
  · rcases evidence with unsigned | checked
    · rw [eq] at canonical
      exact (or_i_left_excludes_unsigned_right canonical unsigned).elim
    · exact (excluded_checked material context canonical satX eq (.inr rfl) inOwn
        (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
        (fun key hk other ho => Ne.symm ((List.pairwise_append.mp nodup).2.2 other ho key hk)) checked).elim
  · exact h

theorem checked_or_i_of_material {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩) (wf : (CoreFragment.or_i X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_i X Y) root) (material : CheckedMaterialIn sc (.or_i X Y) root env flags pa po)
    (ih : ∀ sub, sizeOf sub < sizeOf (CoreFragment.or_i X Y) → ∀ cx mx,
      HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
      HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
      CheckedTrueRowAgreementBIn sc sub root env flags pa po) :
    CheckedTrueRowAgreementBIn sc (.or_i X Y) root env flags pa po := by
  obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
  cases typed_B_shape typed with
  | or_i tx ty =>
    have ix := ih X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .or_i .here) path)
    have iy := ih Y (by simp; omega) _ _ ty wf.2 hy ny (path_trans (.right .or_i .here) path)
    intro own expected top rest context nodup canonical bounded run truth _checked
    rcases or_i_run_B tx ty wf.1 wf.2 context.rules run with ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
    · subst own
      have inOwn : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
      have cc := executionContext_restrict context (active := X) (fun _ h => List.mem_append_left _ h)
        (fun _ h => List.mem_append_left _ h) inOwn
      have bound := bounded_without_selector bounded
      have evidence := uniform_B_execution X _ _ tx wf.1 hx nx root env flags pa po active top rest cc bound childRun truth
      obtain ⟨selected, satX, expectedEq⟩ := or_i_selected_left material context nodup canonical inOwn evidence
      have equal := agree_B tx wf.1 hx nx ix cc (List.pairwise_append.mp nodup).1 satX bound childRun truth
      rw [expectedEq, equal]
    · subst own
      have inOwn : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
      have cc := executionContext_restrict context (active := Y) (fun _ h => List.mem_append_right _ h)
        (fun _ h => List.mem_append_right _ h) inOwn
      have bound := bounded_without_selector bounded
      have evidence := uniform_B_execution Y _ _ ty wf.2 hy ny root env flags pa po active top rest cc bound childRun truth
      obtain ⟨selected, satY, expectedEq⟩ := or_i_selected_right material context nodup canonical inOwn evidence
      have equal := agree_B ty wf.2 hy ny iy cc (List.pairwise_append.mp nodup).2.1 satY bound childRun truth
      rw [expectedEq, equal]
  | remaining impossible => cases impossible

def SmallerCheckedBIn (sc : ScriptContext) (parent root : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) : Prop :=
  ∀ sub, sizeOf sub < sizeOf parent → ∀ cx mx,
    HasType sc sub ⟨.B, cx⟩ → sub.WellFormed sc →
    HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
    CheckedTrueRowAgreementBIn sc sub root env flags pa po

abbrev SmallerCheckedB := SmallerCheckedBIn .tapscript

def SmallerCheckedVIn (sc : ScriptContext) (parent root : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) : Prop :=
  ∀ sub, sizeOf sub < sizeOf parent → ∀ cx mx,
    HasType sc sub ⟨.V, cx⟩ → sub.WellFormed sc →
    HasMalleability sc sub mx → mx.nonMalleable = true → SlotPath sub root →
    CheckedTrueRowAgreementVIn sc sub root env flags pa po

abbrev SmallerCheckedV := SmallerCheckedVIn .tapscript

theorem checked_or_i_self {X Y : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_i X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (ih : SmallerCheckedBIn sc (.or_i X Y) (.or_i X Y) env flags pa po) :
    CheckedTrueRowAgreementBIn sc (.or_i X Y) (.or_i X Y) env flags pa po :=
  checked_or_i_of_material typed wf mal nm .here
    (checkedMaterial_self _ env flags pa po) ih

theorem checked_or_i_expressive {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_i X Y) ⟨.B, cm⟩)
    (wf : (CoreFragment.or_i X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (e : mm.e = true) (path : SlotPath (.or_i X Y) root) (nodup : root.keys.Nodup)
    (ih : SmallerCheckedBIn sc (.or_i X Y) root env flags pa po) :
    CheckedTrueRowAgreementBIn sc (.or_i X Y) root env flags pa po :=
  checked_or_i_of_material typed wf mal nm path
    (checkedMaterial_expressive typed wf mal nm e path nodup) ih

theorem checkedV_and_v_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.and_v X Y) ⟨.V, cm⟩)
    (wf : (CoreFragment.and_v X Y).WellFormed sc)
    (mal : HasMalleability sc (.and_v X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.and_v X Y) root)
    (ih : SmallerCheckedVIn sc (.and_v X Y) root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.and_v X Y) root env flags pa po := by
  obtain ⟨mx, my, hx, hy, nx, ny⟩ := and_v_malleability_children mal nm
  cases SignedV.typed_V_shape typed with
  | and_v tx ty =>
    have ix := ih X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .and_v .here) path)
    have iy := ih Y (by simp; omega) _ _ ty wf.2.1 hy ny (path_trans (.right .and_v .here) path)
    intro own expected rest context nodup canonical bounded run _checked
    obtain ⟨ox, oy, ownEq, runX, runY⟩ := and_v_run_V_frame tx ty wf.1 wf.2.1 run
    obtain ⟨wx, wy, satX, satY, expectedEq⟩ := CandidateResult.combine_usableWitness_iff.mp canonical
    subst own
    obtain ⟨ccx, ccy, ndx, ndy, bx, boundY⟩ := and_v_false_contexts context nodup bounded
    have ex := agree_V tx wf.1 hx nx ix ccx ndx satX bx runX
    have ey := agree_V ty wf.2.1 hy ny iy ccy ndy satY boundY runY
    rw [expectedEq, ex, ey]
    rfl

end LeanMiniscript.Extraction.TapscriptRecovery.CompositeRows

namespace LeanMiniscript.Extraction.TapscriptRecovery.VRows

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport Active OrI SignedV ThresholdUnit
  OriginCounts CheckedRows SlotLocal CompositeRows

theorem typedV_dsat_impossible {child : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType sc child ⟨.V, cm⟩) (env : SatEnv) :
    (satisfactionCandidates child env).dsat = .impossible := by
  cases typed_V_shape typed with
  | verify tx => rfl
  | and_v tx ty =>
    simp only [satisfactionCandidates, typedV_dsat_impossible ty env]
    cases (satisfactionCandidates _ env).sat <;> rfl
  | or_c tx d u ty => rfl
  | or_i tx ty =>
    simp [satisfactionCandidates, typedV_dsat_impossible tx env, typedV_dsat_impossible ty env,
      CandidateResult.withSelector, CandidateResult.select]
  | andor tx d u ty tz =>
    simp only [satisfactionCandidates, typedV_dsat_impossible ty env, typedV_dsat_impossible tz env]
    cases (satisfactionCandidates _ env).sat <;> cases (satisfactionCandidates _ env).dsat <;> rfl
termination_by sizeOf child

theorem V_pair {child : CoreFragment} {env : SatEnv} {own expected : Witness}
    {cm : CorrectnessModifiers} (typed : HasType sc child ⟨.V, cm⟩)
    (canonical : satisfy child env = some expected) :
    PairItems (LocalSlot child env own expected) (satisfactionCandidates child env) := by
  constructor
  · intro witness projection item member _actual _key _keyMem _valid _size
    have eq : witness = expected := Option.some.inj (projection.symm.trans canonical)
    simpa [eq] using member
  · rw [typedV_dsat_impossible typed env]
    intro witness projection
    cases projection

theorem checkedMaterial_V {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers}
    (typed : HasType sc child ⟨.V, cm⟩)
    (path : SlotPath child root) (nodup : root.keys.Nodup) :
    CheckedMaterialIn sc child root env flags pa po := by
  intro own expected context canonical sig member key keyMem checked
  cases sc with
  | p2wsh =>
    obtain ⟨_, rfl, frame⟩ := context.saneFrame
    exact P2WSHRecovery.signature_in_satisfaction frame path canonical (frame.items _ member) keyMem checked
  | tapscript =>
    have supported := path_pair path context (V_pair typed canonical) (fun _ h => h) nodup
    have valid := MultiA.verifySigFor_of_checkSigWithEncoding checked
    have disclosed := context.thirdParty.2.1 sig (context.consumedIn sig member)
      key (context.childKeys key keyMem) valid
    exact supported.1 pa context.canonical sig disclosed member key keyMem valid
      (successful_slot_size context.version (context.keySizes key (context.childKeys key keyMem)) checked)

theorem checkedV_or_i_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_i X Y) ⟨.V, cm⟩)
    (wf : (CoreFragment.or_i X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_i X Y) root) (rootNodup : root.keys.Nodup)
    (ih : SmallerCheckedVIn sc (.or_i X Y) root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.or_i X Y) root env flags pa po := by
  have material := checkedMaterial_V typed path rootNodup (env := env) (flags := flags) (pa := pa) (po := po)
  obtain ⟨mx, my, hx, hy, nx, ny, _signed⟩ := or_i_malleability_children mal nm
  cases typed_V_shape typed with
  | or_i tx ty =>
    have ix := ih X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .or_i .here) path)
    have iy := ih Y (by simp; omega) _ _ ty wf.2 hy ny (path_trans (.right .or_i .here) path)
    intro own expected rest context nodup canonical bounded run _checked
    rcases or_i_run_V tx ty wf.1 wf.2 context.rules run with
        ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
    · subst own
      have inOwn : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
      have cc := executionContext_restrict context (active := X) (fun _ h => List.mem_append_left _ h)
        (fun _ h => List.mem_append_left _ h) inOwn
      have bound := bounded_without_selector bounded
      have evidence := ambientExecutionV_from_smaller_B tx wf.1 hx nx
        (fun sub _ => uniform_B_execution sub) root env flags pa po active rest cc bound childRun
      obtain ⟨selected, satX, expectedEq⟩ := or_i_selected_left material context nodup canonical inOwn evidence
      have eqChild := agree_V tx wf.1 hx nx ix cc (List.pairwise_append.mp nodup).1 satX bound childRun
      rw [expectedEq, eqChild]
    · subst own
      have inOwn : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
      have cc := executionContext_restrict context (active := Y) (fun _ h => List.mem_append_right _ h)
        (fun _ h => List.mem_append_right _ h) inOwn
      have bound := bounded_without_selector bounded
      have evidence := ambientExecutionV_from_smaller_B ty wf.2 hy ny
        (fun sub _ => uniform_B_execution sub) root env flags pa po active rest cc bound childRun
      obtain ⟨selected, satY, expectedEq⟩ := or_i_selected_right material context nodup canonical inOwn evidence
      have eqChild := agree_V ty wf.2 hy ny iy cc (List.pairwise_append.mp nodup).2.1 satY bound childRun
      rw [expectedEq, eqChild]

def BPending (root fragment : CoreFragment) (mm : MalleabilityModifiers) : Prop :=
  fragment.keys ≠ [] ∧ match fragment with
    | .c (.pk_k _) | .c (.pk_h _) | .multi _ _ | .multi_a _ _ | .and_v _ _ | .j _ | .n _ => False
    | .or_i _ _ => fragment ≠ root ∧ mm.e = false
    | _ => True

theorem checkedB_no_keys {fragment root : CoreFragment} (env : SatEnv) (flags : ScriptFlags)
    (pa po : Witness) (keys : fragment.keys = []) :
    CheckedTrueRowAgreementBIn sc fragment root env flags pa po := by
  intro own expected top rest context nodup canonical bounded run truth checked
  obtain ⟨sig, member, key, keyMem, valid⟩ := checked
  simp [keys] at keyMem

theorem checkedB_step {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.B, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootWF : root.WellFormed sc) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedBIn sc fragment root env flags pa po)
    (ihV : SmallerCheckedVIn sc fragment root env flags pa po)
    (rest : BPending root fragment mm → CheckedTrueRowAgreementBIn sc fragment root env flags pa po) :
    CheckedTrueRowAgreementBIn sc fragment root env flags pa po := by
  by_cases empty : fragment.keys = []
  · exact checkedB_no_keys env flags pa po empty
  cases fragment with
  | c child =>
    cases child with
    | pk_k key => exact checkedTrue_c_pk_k key root env flags pa po
    | pk_h key => exact checkedTrue_c_pk_h key root env flags pa po
    | _ => exact rest ⟨empty, trivial⟩
  | multi k keys =>
    cases sc with
    | p2wsh => exact checkedTrue_multi_from_path path rootWF
    | tapscript => exact wf.1.elim
  | multi_a k keys =>
    cases sc with
    | tapscript => exact checkedTrue_multi_a_from_path env flags pa po path rootWF rootNodup
    | p2wsh => exact wf.1.elim
  | and_v X Y => exact checked_and_v_step typed wf mal nm path ihB ihV
  | or_i X Y =>
    by_cases e : mm.e = true
    · exact checked_or_i_expressive typed wf mal nm e path rootNodup ihB
    · by_cases self : CoreFragment.or_i X Y = root
      · subst root
        exact checked_or_i_self typed wf mal nm ihB
      · exact rest ⟨empty, self, Bool.eq_false_iff.mpr e⟩
  | j child =>
    cases typed with
    | j_wrap tx n => cases mal with
      | j hx =>
        exact checkedTrue_j (ihB child (by simp) _ _ tx wf hx nm (path_trans (.wrapper .j .here) path))
  | n child =>
    cases typed with
    | n_wrap tx => cases mal with
      | n hx =>
        exact checkedTrue_n (ihB child (by simp) _ _ tx wf hx nm (path_trans (.wrapper .n .here) path))
  | _ => exact rest ⟨empty, trivial⟩

end LeanMiniscript.Extraction.TapscriptRecovery.VRows

namespace LeanMiniscript.Extraction.TapscriptRecovery.VConditions

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport OrI OrDC SignedV ThresholdUnit
  DsatMaterial FalseUniform SlotLocal CompositeRows VRows

theorem free_of_sources {choice active root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected consumed : Witness}
    (material : CheckedMaterialIn sc choice root env flags pa po)
    (context : ExecutionContextIn sc root choice env flags pa po own)
    (canonical : satisfy choice env = some expected)
    (keys : ∀ key ∈ active.keys, key ∈ choice.keys)
    (included : ∀ item ∈ consumed, item ∈ own)
    (sources : Items (CheckedSlot sc active env flags consumed []) expected) :
    ¬ CheckedSignature active env flags consumed := by
  rintro ⟨sig, member, key, keyMem, checked⟩
  have disclosed := material own expected context canonical sig (included sig member) key (keys key keyMem) checked
  have impossible := sources sig disclosed member key keyMem checked
    (checked_slot_size context (keys key keyMem) checked)
  exact List.not_mem_nil impossible

theorem dsat_sources {condition target : CoreFragment} {env : SatEnv} {actual dsat : Witness}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc condition ⟨.B, cm⟩) (wf : condition.WellFormed sc)
    (mal : HasMalleability sc condition mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sound : env.Sound) (sizes : ∀ key ∈ condition.keys, key.bytes.size = 32)
    (canonical : dissatisfy condition env = some dsat) : Items (LocalSlot target env actual []) dsat := by
  intro item member
  have small := expressive_dsat_items_small typed wf mal nm e sound sizes canonical item member
  exact localSlot_short (by omega)

theorem split_contexts {choice X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po left right : Witness} {rest : Stack}
    (context : ExecutionContextIn sc root choice env flags pa po (right ++ left))
    (keysX : ∀ key ∈ X.keys, key ∈ choice.keys) (keysY : ∀ key ∈ Y.keys, key ∈ choice.keys)
    (locksX : ∀ lock ∈ X.hashLocks, lock ∈ choice.hashLocks)
    (locksY : ∀ lock ∈ Y.hashLocks, lock ∈ choice.hashLocks)
    (bounded : ∀ item ∈ (right ++ left).toInitialStack ++ rest, item.size ≤ maxScriptElementSize) :
    ExecutionContextIn sc root X env flags pa po left ∧ ExecutionContextIn sc root Y env flags pa po right ∧
    (∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) ∧
    (∀ item ∈ right.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) := by
  have boundAll : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest), item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  exact ⟨executionContext_restrict context keysX locksX (fun _ h => List.mem_append_right _ h),
    executionContext_restrict context keysY locksY (fun _ h => List.mem_append_left _ h),
    boundAll, fun item member => boundAll item (List.mem_append_right _ member)⟩

theorem false_agreement {child root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} {top : StackElement} {rest : Stack}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc child ⟨.B, cm⟩) (wf : child.WellFormed sc)
    (mal : HasMalleability sc child mm) (nm : mm.nonMalleable = true)
    (d : cm.d = true) (u : cm.u = true) (e : mm.e = true)
    (context : ExecutionContextIn sc root child env flags pa po own) (nodup : child.keys.Nodup)
    (canonical : dissatisfy child env = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile child) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []))
    (falsehood : castToBool top = false) (free : ¬ CheckedSignature child env flags own) : own = expected := by
  have actual := uniform_conditionFalseComplete child cm mm typed wf mal nm d u e
    root env flags pa po own top rest context nodup bounded run falsehood free
  exact Option.some.inj (actual.symm.trans canonical)

theorem fallback_noChecked {choice condition continuation root : CoreFragment}
    {env : SatEnv} {flags : ScriptFlags} {pa po own expected actual dsat sat : Witness}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (material : CheckedMaterialIn sc choice root env flags pa po)
    (context : ExecutionContextIn sc root choice env flags pa po own)
    (conditionContext : ExecutionContextIn sc root condition env flags pa po actual)
    (typed : HasType sc condition ⟨.B, cm⟩) (wf : condition.WellFormed sc)
    (mal : HasMalleability sc condition mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (canonical : satisfy choice env = some expected) (expectedEq : expected = sat ++ dsat)
    (canonicalD : dissatisfy condition env = some dsat) (canonicalS : satisfy continuation env = some sat)
    (conditionKeys : ∀ key ∈ condition.keys, key ∈ choice.keys)
    (continuationKeys : ∀ key ∈ continuation.keys, key ∈ choice.keys)
    (continuationLocks : ∀ lock ∈ continuation.hashLocks, lock ∈ choice.hashLocks)
    (included : ∀ item ∈ actual, item ∈ own)
    (separate : ∀ key ∈ condition.keys, ∀ other ∈ continuation.keys, key ≠ other) :
    ¬ CheckedSignature condition env flags actual := by
  apply free_of_sources material context canonical conditionKeys included
  rw [expectedEq]
  exact items_combine (expressive_dsat_checked_slots typed wf mal nm e context
    (fun key member => context.childKeys key (conditionKeys key member)) canonicalD)
    ((foreign_checked_pair conditionContext (fun key member => context.childKeys key (continuationKeys key member)) (fun l h => context.childLocks l (continuationLocks l h)) separate).1 sat canonicalS)

theorem checkedV_or_c_step {X Y root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.or_c X Y) ⟨.V, cm⟩)
    (wf : (CoreFragment.or_c X Y).WellFormed sc)
    (mal : HasMalleability sc (.or_c X Y) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.or_c X Y) root) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedBIn sc (.or_c X Y) root env flags pa po)
    (ihV : SmallerCheckedVIn sc (.or_c X Y) root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.or_c X Y) root env flags pa po := by
  have material := checkedMaterial_V typed path rootNodup (env := env) (flags := flags) (pa := pa) (po := po)
  obtain ⟨mx, my, hx, hy, nx, ny, ex, _signed⟩ := shortCircuit_malleability_children (keep := false) mal nm
  cases typed_V_shape typed with
  | or_c tx d u ty =>
    have ix := ihB X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.left .or_c .here) path)
    have iy := ihV Y (by simp; omega) _ _ ty wf.2 hy ny (path_trans (.right .or_c .here) path)
    have rawD := expressive_rawUnsigned wf.1 tx hx nx ex env
    intro own expected rest context nodup canonical bounded run _checked
    have kx : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_c X Y).keys := fun _ h => List.mem_append_left _ h
    have ky : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_c X Y).keys := fun _ h => List.mem_append_right _ h
    have lx : ∀ lock ∈ X.hashLocks, lock ∈ (CoreFragment.or_c X Y).hashLocks := fun _ h => List.mem_append_left _ h
    have ly : ∀ lock ∈ Y.hashLocks, lock ∈ (CoreFragment.or_c X Y).hashLocks := fun _ h => List.mem_append_right _ h
    have ndx := (List.pairwise_append.mp nodup).1
    have ndy := (List.pairwise_append.mp nodup).2.1
    have separate := (List.pairwise_append.mp nodup).2.2
    rcases shortCircuit_run_frame (keep := false) (top := falseElement) tx ty wf.1 wf.2 run with
        ⟨value, runX, truth⟩ | ⟨ox, oy, value, ownEq, runX, falsehood, runY⟩
    · have ccx := executionContext_restrict context kx lx (fun _ h => h)
      have evidence := uniform_B_execution X _ _ tx wf.1 hx nx root env flags pa po own value rest ccx bounded runX truth
      rcases shortCircuit_candidate_cases false canonical with ⟨satX, _⟩ | ⟨dx, sy, expectedEq, dsatX, satY, excluded⟩
      · exact agree_B tx wf.1 hx nx ix ccx ndx satX bounded runX truth
      · have sources : Items (CheckedSlot sc X env flags own []) expected := by
          rw [expectedEq]
          exact items_combine (expressive_dsat_checked_slots tx wf.1 hx nx ex context
            (fun key member => context.childKeys key (kx key member)) dsatX)
            ((foreign_checked_pair ccx (fun key member => context.childKeys key (ky key member)) (fun l h => context.childLocks l (ly l h)) separate).1 sy satY)
        have free := free_of_sources material context canonical kx (fun _ h => h) sources
        exact evidence.elim (fun raw => (excluded raw).elim) (fun sig => (free sig).elim)
    · subst own
      obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts context kx ky lx ly bounded
      have evidenceY := ambientExecutionV_from_smaller_B ty wf.2 hy ny
        (fun sub _ => uniform_B_execution sub) root env flags pa po oy rest ccy byBound runY
      rcases shortCircuit_candidate_cases false canonical with ⟨satX, excluded⟩ | ⟨dx, sy, expectedEq, dsatX, satY, _⟩
      · have sources : Items (CheckedSlot sc Y env flags oy []) expected :=
          (foreign_checked_pair ccy (fun key member => context.childKeys key (kx key member)) (fun l h => context.childLocks l (lx l h))
            (fun key hk other ho => Ne.symm (separate other ho key hk))).1 expected satX
        have freeY := free_of_sources material context canonical ky (fun _ h => List.mem_append_left _ h) sources
        exact evidenceY.elim (fun raw => (excluded (unsigned_combine rawD raw)).elim)
          (fun sig => (freeY sig).elim)
      · have freeX := fallback_noChecked material context ccx tx wf.1 hx nx ex canonical expectedEq
          dsatX satY kx ky ly (fun _ h => List.mem_append_right _ h) separate
        have eqX := false_agreement tx wf.1 hx nx d u ex ccx ndx dsatX bx runX falsehood freeX
        have eqY := agree_V ty wf.2 hy ny iy ccy ndy satY byBound runY
        rw [expectedEq, eqX, eqY]

theorem andor_candidate_rows {X Y Z : CoreFragment} {env : SatEnv} {expected : Witness}
    (canonical : satisfy (.andor X Y Z) env = some expected) :
    (∃ sx sy, expected = sy ++ sx ∧ satisfy X env = some sx ∧ satisfy Y env = some sy ∧
      ¬ RawUnsigned ((satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).sat)) ∨
    (∃ dx sz, expected = sz ++ dx ∧ dissatisfy X env = some dx ∧ satisfy Z env = some sz ∧
      ¬ RawUnsigned ((satisfactionCandidates X env).sat.combine (satisfactionCandidates Y env).sat)) := by
  rcases select_usable_rows canonical with ⟨left, excluded⟩ | ⟨right, excluded⟩
  · obtain ⟨sx, sy, cx, cy, eq⟩ := CandidateResult.combine_usableWitness_iff.mp left
    exact Or.inl ⟨sx, sy, eq, cx, cy, excluded⟩
  · obtain ⟨dx, sz, cx, cz, eq⟩ := CandidateResult.combine_usableWitness_iff.mp right
    exact Or.inr ⟨dx, sz, eq, cx, cz, excluded⟩

theorem checkedV_andor_step {X Y Z root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.andor X Y Z) ⟨.V, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed sc)
    (mal : HasMalleability sc (.andor X Y Z) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.andor X Y Z) root) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedBIn sc (.andor X Y Z) root env flags pa po)
    (ihV : SmallerCheckedVIn sc (.andor X Y Z) root env flags pa po) :
    CheckedTrueRowAgreementVIn sc (.andor X Y Z) root env flags pa po := by
  have material := checkedMaterial_V typed path rootNodup (env := env) (flags := flags) (pa := pa) (po := po)
  obtain ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex⟩ := andor_malleability_children mal nm
  cases typed_V_shape typed with
  | andor tx d u ty tz =>
    have ix := ihB X (by simp; omega) _ _ tx wf.1 hx nx (path_trans (.condition .here) path)
    have iy := ihV Y (by simp; omega) _ _ ty wf.2.1 hy ny (path_trans (.thenBranch .here) path)
    have iz := ihV Z (by simp; omega) _ _ tz wf.2.2.1 hz nz (path_trans (.elseBranch .here) path)
    have rawD := expressive_rawUnsigned wf.1 tx hx nx ex env
    intro own expected rest context nodup canonical bounded run _checked
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
    rcases andor_run_V_frame tx ty tz wf.1 wf.2.1 wf.2.2.1 run with
        ⟨ox, oz, value, ownEq, runX, falsehood, runZ⟩ | ⟨ox, oy, value, ownEq, runX, truth, runY⟩
    · subst own
      obtain ⟨ccx, ccz, bx, bz⟩ := split_contexts context kx kz lx lz bounded
      have evidenceZ := ambientExecutionV_from_smaller_B tz wf.2.2.1 hz nz
        (fun sub _ => uniform_B_execution sub) root env flags pa po oz rest ccz bz runZ
      rcases andor_candidate_rows canonical with
          ⟨sx, sy, expectedEq, satX, satY, excluded⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, _⟩
      · have sourcesZ : Items (CheckedSlot sc Z env flags oz []) expected := by
          rw [expectedEq]
          exact items_combine
            ((foreign_checked_pair ccz (fun key member => context.childKeys key (kx key member)) (fun l h => context.childLocks l (lx l h))
              (fun key hk other ho => Ne.symm (sepXZ other ho key hk))).1 sx satX)
            ((foreign_checked_pair ccz (fun key member => context.childKeys key (ky key member)) (fun l h => context.childLocks l (ly l h))
              (fun key hk other ho => Ne.symm (sepYZ other ho key hk))).1 sy satY)
        have freeZ := free_of_sources material context canonical kz (fun _ h => List.mem_append_left _ h) sourcesZ
        exact evidenceZ.elim (fun raw => (excluded (unsigned_combine rawD raw)).elim)
          (fun sig => (freeZ sig).elim)
      · have freeX := fallback_noChecked material context ccx tx wf.1 hx nx ex canonical expectedEq
          dsatX satZ kx kz lz (fun _ h => List.mem_append_right _ h) sepXZ
        have eqX := false_agreement tx wf.1 hx nx d u ex ccx ndx dsatX bx runX falsehood freeX
        have eqZ := agree_V tz wf.2.2.1 hz nz iz ccz ndz satZ bz runZ
        rw [expectedEq, eqX, eqZ]
    · subst own
      obtain ⟨ccx, ccy, bx, byBound⟩ := split_contexts context kx ky lx ly bounded
      have evidenceX := uniform_B_execution X _ _ tx wf.1 hx nx root env flags pa po ox value
        (oy.toInitialStack ++ rest) ccx bx runX truth
      have evidenceY := ambientExecutionV_from_smaller_B ty wf.2.1 hy ny
        (fun sub _ => uniform_B_execution sub) root env flags pa po oy rest ccy byBound runY
      rcases andor_candidate_rows canonical with
          ⟨sx, sy, expectedEq, satX, satY, _⟩ | ⟨dx, sz, expectedEq, dsatX, satZ, excluded⟩
      · have eqX := agree_B tx wf.1 hx nx ix ccx ndx satX bx runX truth
        have eqY := agree_V ty wf.2.1 hy ny iy ccy ndy satY byBound runY
        rw [expectedEq, eqX, eqY]
      · have sourcesX : Items (CheckedSlot sc X env flags ox []) expected := by
          rw [expectedEq]
          exact items_combine (expressive_dsat_checked_slots tx wf.1 hx nx ex context
            (fun key member => context.childKeys key (kx key member)) dsatX)
            ((foreign_checked_pair ccx (fun key member => context.childKeys key (kz key member)) (fun l h => context.childLocks l (lz l h)) sepXZ).1 sz satZ)
        have sourcesY : Items (CheckedSlot sc Y env flags oy []) expected := by
          rw [expectedEq]
          exact items_combine (expressive_dsat_checked_slots tx wf.1 hx nx ex context
            (fun key member => context.childKeys key (kx key member)) dsatX)
            ((foreign_checked_pair ccy (fun key member => context.childKeys key (kz key member)) (fun l h => context.childLocks l (lz l h)) sepYZ).1 sz satZ)
        have freeX := free_of_sources material context canonical kx (fun _ h => List.mem_append_right _ h) sourcesX
        have freeY := free_of_sources material context canonical ky (fun _ h => List.mem_append_left _ h) sourcesY
        rcases evidenceX with rawX | sigX
        · rcases evidenceY with rawY | sigY
          · exact (excluded (unsigned_combine rawX rawY)).elim
          · exact (freeY sigY).elim
        · exact (freeX sigX).elim

theorem checkedV_from_smaller_B {fragment root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc fragment ⟨.V, cm⟩) (wf : fragment.WellFormed sc)
    (mal : HasMalleability sc fragment mm) (nm : mm.nonMalleable = true)
    (path : SlotPath fragment root) (rootNodup : root.keys.Nodup)
    (ihB : SmallerCheckedBIn sc fragment root env flags pa po) :
    CheckedTrueRowAgreementVIn sc fragment root env flags pa po := by
  have ihV : SmallerCheckedVIn sc fragment root env flags pa po := by
    intro sub smaller cx mx tx wx hx nx subPath
    apply checkedV_from_smaller_B tx wx hx nx subPath rootNodup
    intro inner innerSmaller ci mi ti wi hi ni innerPath
    exact ihB inner (Nat.lt_trans innerSmaller smaller) ci mi ti wi hi ni innerPath
  cases typed_V_shape typed with
  | verify tx => exact checkedV_verify_step typed wf mal nm path ihB
  | and_v tx ty => exact checkedV_and_v_step typed wf mal nm path ihV
  | or_i tx ty => exact checkedV_or_i_step typed wf mal nm path rootNodup ihV
  | or_c tx d u ty => exact checkedV_or_c_step typed wf mal nm path rootNodup ihB ihV
  | andor tx d u ty tz => exact checkedV_andor_step typed wf mal nm path rootNodup ihB ihV
termination_by sizeOf fragment

end LeanMiniscript.Extraction.TapscriptRecovery.VConditions
