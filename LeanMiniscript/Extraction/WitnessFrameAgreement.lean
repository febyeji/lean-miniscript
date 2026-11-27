import LeanMiniscript.Extraction.TapscriptRecovery.KeyAgreement

/-!
# Witness frame agreement for sane witness scripts

The induction tracks the path from each executed fragment to the published satisfaction.
At a threshold, every true row either has an unsigned candidate or discloses a checked
signature belonging to that row. The selected positions and the execution have the same
count, so child frame agreement determines the complete witness.
-/

namespace LeanMiniscript.Extraction.TapscriptRecovery

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open OrI ThresholdCanonical ThresholdRun UnsignedSelection
open OriginCounts SlotLocal CompositeRows BChoiceMaterial
open VConditions KAgreement ThresholdUnit ThresholdAlt
open BooleanRows SuccessUniform ThresholdRows

variable {sc : ScriptContext}

private theorem executionContext_of_sane {sane : SaneFragment sc} {child env flags args other consumed}
    (ctx : TapscriptWitness.ExecutionContextIn sc sane child env flags args other consumed)
    (encoding : env.EncodingSound flags) :
    OrI.ExecutionContextIn sc sane.checked.fragment child env flags args other consumed := by
  refine ⟨ctx.sound, encoding, ctx.version, ctx.modeled, ?_, ?_, ctx.canonical, ctx.thirdParty,
    ctx.keys, ctx.locks, ctx.items⟩
  · cases sc with
    | tapscript => exact TapscriptWitness.wellFormed_keySizes _ sane.checked.wellFormed
    | p2wsh => exact ⟨sane, rfl, ctx.recover.2⟩
  · cases sc with
    | tapscript => exact ctx.recover
    | p2wsh => exact ctx.recover.1

/-- Recover the full threshold frame by locating each true execution row in the canonical selection. -/
theorem threshold_agreement {k children env flags pa po cm mm} (sane : SaneFragment sc)
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (path : SlotPath (.thresh k children) sane.checked.fragment)
    (ih : SmallerCheckedBIn sc (.thresh k children) sane.checked.fragment env flags pa po) :
    CheckedTrueRowAgreementBIn sc (.thresh k children) sane.checked.fragment env flags pa po := by
  intro own expected top rest ctx nodup canonical bounded run truth _
  have parent : TapscriptWitness.ExecutionContextIn sc sane (.thresh k children) env flags pa po own :=
    ⟨ctx.sound, ctx.version, ctx.modeled, ctx.canonical, ctx.thirdParty, (by
        cases sc with
        | tapscript => exact ctx.recover
        | p2wsh =>
          obtain ⟨_, _, disjoint⟩ := ctx.material
          exact ⟨ctx.recover, disjoint⟩),
      ctx.childKeys, ctx.childLocks, ctx.consumedIn⟩
  have subcontext {child block}
      (sub : TapscriptWitness.ExecutionContextIn sc sane child env flags pa po block) :
      OrI.ExecutionContextIn sc sane.checked.fragment child env flags pa po block :=
    executionContext_of_sane sub ctx.encoding
  apply TapscriptWitness.threshold_frame_of_children typed wf mal nm parent path
    canonical bounded run truth
  · intro child member block suffix value base mods ct sub row bound positive
    obtain ⟨_, hm, _, cw, ch, cn, _⟩ :=
      TapscriptWitness.threshold_children_static typed wf mal nm child member
    have ev : ExecutionEvidence child env flags block := by
      cases row with
      | b rx =>
        exact uniform_B_execution child mods hm ct cw ch cn sane.checked.fragment env flags
          pa po block value suffix (subcontext sub) bound rx positive
      | w saved order size rx =>
        apply ambientExecutionW_step ct cw ch cn (fun inner _ => uniform_B_execution inner)
          sane.checked.fragment env flags pa po block saved value suffix order (subcontext sub) _ rx positive
        simpa [List.forall_mem_cons] using And.intro size bound
    rcases ev with ⟨c, eq, flag⟩ | sig
    · exact .inl (by simp [CandidatePair.unsignedSat, eq, flag])
    · exact .inr sig
  · intro child member block suffix value base mods expected ct cd cu free sub row bound projection
    obtain ⟨_, hm, _, cw, ch, cn, ce⟩ :=
      TapscriptWitness.threshold_children_static typed wf mal nm child member
    have childPath := path_trans (SlotPath.of_threshold_member k member .here) path
    have childNodup := childPath.noDup sane.noDuplicateKeys
    have unchecked (neg : castToBool value = false) : ¬ CheckedSignature child env flags block := by
      rintro ⟨sig, hs, key, hk, checked⟩
      exact free neg sig hs key hk checked
    cases row with
    | b rx =>
      cases pos : castToBool value with
      | true =>
        have agree := ih child (threshold_child_smaller member) mods hm ct cw ch cn childPath
        exact agree_B ct cw ch cn agree (subcontext sub) childNodup (by simpa [satisfy, pos] using projection) bound rx pos
      | false =>
        exact row_agreement_noChecked ct cw ch cn cd cu ce (subcontext sub) childNodup
          projection bound rx (unchecked pos)
    | w saved order size rx =>
      have inputBound : ∀ item ∈ saved :: (block.toInitialStack ++ suffix),
          item.size ≤ maxScriptElementSize := by
        simpa [List.forall_mem_cons] using And.intro size bound
      cases pos : castToBool value with
      | true =>
        have agree := agree_W_from_smaller_B ct cw ch cn childPath
          (fun c small => ih c (Nat.lt_trans small (threshold_child_smaller member)))
        exact agree block expected saved value suffix order (subcontext sub) childNodup
          (by simpa [satisfy, pos] using projection) inputBound rx pos
      | false =>
        have result := (rowCompleteW_of_typed ct cw ch cn cd cu ce sane.checked.fragment env flags
          pa po block saved value suffix order (subcontext sub) childNodup inputBound rx (unchecked pos)).2
        exact Option.some.inj (result.symm.trans projection)

/-- Checked B and V frames agree with the selected witness at every descendant of the sane root. -/
theorem checked_agreement (sane : SaneFragment sc) {env : SatEnv}
    {flags : ScriptFlags} {pa po : Witness}
    (wf : sane.checked.fragment.WellFormed sc) (nodup : sane.checked.fragment.keys.Nodup)
    (origin : (satisfactionCandidates sane.checked.fragment env).sat.CanonicalWhenUsable)
    (fragment : CoreFragment) (path : SlotPath fragment sane.checked.fragment) :
    (∀ cx mx, HasType sc fragment ⟨.B, cx⟩ → fragment.WellFormed sc →
      HasMalleability sc fragment mx → mx.nonMalleable = true →
      CheckedTrueRowAgreementBIn sc fragment sane.checked.fragment env flags pa po) ∧
    (∀ cx mx, HasType sc fragment ⟨.V, cx⟩ → fragment.WellFormed sc →
      HasMalleability sc fragment mx → mx.nonMalleable = true →
      CheckedTrueRowAgreementVIn sc fragment sane.checked.fragment env flags pa po) := by
  have ihB : SmallerCheckedBIn sc fragment sane.checked.fragment env flags pa po := by
    intro child smaller cm mm ct cw ch cn subpath
    exact (checked_agreement sane wf nodup origin child subpath).1 cm mm ct cw ch cn
  have ihV : SmallerCheckedVIn sc fragment sane.checked.fragment env flags pa po := by
    intro child smaller cm mm ct cw ch cn subpath
    exact (checked_agreement sane wf nodup origin child subpath).2 cm mm ct cw ch cn
  constructor
  · intro cm mm ct cw ch cn
    apply checkedB_threshold_step ct cw ch cn path wf nodup origin ihB ihV
    rintro ⟨k, cs, rfl⟩
    exact threshold_agreement sane ct cw ch cn path ihB
  · intro cm mm ct cw ch cn
    exact checkedV_from_smaller_B ct cw ch cn path nodup ihB
termination_by sizeOf fragment


/-- At the script root, child frame agreement recovers the complete published witness. -/
theorem root_frame (sane : SaneFragment sc) {env : SatEnv} {flags : ScriptFlags}
    {args observed : Witness} {cm : CorrectnessModifiers}
    (typed : HasType sc sane.checked.fragment ⟨.B, cm⟩)
    (ctx : TapscriptWitness.ExecutionContextIn sc sane sane.checked.fragment env flags args observed observed)
    (encoding : env.EncodingSound flags)
    (bounded : ∀ item ∈ observed.toInitialStack, item.size ≤ maxScriptElementSize)
    (top : StackElement)
    (run : Eval (compile sane.checked.fragment) observed.toInitialStack [] flags env.txCtx (.success [top] []))
    (truth : castToBool top = true) : observed = args := by
  have wf := sane.checked.wellFormed
  have origin := (malleabilityCandidateSound env wf typed sane.hasMalleability).canonicalSat sane.nonMalleable
  have context := executionContext_of_sane ctx encoding
  have agree := (checked_agreement sane (flags := flags) (pa := args) (po := observed) wf
    sane.noDuplicateKeys origin sane.checked.fragment .here).1 cm _ typed wf sane.hasMalleability sane.nonMalleable
  exact agree_B typed wf sane.hasMalleability sane.nonMalleable agree context sane.noDuplicateKeys
    ctx.canonical (rest := []) (by simpa using bounded) (by simpa using run) truth

end LeanMiniscript.Extraction.TapscriptRecovery
