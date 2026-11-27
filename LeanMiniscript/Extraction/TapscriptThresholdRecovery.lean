import LeanMiniscript.Extraction.P2WSHRecovery.Frames

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript CandidatePair

variable {sc : ScriptContext}

private theorem threshold_malleability_children {k : Nat} {children : List CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true) :
    ∃ childMods, HasMalleabilityList sc children childMods ∧
      MalleabilityModifiers.allNonMalleable childMods = true ∧
      MalleabilityModifiers.allE childMods = true ∧ MalleabilityModifiers.countNonS childMods ≤ k := by
  cases mal with
  | thresh childrenMal =>
    obtain ⟨allNm, allE, count⟩ := (boolAnd3_eq_true _ _ _).mp nm
    exact ⟨_, childrenMal, allNm, allE, by simpa [MalleabilityModifiers.atMostNonS] using count⟩

private theorem list_child_static {children : List CoreFragment} {types : List MiniType}
    {childMods : List MalleabilityModifiers}
    (typed : HasTypeList sc children types)
    (wf : CoreFragment.allWellFormed sc children)
    (mal : HasMalleabilityList sc children childMods)
    (nm : MalleabilityModifiers.allNonMalleable childMods = true)
    (expressive : MalleabilityModifiers.allE childMods = true) :
    ∀ child ∈ children, ∃ ty mm, HasType sc child ty ∧ child.WellFormed sc ∧
      HasMalleability sc child mm ∧ mm.nonMalleable = true ∧ mm.e = true := by
  cases typed with
  | nil => simp
  | cons headTyped tailTyped =>
    cases mal with
    | cons headMal tailMal =>
      obtain ⟨headNm, tailNm⟩ := Bool.and_eq_true_iff.mp nm
      obtain ⟨headE, tailE⟩ := Bool.and_eq_true_iff.mp expressive
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, headTyped, wf.1, headMal, headNm, headE⟩
      · exact list_child_static tailTyped wf.2 tailMal tailNm tailE child member
termination_by sizeOf children

theorem threshold_children_static {k : Nat} {children : List CoreFragment}
    {mods : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType sc (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true) :
    ∀ child ∈ children, ∃ ty cm, HasType sc child ty ∧ child.WellFormed sc ∧
      HasMalleability sc child cm ∧ cm.nonMalleable = true ∧ cm.e = true := by
  obtain ⟨childMods, childrenMal, allNm, allE, _⟩ := threshold_malleability_children mal nm
  cases typed with
  | thresh firstTyped _ _ tailTyped _ _ _ =>
    exact list_child_static (.cons firstTyped tailTyped) wf.2.1 childrenMal allNm allE

/-- The retained source row for a checked key is selected, even when the
    threshold is nested inside another branch. -/
theorem checked_threshold_position_of_path {k children root env flags args other consumed canonical cm mm positions}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ctx : ExecutionContextIn sc root (.thresh k children) env flags args other consumed)
    (path : FragmentPath (.thresh k children) root.checked.fragment)
    (sat : satisfy (.thresh k children) env = some canonical)
    (chosen : thresholdPositions k (satisfactionCandidatesList children env) = some positions)
    {i child sig key} (childAt : children[i]? = some child) (member : key ∈ child.keys) (eligible : sig ∈ other)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    i ∈ positions := by
  have childMem := List.mem_of_getElem? childAt
  have keyIn := threshold_keys_member childMem key member
  have available : sig ∈ canonical := by
    cases sc with
    | tapscript => exact ExecutionContext.signature_in_satisfaction ctx path sat eligible keyIn checked
    | p2wsh => exact P2WSHRecovery.signature_in_satisfaction ctx path sat eligible keyIn checked
  have selected : (thresholdSatisfaction k (satisfactionCandidatesList children env)).usableWitness? = some canonical := by
    simpa [satisfy, satisfactionCandidates, threshold_candidate_guard wf] using sat
  obtain ⟨frame, row, contains⟩ := checked_threshold_source ctx (path.noDup root.noDuplicateKeys)
    selected chosen childAt member available eligible checked
  by_cases included : i ∈ positions
  · exact included
  exfalso
  obtain ⟨_, _, ct, cw, ch, cn, ce⟩ := threshold_children_static typed wf mal nm child childMem
  have dsat : dissatisfy child env = some frame := by simpa [dissatisfy, included] using row
  cases sc with
  | tapscript =>
    exact expressive_dsat_excludes_signature ct cw ch cn ce ctx.sound ctx.version dsat
      (wellFormed_keySizes child cw key member) checked contains
  | p2wsh =>
    exact P2WSHRecovery.expressive_dsat_excludes_checked ctx ct cw ch cn ce
      (fun k hk => ctx.keys k (threshold_keys_member childMem k hk)) dsat checked contains

private theorem ExecutedRows.true_at {env flags bases children bits blocks}
    (rows : ExecutedRows env flags bases children bits blocks) {i : Nat} {child : CoreFragment}
    (childAt : children[i]? = some child) (positive : bits[i]? = some true) :
    ∃ base block rest top, bases[i]? = some base ∧ block ∈ blocks ∧ ExecutedRow env flags child block rest top base ∧
      (∀ item ∈ block.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) ∧ castToBool top = true := by
  induction rows generalizing i with
  | nil => simp at childAt
  | cons row bound _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at childAt positive
      subst child
      exact ⟨_, _, _, _, rfl, .head _, row, bound, positive⟩
    | succ i =>
      obtain ⟨base, block, rest, top, baseAt, mem, run, bounded, truth⟩ := ih childAt positive
      exact ⟨base, block, rest, top, baseAt, .tail _ mem, run, bounded, truth⟩

/-- The child induction hypotheses concern only the execution of the child
    itself. Selection, disjointness, and disclosure are discharged at the parent. -/
theorem threshold_frame_of_children {k children root env flags args other consumed canonical cm mm rest top}
    (typed : HasType sc (.thresh k children) ⟨.B, cm⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (mal : HasMalleability sc (.thresh k children) mm) (nm : mm.nonMalleable = true)
    (ctx : ExecutionContextIn sc root (.thresh k children) env flags args other consumed)
    (path : FragmentPath (.thresh k children) root.checked.fragment)
    (sat : satisfy (.thresh k children) env = some canonical)
    (bounded : ∀ item ∈ consumed.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.thresh k children)) (consumed.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true)
    (evidence : ∀ child ∈ children, ∀ {block rest top base mods},
      HasType sc child ⟨base, mods⟩ → ExecutionContextIn sc root child env flags args other block →
      ExecutedRow env flags child block rest top base →
      (∀ item ∈ block.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) → castToBool top = true →
      (satisfactionCandidates child env).unsignedSat = true ∨
        ∃ sig ∈ block, ∃ key ∈ child.keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true)
    (recover : ∀ {child : CoreFragment}, child ∈ children →
      ∀ {block rest top base mods expected}, HasType sc child ⟨base, mods⟩ →
      mods.d = true → mods.u = true →
      (castToBool top = false → ∀ sig ∈ block, ∀ key ∈ child.keys,
        checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes ≠ .ok true) →
      ExecutionContextIn sc root child env flags args other block →
      ExecutedRow env flags child block rest top base →
      (∀ item ∈ block.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
      (if castToBool top then (satisfactionCandidates child env).sat else (satisfactionCandidates child env).dsat).usableWitness? =
        some expected → block = expected) : consumed = canonical := by
  apply threshold_frame_of_rows typed wf ctx sat bounded run truth
  case recover =>
    intro i child block rest top base own positions childAt chosen matched typedChild childCtx row bound selected
    obtain ⟨mods, ct, cd, cu⟩ := typedChild
    apply recover (List.mem_of_getElem? childAt) ct cd cu _ childCtx row bound selected
    intro neg sig hs key hk checked
    have selected := checked_threshold_position_of_path typed wf mal nm ctx path sat chosen childAt hk (childCtx.items _ hs) checked
    simp [neg, selected] at matched
  intro first tail bits blocks positions shape rows wire chosen i child childAt positive signed
  obtain ⟨_, block, _, _, baseAt, seen, row, bound, childTruth⟩ := rows.true_at childAt positive
  have member := List.mem_of_getElem? childAt
  have childCtx : ExecutionContextIn sc root child env flags args other block := by
    apply ctx.restrict (threshold_keys_member member) (threshold_locks_member member)
    intro item occurs
    have inside : item ∈ (blocks.map Witness.toInitialStack).flatten :=
      List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, seen, rfl⟩, by simpa [Witness.toInitialStack] using occurs⟩
    rw [← wire] at inside
    simpa [Witness.toInitialStack] using inside
  obtain ⟨_, ct, _, _⟩ := threshold_type_at typed shape childAt baseAt
  rcases evidence child member ct childCtx row bound childTruth with unsigned | ⟨sig, hs, key, hk, checked⟩
  · simp [signed] at unsigned
  · exact checked_threshold_position_of_path typed wf mal nm ctx path sat chosen childAt hk (childCtx.items _ hs) checked

end LeanMiniscript.Extraction.TapscriptWitness
