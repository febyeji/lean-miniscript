import LeanMiniscript.Extraction.TapscriptThresholdCount

/-! Relate a threshold's selected positions to its serialized witness. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Miniscript CandidatePair

/-- The bit at a source index says whether assembly takes that child's sat. -/
def positionFlags (positions : List Nat) (arity : Nat) : List Bool :=
  (List.range arity).map fun i => decide (i ∈ positions)

private theorem assembleThreshold_layout {positions : List Nat} {prior : List CandidatePair}
    {count : Nat} {witness : Witness}
    (selected : (assembleThreshold positions prior.length count prior).usableWitness? = some witness) :
    ∃ frames, ChoiceFrames prior.reverse (positionFlags positions prior.length) frames ∧
      (positionFlags positions prior.length).count true = count ∧
      witness.toInitialStack = (frames.map Witness.toInitialStack).flatten := by
  induction prior generalizing count witness with
  | nil =>
    cases count <;> simp [assembleThreshold, CandidateResult.usable, CandidateResult.usableWitness?] at selected
    subst witness
    exact ⟨[], .nil, rfl, rfl⟩
  | cons row prior ih =>
    simp only [List.length_cons, assembleThreshold, Nat.add_one_sub_one] at selected
    simp only [List.length_cons, List.reverse_cons, positionFlags, List.range_succ, List.map_append,
      List.map_singleton]
    split at selected
    next takes =>
      cases count with
      | zero => contradiction
      | succ n =>
        obtain ⟨_, w, kept, child, rfl⟩ := CandidateResult.combine_usableWitness_iff.mp selected
        obtain ⟨frames, layout, quota, assembled⟩ := ih kept
        refine ⟨frames ++ [w], by simpa [takes, positionFlags] using layout.snocSat child, ?_, ?_⟩
        · simpa [takes, positionFlags] using quota
        · simp [assembled]
    next skips =>
      obtain ⟨_, w, kept, child, rfl⟩ := CandidateResult.combine_usableWitness_iff.mp selected
      obtain ⟨frames, layout, quota, assembled⟩ := ih kept
      exact ⟨frames ++ [w], by simpa [skips, positionFlags] using layout.snocDsat child,
        by simpa [skips, positionFlags] using quota, by simp [assembled]⟩

/-- The selected usable witness exposes one child witness per position, the
    exact number of true decisions, and every unsigned child as a true bit. -/
theorem selected_threshold_layout {count : Nat} {children : List CandidatePair} {witness : Witness}
    (selected : (thresholdSatisfaction count children).usableWitness? = some witness) :
    ∃ bits frames, ChoiceFrames children bits frames ∧ bits.count true = count ∧
      (∀ (i : Nat) (child : CandidatePair), children[i]? = some child → child.unsignedSat = true → bits[i]? = some true) ∧
      witness.toInitialStack = (frames.map Witness.toInitialStack).flatten := by
  obtain ⟨positions, chosen, assembled⟩ := thresholdSatisfaction_usable_positions selected
  rw [← List.length_reverse (as := children)] at assembled
  obtain ⟨frames, layout, quota, stacked⟩ := assembleThreshold_layout assembled
  simp only [List.reverse_reverse, List.length_reverse] at layout quota
  refine ⟨_, frames, layout, quota, ?_, stacked⟩
  intro i child lookup unsigned
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have mem := (thresholdPositions_spec chosen).2 i child lookup unsigned
  simp [positionFlags, List.getElem?_range bound, mem]

private theorem count_le_and_eq_of_inclusion {observed chosen : List Bool}
    (arity : observed.length = chosen.length)
    (included : ∀ (i : Nat), observed[i]? = some true → chosen[i]? = some true) :
    observed.count true ≤ chosen.count true ∧
      (observed.count true = chosen.count true → observed = chosen) := by
  induction observed generalizing chosen with
  | nil =>
    cases chosen <;> simp_all
  | cons actual observed ih =>
    cases chosen with
    | nil => simp at arity
    | cons expected chosen =>
      obtain ⟨le, eq⟩ := ih (by simpa using arity)
        (fun i h => included (i + 1) (by simpa using h))
      have head := included 0
      cases actual <;> cases expected <;> simp_all <;> omega

private theorem choiceFrames_projections {children bits frames}
    (choices : ChoiceFrames children bits frames) :
    List.zipWith (fun row bit => (if bit then row.sat else row.dsat).usableWitness?)
      children bits = frames.map some := by
  induction choices with
  | nil => rfl
  | snocSat prior selected ih =>
    rw [List.zipWith_append prior.lengths.1.symm]
    simp [ih, selected]
  | snocDsat prior selected ih =>
    rw [List.zipWith_append prior.lengths.1.symm]
    simp [ih, selected]

/-- Once each observed true row with HASSIG is known to occupy a selected
    position, unsigned inclusion and the exact count force identical decisions.
    Recovering each observed child witness at that decision then determines the
    entire wire-order witness. -/
theorem threshold_witness_agreement {count : Nat} {children : List CandidatePair}
    {original other : Witness} {observed : List Bool} {blocks : List Witness}
    (selected : (thresholdSatisfaction count children).usableWitness? = some original)
    (observedRows : ChoiceFrames children observed blocks) (exactCount : observed.count true = count)
    (wire : other.toInitialStack = (blocks.map Witness.toInitialStack).flatten)
    (signedIncluded : ∀ positions, thresholdPositions count children = some positions →
      ∀ (i : Nat) (child : CandidatePair), children[i]? = some child → observed[i]? = some true →
        child.unsignedSat = false → i ∈ positions) :
    other = original := by
  obtain ⟨positions, chosen, assembled⟩ := thresholdSatisfaction_usable_positions selected
  rw [← List.length_reverse (as := children)] at assembled
  obtain ⟨frames, layout, quota, stacked⟩ := assembleThreshold_layout assembled
  simp only [List.length_reverse, List.reverse_reverse] at layout quota
  have bitsEq : observed = positionFlags positions children.length := by
    apply (count_le_and_eq_of_inclusion (observedRows.lengths.1.trans layout.lengths.1.symm) ?_).2
      (exactCount.trans quota.symm)
    intro i positive
    have bound : i < children.length := observedRows.lengths.1 ▸ (List.getElem?_eq_some_iff.mp positive).1
    have lookup := List.getElem?_eq_getElem (l := children) bound
    have mem : i ∈ positions := by
      cases hs : children[i].unsignedSat with
      | true => exact (thresholdPositions_spec chosen).2 i _ lookup hs
      | false => exact signedIncluded positions chosen i _ lookup positive hs
    simp [positionFlags, List.getElem?_range bound, mem]
  rw [bitsEq] at observedRows
  have blocksEq := (List.map_inj_right (fun _ _ => Option.some.inj)).mp
    ((choiceFrames_projections observedRows).symm.trans (choiceFrames_projections layout))
  rw [blocksEq, ← stacked] at wire
  simpa [Witness.toInitialStack] using congrArg List.reverse wire

private theorem ExecutedRows.lengths {env flags bases children bits blocks}
    (rows : ExecutedRows env flags bases children bits blocks) :
    bits.length = children.length ∧ blocks.length = children.length := by
  induction rows <;> simp_all

private theorem ExecutedRows.agree {env flags bases children bits blocks}
    (rows : ExecutedRows env flags bases children bits blocks) {expected : List Witness}
    (projection : List.zipWith (fun child bit =>
        (if bit then (satisfactionCandidates child env).sat else (satisfactionCandidates child env).dsat).usableWitness?)
      children bits = expected.map some)
    (recover : ∀ base ∈ bases, ∀ child ∈ children, ∀ block ∈ blocks, ∀ rest top canonical,
      ExecutedRow env flags child block rest top base →
      (∀ item ∈ Witness.toInitialStack block ++ rest, item.size ≤ maxScriptElementSize) →
      (if castToBool top then (satisfactionCandidates child env).sat else (satisfactionCandidates child env).dsat).usableWitness? =
        some canonical → block = canonical) : blocks = expected := by
  induction rows generalizing expected with
  | nil => cases expected <;> simp_all
  | cons row bounded tail ih =>
    cases expected with
    | nil => simp at projection
    | cons head expected =>
      obtain ⟨first, later⟩ := List.cons.inj projection
      rw [recover _ (by simp) _ (by simp) _ (by simp) _ _ head row bounded first,
        ih later (fun b hb c hc w hw => recover b (by simp [hb]) c (by simp [hc]) w (by simp [hw]))]

private theorem threshold_keys_member {child : CoreFragment} {children : List CoreFragment}
    (member : child ∈ children) : ∀ key ∈ child.keys, key ∈ CoreFragment.keysList children := by
  induction children with
  | nil => simp at member
  | cons first children ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact fun _ h => List.mem_append_left _ h
    · exact fun _ h => List.mem_append_right _ (ih member _ h)

private theorem threshold_locks_member {child : CoreFragment} {children : List CoreFragment}
    (member : child ∈ children) : ∀ lock ∈ child.hashLocks, lock ∈ CoreFragment.hashLocksList children := by
  induction children with
  | nil => simp at member
  | cons first children ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact fun _ h => List.mem_append_left _ h
    · exact fun _ h => List.mem_append_right _ (ih member _ h)


private theorem threshold_key_position_unique {children : List CoreFragment} {i j : Nat}
    {first second : CoreFragment} {key : PubKey} (nodup : (CoreFragment.keysList children).Nodup)
    (left : children[i]? = some first) (right : children[j]? = some second)
    (firstKey : key ∈ first.keys) (secondKey : key ∈ second.keys) : i = j := by
  induction children generalizing i j with
  | nil => simp at left
  | cons head tail ih =>
    have parts := List.pairwise_append.mp nodup
    cases i <;> cases j <;> simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq, Nat.succ.injEq]
    case zero.succ =>
      exact False.elim (parts.2.2 key firstKey key (threshold_keys_member (List.mem_of_getElem? right) key secondKey) rfl)
    case succ.zero =>
      exact False.elim (parts.2.2 key secondKey key (threshold_keys_member (List.mem_of_getElem? left) key firstKey) rfl)
    case succ.succ => exact ih parts.2.1 left right

/-- A checked signature disclosed by a usable threshold witness occurs in the
    canonical frame for its own key's position, including when that position
    was dissatisfied. This tracks the source through both wire-order reversals. -/
theorem checked_threshold_source {root env flags args other consumed k children canonical positions}
    (ctx : ExecutionContext root (.thresh k children) env flags args other consumed)
    (nodup : (CoreFragment.keysList children).Nodup)
    (selected : (thresholdSatisfaction k (satisfactionCandidatesList children env)).usableWitness? = some canonical)
    (chosen : thresholdPositions k (satisfactionCandidatesList children env) = some positions)
    {i : Nat} {child : CoreFragment} {sig : StackElement} {key : PubKey}
    (childAt : children[i]? = some child) (member : key ∈ child.keys)
    (available : sig ∈ canonical) (eligible : sig ∈ other)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    ∃ frame, (if i ∈ positions then (satisfactionCandidates child env).sat else (satisfactionCandidates child env).dsat).usableWitness? =
      some frame ∧ sig ∈ frame := by
  obtain ⟨p, positionsEq, assembled⟩ := thresholdSatisfaction_usable_positions selected
  rw [chosen] at positionsEq
  cases positionsEq
  rw [← List.length_reverse (as := satisfactionCandidatesList children env)] at assembled
  obtain ⟨frames, layout, _, wire⟩ := assembleThreshold_layout assembled
  simp only [List.reverse_reverse, List.length_reverse] at layout
  have inWire : sig ∈ (frames.map Witness.toInitialStack).flatten := by
    rw [← wire]
    simpa [Witness.toInitialStack] using available
  obtain ⟨stack, stacked, sigMem⟩ := List.mem_flatten.mp inWire
  obtain ⟨frame, frameMem, rfl⟩ := List.mem_map.mp stacked
  obtain ⟨j, bound, frameEq⟩ := List.getElem_of_mem frameMem
  have sigMem : sig ∈ frame := by simpa [Witness.toInitialStack] using sigMem
  have childBound : j < children.length := by simpa [layout.lengths.2] using bound
  let source := children[j]
  have actual := congrArg (fun xs : List (Option Witness) => xs[j]?) (choiceFrames_projections layout)
  have sourceRow : (if j ∈ positions then (satisfactionCandidates source env).sat else (satisfactionCandidates source env).dsat).usableWitness? =
      some frame := by
    simpa [source, List.getElem?_zipWith, List.getElem?_eq_getElem childBound, List.getElem?_eq_getElem bound,
      positionFlags, List.getElem?_range childBound, frameEq] using actual
  have keySizes := wellFormed_keySizes _ root.checked.wellFormed
  have inRoot : ∀ k ∈ source.keys, k ∈ root.checked.fragment.keys :=
    fun k h => ctx.keys k (threshold_keys_member (List.getElem_mem childBound) k h)
  have testedKey := ctx.keys key (threshold_keys_member (List.mem_of_getElem? childAt) key member)
  have material : Material source env sig := by
    split at sourceRow
    · exact (candidates_material source env).1 frame sourceRow sig sigMem
    · exact (candidates_material source env).2 frame sourceRow sig sigMem
  obtain ⟨signer, signerKey, selectedSig⟩ := material_signature_of_size ctx.sound
    (fun k h => keySizes k (inRoot k h)) material (successful_slot_size ctx.version (keySizes key testedKey) checked)
  have signerEq : signer = key := by
    by_cases eq : signer = key
    · exact eq
    · exact (ctx.thirdParty.1 sig eligible signer (inRoot signer signerKey) key testedKey eq
        (ctx.sound.signatureValid selectedSig) (verifySigFor_of_checkSigWithEncoding checked)).elim
  subst signer
  have ij := threshold_key_position_unique nodup childAt (List.getElem?_eq_getElem childBound) member signerKey
  subst i
  have same : child = source := by simpa [source, List.getElem?_eq_getElem childBound] using childAt.symm
  exact ⟨frame, same ▸ sourceRow, sigMem⟩


/-- At the threshold root, the third-party rules put every checked signature
    in the published witness. A child whose usable dsat omits that signature
    must have been selected at its source position. -/
theorem checked_threshold_position_selected {root : SaneFragment .tapscript} {env flags args other consumed k children positions}
    (shape : root.checked.fragment = .thresh k children)
    (ctx : ExecutionContext root (.thresh k children) env flags args other consumed)
    (chosen : thresholdPositions k (satisfactionCandidatesList children env) = some positions)
    {i : Nat} {child : CoreFragment} {sig : StackElement} {key : PubKey}
    (childAt : children[i]? = some child) (member : key ∈ child.keys)
    (disclosed : sig ∈ other)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true)
    (dsat : ∀ frame, (satisfactionCandidates child env).dsat.usableWitness? = some frame → sig ∉ frame) :
    i ∈ positions := by
  have wf := root.checked.wellFormed
  have sel := ctx.canonical
  have nodup := root.noDuplicateKeys
  rw [shape] at wf sel nodup
  have selected : (thresholdSatisfaction k (satisfactionCandidatesList children env)).usableWitness? = some args := by
    simpa [satisfy, satisfactionCandidates, threshold_candidate_guard wf] using sel
  have available := ctx.thirdParty.2.1 sig disclosed key
    (ctx.keys key (threshold_keys_member (List.mem_of_getElem? childAt) key member))
    (verifySigFor_of_checkSigWithEncoding checked)
  obtain ⟨frame, row, contains⟩ := checked_threshold_source ctx nodup selected chosen childAt member available disclosed checked
  by_cases included : i ∈ positions
  · exact included
  · exact (dsat frame (by simpa [included] using row) contains).elim

/-- Lift child row recovery and inclusion of observed signed positions through
    a compiled threshold, keeping the same sane root and third-party witness.
    The execution yields the observed bits, child frames, and both cardinalities. -/
theorem frameUnique_thresh_of_rows {k : Nat} {children : List CoreFragment}
    (signed : ∀ {root env flags args other consumed canonical first tail bits blocks positions},
      ExecutionContext root (.thresh k children) env flags args other consumed →
      satisfy (.thresh k children) env = some canonical →
      children = first :: tail →
      ExecutedRows env flags (.B :: List.replicate tail.length .W) children bits blocks →
      consumed.toInitialStack = (blocks.map Witness.toInitialStack).flatten →
      thresholdPositions k (satisfactionCandidatesList children env) = some positions →
      ∀ (i : Nat) child, children[i]? = some child → bits[i]? = some true →
        (satisfactionCandidates child env).unsignedSat = false → i ∈ positions)
    (recover : ∀ {root env flags args other} {child : CoreFragment}, child ∈ children →
      ∀ {block rest top base canonical}, ExecutionContext root child env flags args other block →
      ExecutedRow env flags child block rest top base →
      (∀ item ∈ Witness.toInitialStack block ++ rest, item.size ≤ maxScriptElementSize) →
      (if castToBool top then (satisfactionCandidates child env).sat else (satisfactionCandidates child env).dsat).usableWitness? =
        some canonical → block = canonical) : FrameUnique .B (.thresh k children) := by
  intro root env flags args other consumed canonical cm typed wf ctx sel rest bounded top run truth
  obtain ⟨first, tail, bits, blocks, shape, rows, quota, wire⟩ :=
    threshold_executed_rows typed wf ctx.version bounded run truth
  have selected : (thresholdSatisfaction k (satisfactionCandidatesList children env)).usableWitness? = some canonical := by
    simpa [satisfy, satisfactionCandidates, threshold_candidate_guard wf] using sel
  obtain ⟨positions, chosen, assembled⟩ := thresholdSatisfaction_usable_positions selected
  rw [← List.length_reverse (as := satisfactionCandidatesList children env)] at assembled
  obtain ⟨frames, layout, targetCount, stacked⟩ := assembleThreshold_layout assembled
  simp only [List.length_reverse, List.reverse_reverse] at layout targetCount
  let table := satisfactionCandidatesList children env
  have tableLength : table.length = children.length := by simp [table]
  have bitsEq : bits = positionFlags positions table.length := by
    apply (count_le_and_eq_of_inclusion (rows.lengths.1.trans (tableLength.symm.trans layout.lengths.1.symm)) ?_).2
      (quota.trans targetCount.symm)
    intro i positive
    have bound : i < children.length := rows.lengths.1 ▸ (List.getElem?_eq_some_iff.mp positive).1
    have childAt := List.getElem?_eq_getElem (l := children) bound
    have rowAt : table[i]? = some (satisfactionCandidates children[i] env) := by simp [table, childAt]
    have mem : i ∈ positions := by
      cases unsigned : (satisfactionCandidates children[i] env).unsignedSat with
      | true => exact (thresholdPositions_spec chosen).2 i _ rowAt unsigned
      | false => exact signed ctx sel shape rows wire chosen i _ childAt positive unsigned
    simp [positionFlags, List.getElem?_range bound, mem]
  have projection := choiceFrames_projections layout
  rw [← bitsEq] at projection
  have blocksEq : blocks = frames := by
    apply rows.agree
    · simpa [List.zipWith_map_left] using projection
    · intro base _ child member block seen tailStack value generated row bound selected
      apply recover member (root := root) (args := args) (other := other) _ row bound selected
      apply ctx.restrict
      · intro key occurs
        exact threshold_keys_member member key occurs
      · intro lock occurs
        exact threshold_locks_member member lock occurs
      · intro item occurs
        have inside : item ∈ (blocks.map Witness.toInitialStack).flatten := by
          apply List.mem_flatten.mpr
          exact ⟨_, List.mem_map.mpr ⟨_, seen, rfl⟩, by simpa [Witness.toInitialStack] using occurs⟩
        rw [← wire] at inside
        simpa [Witness.toInitialStack] using inside
  rw [blocksEq, ← stacked] at wire
  simpa [Witness.toInitialStack] using congrArg List.reverse wire

end LeanMiniscript.Extraction.TapscriptWitness
