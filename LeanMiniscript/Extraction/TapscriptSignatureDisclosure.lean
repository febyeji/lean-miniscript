import LeanMiniscript.Extraction.TapscriptThresholdAgreement
import LeanMiniscript.Extraction.TapscriptUnsignedWitness

/-! Trace an eligible checked signature from the root witness to a particular
    subfragment. At each branch the other children have disjoint key sets.
    A canonical dissatisfaction can only contribute selectors and public keys. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

inductive Wrapper where
  | a | s | c | d | v | j | n

def wrap : Wrapper → CoreFragment → CoreFragment
  | .a, x => .a x | .s, x => .s x | .c, x => .c x | .d, x => .d x
  | .v, x => .v x | .j, x => .j x | .n, x => .n x

inductive Binary where
  | and_v | and_b | or_b | or_c | or_d | or_i

def join : Binary → CoreFragment → CoreFragment → CoreFragment
  | .and_v, x, y => .and_v x y | .and_b, x, y => .and_b x y
  | .or_b, x, y => .or_b x y | .or_c, x, y => .or_c x y
  | .or_d, x, y => .or_d x y | .or_i, x, y => .or_i x y

@[simp] theorem wrap_keys (op : Wrapper) (x : CoreFragment) : (wrap op x).keys = x.keys := by
  cases op <;> rfl

@[simp] theorem join_keys (op : Binary) (x y : CoreFragment) :
    (join op x y).keys = x.keys ++ y.keys := by cases op <;> rfl

@[simp] theorem keysList_append (before after : List CoreFragment) :
    CoreFragment.keysList (before ++ after) = CoreFragment.keysList before ++ CoreFragment.keysList after := by
  induction before with
  | nil => rfl
  | cons head tail ih => simp [CoreFragment.keysList, ih, List.append_assoc]

/-- Syntactic occurrence retains the enclosing branch, independently of
which candidate or actual runtime path was selected. -/
inductive FragmentPath (target : CoreFragment) : CoreFragment → Prop where
  | here : FragmentPath target target
  | wrapper {x : CoreFragment} (op : Wrapper) (path : FragmentPath target x) : FragmentPath target (wrap op x)
  | left {x y : CoreFragment} (op : Binary) (path : FragmentPath target x) : FragmentPath target (join op x y)
  | right {x y : CoreFragment} (op : Binary) (path : FragmentPath target y) : FragmentPath target (join op x y)
  | condition {x y z : CoreFragment} (path : FragmentPath target x) : FragmentPath target (.andor x y z)
  | thenBranch {x y z : CoreFragment} (path : FragmentPath target y) : FragmentPath target (.andor x y z)
  | elseBranch {x y z : CoreFragment} (path : FragmentPath target z) : FragmentPath target (.andor x y z)
  | threshold {x : CoreFragment} (k : Nat) (before after : List CoreFragment)
      (path : FragmentPath target x) : FragmentPath target (.thresh k (before ++ x :: after))

theorem FragmentPath.keys {target parent : CoreFragment} (path : FragmentPath target parent) :
    ∀ key ∈ target.keys, key ∈ parent.keys := by
  induction path with
  | here => exact fun _ h => h
  | wrapper op _ ih => simpa using ih
  | left op _ ih => intro key hk; rw [join_keys]; exact List.mem_append_left _ (ih key hk)
  | right op _ ih => intro key hk; rw [join_keys]; exact List.mem_append_right _ (ih key hk)
  | condition _ ih => intro key hk; exact List.mem_append_left _ (List.mem_append_left _ (ih key hk))
  | thenBranch _ ih => intro key hk; exact List.mem_append_left _ (List.mem_append_right _ (ih key hk))
  | elseBranch _ ih => intro key hk; exact List.mem_append_right _ (ih key hk)
  | threshold k before after _ ih =>
    intro key hk
    simp only [CoreFragment.keys, keysList_append, CoreFragment.keysList]
    exact List.mem_append_right _ (List.mem_append_left _ (ih key hk))

theorem FragmentPath.noDup {target parent : CoreFragment} (path : FragmentPath target parent) :
    parent.keys.Nodup → target.keys.Nodup := by
  induction path with
  | here => exact id
  | wrapper op _ ih => simpa using ih
  | left op _ ih => intro nd; rw [join_keys] at nd; exact ih (List.pairwise_append.mp nd).1
  | right op _ ih => intro nd; rw [join_keys] at nd; exact ih (List.pairwise_append.mp nd).2.1
  | condition _ ih => intro nd; exact ih (List.pairwise_append.mp (List.pairwise_append.mp nd).1).1
  | thenBranch _ ih => intro nd; exact ih (List.pairwise_append.mp (List.pairwise_append.mp nd).1).2.1
  | elseBranch _ ih => intro nd; exact ih (List.pairwise_append.mp nd).2.1
  | threshold k before after _ ih =>
    intro nd
    simp only [CoreFragment.keys, keysList_append, CoreFragment.keysList] at nd
    exact ih (List.pairwise_append.mp (List.pairwise_append.mp nd).2.1).1

theorem FragmentPath.of_threshold_member {target child : CoreFragment} {children : List CoreFragment}
    (k : Nat) (member : child ∈ children) (path : FragmentPath target child) :
    FragmentPath target (.thresh k children) := by
  obtain ⟨before, after, eq⟩ := List.append_of_mem member
  rw [eq]
  exact .threshold k before after path

/-- The predicate records actual material membership independently of its
candidate origin. Encoding size is supplied by the actual successful slot. -/
def LocalSlot (target : CoreFragment) (env : SatEnv) (own expected : Witness)
    (item : StackElement) : Prop :=
  item ∈ own → ∀ key ∈ target.keys,
    verifySigFor checkSig checkSchnorrSig env.txCtx item key.bytes = true →
    (item.size = 64 ∨ item.size = 65) → item ∈ expected

private theorem localSlot_short {target : CoreFragment} {env : SatEnv} {own expected : Witness}
    {item : StackElement} (short : item.size < 64) : LocalSlot target env own expected item := by
  intro _ _ _ _ size
  omega

private theorem foreign_pair {root : SaneFragment .tapscript} {target other : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} (context : ExecutionContext root target env flags pa po own)
    (keysIn : ∀ key ∈ other.keys, key ∈ root.checked.fragment.keys)
    (distinct : ∀ key ∈ target.keys, ∀ otherKey ∈ other.keys, key ≠ otherKey) :
    PairItems (LocalSlot target env po expected) (satisfactionCandidates other env) := by
  apply all_items other
  · exact localSlot_short (by decide)
  · exact localSlot_short (by decide)
  · intro key member
    exact localSlot_short (by rw [(wellFormed_keySizes _ root.checked.wellFormed) key (keysIn key member)]; decide)
  · intro otherKey otherMem sig selected actual key keyMem valid _size
    exact (context.thirdParty.1 sig actual
      key (context.keys key keyMem) otherKey (keysIn otherKey otherMem)
      (distinct key keyMem otherKey otherMem) valid (context.sound.signatureValid selected)).elim
  · intro lock _member preimage selected
    exact localSlot_short (by rw [(context.sound.preimageMatches selected).1]; decide)

/-- Keep origin and usability as separate, checked guards. -/
def CanonicalItems (P : StackElement → Prop) (result : CandidateResult) : Prop :=
  ∀ candidate, result = .candidate candidate → candidate.status = .usable →
    candidate.origin = .canonical → Items P candidate.witness

def CanonicalPairItems (P : StackElement → Prop) (pair : CandidatePair) : Prop :=
  CanonicalItems P pair.sat ∧ CanonicalItems P pair.dsat

private theorem c_impossible (P : StackElement → Prop) : CanonicalItems P .impossible := by
  intro candidate eq
  cases eq

private theorem c_usable {P : StackElement → Prop} {witness : Witness} (items : Items P witness)
    (signed : Bool) : CanonicalItems P (.usable witness signed) := by
  intro candidate eq _ _
  cases eq
  exact items

private theorem c_of_supports {P : StackElement → Prop} {result : CandidateResult}
    (supported : result.Supports (Items P)) : CanonicalItems P result := by
  intro candidate eq usable _origin
  exact supported candidate.witness (by simp [eq, CandidateResult.usableWitness?, usable])

private theorem c_combine {P : StackElement → Prop} {left right : CandidateResult}
    (hl : CanonicalItems P left) (hr : CanonicalItems P right) : CanonicalItems P (left.combine right) := by
  cases left with
  | impossible => exact c_impossible P
  | candidate left =>
    cases right with
    | impossible => exact c_impossible P
    | candidate right =>
      intro candidate eq usable origin
      cases eq
      obtain ⟨ul, ur⟩ := (SatisfactionCandidate.combine_status_eq_usable_iff left right).mp usable
      obtain ⟨cl, cr⟩ := (SatisfactionCandidate.combine_origin_eq_canonical_iff left right).mp origin
      exact items_combine (hl left rfl ul cl) (hr right rfl ur cr)

private theorem c_select {P : StackElement → Prop} {left right : CandidateResult}
    (hl : CanonicalItems P left) (hr : CanonicalItems P right) : CanonicalItems P (left.select right) := by
  cases left with
  | impossible => exact hr
  | candidate left =>
    cases right with
    | impossible => exact hl
    | candidate right =>
      intro candidate eq usable origin
      have eq' : left.select right = candidate := CandidateResult.candidate.inj eq
      rcases SatisfactionCandidate.select_usable_source left right (eq' ▸ usable) with
        ⟨chosen, selectedUsable⟩ | ⟨chosen, selectedUsable⟩
      · rw [← eq', chosen] at origin ⊢
        exact hl left rfl selectedUsable origin
      · rw [← eq', chosen] at origin ⊢
        exact hr right rfl selectedUsable origin

private theorem c_selector {P : StackElement → Prop} {result : CandidateResult} {selector : StackElement}
    (supported : CanonicalItems P result) (item : P selector) : CanonicalItems P (result.withSelector selector) := by
  cases result with
  | impossible => exact c_impossible P
  | candidate value =>
    intro candidate eq usable origin
    cases eq
    intro element member
    rcases List.mem_append.mp member with member | member
    · exact supported value rfl usable origin element member
    · exact List.mem_singleton.mp member ▸ item

private theorem c_noncanonical (P : StackElement → Prop) (result : CandidateResult) :
    CanonicalItems P result.markNonCanonical := by
  cases result with
  | impossible => exact c_impossible P
  | candidate value => intro candidate eq _ origin; cases eq; cases origin

private theorem c_overcomplete (P : StackElement → Prop) (result : CandidateResult) :
    CanonicalItems P result.markOvercomplete := by
  cases result with
  | impossible => exact c_impossible P
  | candidate value => intro candidate eq usable; cases eq; cases usable

private theorem c_zero {P : StackElement → Prop} {pairs : List CandidatePair}
    (rows : ∀ row ∈ pairs, CanonicalItems P row.dsat) : CanonicalItems P (CandidatePair.selectExactly 0 pairs) := by
  have helper : ∀ revPairs : List CandidatePair,
      (∀ row ∈ revPairs.reverse, CanonicalItems P row.dsat) →
      CanonicalItems P (CandidatePair.selectExactly 0 revPairs.reverse) := by
    intro revPairs
    induction revPairs with
    | nil => intro _; exact c_usable (by simp [Items]) false
    | cons pair tail ih =>
      intro rows
      simp only [List.reverse_cons] at rows ⊢
      rw [CandidatePair.selectExactly_append, CandidatePair.extendCounts_getD_zero]
      exact c_combine (ih (fun row member => rows row (List.mem_append_left _ member)))
        (rows pair (by simp))
  simpa using helper pairs.reverse (by simpa using rows)

private theorem c_threshold_dsat {P : StackElement → Prop} {states : List CandidateResult} (k : Nat)
    (zero : CanonicalItems P (states.getD 0 .impossible)) :
    CanonicalItems P (CandidatePair.thresholdDissatisfaction k states) := by
  cases states with
  | nil => exact c_impossible P
  | cons head tail =>
    change CanonicalItems P head at zero
    unfold CandidatePair.thresholdDissatisfaction
    have helper : ∀ (entries : List (CandidateResult × Nat)) (previous : CandidateResult),
        CanonicalItems P previous → CanonicalItems P (entries.foldl
          (fun selected entry => if entry.2 = k then selected else selected.select entry.1.markOvercomplete) previous) := by
      intro entries
      induction entries with
      | nil => exact fun _ h => h
      | cons entry entries ih =>
        intro previous supported
        simp only [List.foldl_cons]
        apply ih
        split
        · exact supported
        · exact c_select supported (c_overcomplete P _)
    exact helper _ _ zero

/-- Canonical usable dsat material contains only empty/selector/key items.
Noncanonical usable dsat and raw DONTUSE rows are outside this statement. -/
theorem canonical_dsat_items (fragment : CoreFragment) (env : SatEnv) {P : StackElement → Prop}
    (empty : P falseElement) (one : P trueElement) (keys : ∀ key ∈ fragment.keys, P key.bytes) :
    CanonicalItems P (satisfactionCandidates fragment env).dsat := by
  cases fragment with
  | zero => exact c_usable (by simp [Items]) false
  | one | older _ | after _ | or_c _ _ | v _ => exact c_impossible P
  | pk_k key => exact c_usable (by simpa [Items] using empty) false
  | pk_h key =>
    exact c_usable (show Items P [falseElement, key.bytes] from by
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact empty
      · exact List.mem_singleton.mp member ▸ keys key (by simp [CoreFragment.keys])) false
  | sha256 _ | hash256 _ | ripemd160 _ | hash160 _ =>
    intro candidate eq usable
    cases eq
    cases usable
  | and_v X Y => exact c_noncanonical P _
  | and_b X Y =>
    exact c_select (c_select (c_combine
      (canonical_dsat_items X env empty one (fun key h => keys key (List.mem_append_left _ h)))
      (canonical_dsat_items Y env empty one (fun key h => keys key (List.mem_append_right _ h))))
      (c_overcomplete P _)) (c_overcomplete P _)
  | or_b X Y | or_d X Y =>
    exact c_combine
      (canonical_dsat_items X env empty one (fun key h => keys key (List.mem_append_left _ h)))
      (canonical_dsat_items Y env empty one (fun key h => keys key (List.mem_append_right _ h)))
  | or_i X Y =>
    exact c_select
      (c_selector (canonical_dsat_items X env empty one (fun key h => keys key (List.mem_append_left _ h))) one)
      (c_selector (canonical_dsat_items Y env empty one (fun key h => keys key (List.mem_append_right _ h))) empty)
  | andor X Y Z =>
    exact c_select (c_combine
      (canonical_dsat_items X env empty one (fun key h => keys key (List.mem_append_left _ (List.mem_append_left _ h))))
      (canonical_dsat_items Z env empty one (fun key h => keys key (List.mem_append_right _ h))))
      (c_noncanonical P _)
  | a X | s X | c X | n X => exact canonical_dsat_items X env empty one keys
  | d X => exact c_usable (by simpa [Items] using empty) false
  | j X => exact c_select (c_usable (by simpa [Items] using empty) false) (c_noncanonical P _)
  | multi k keyList =>
    simp only [satisfactionCandidates, legacyMultiCandidates]
    split
    · exact c_impossible P
    · exact c_usable (by intro item h; exact (List.mem_replicate.mp h).2 ▸ empty) false
  | multi_a k keyList =>
    simp only [satisfactionCandidates, multiACandidates]
    split
    · exact c_usable (by intro item h; exact (List.mem_replicate.mp h).2 ▸ empty) false
    · exact c_impossible P
  | thresh k children =>
    simp only [satisfactionCandidates]
    split
    · apply c_threshold_dsat (P := P) (states := CandidatePair.countCandidates (satisfactionCandidatesList children env)) k
      apply c_zero (P := P) (pairs := satisfactionCandidatesList children env)
      intro row member
      rw [satisfactionCandidatesList_eq_map] at member
      obtain ⟨child, childMem, rfl⟩ := List.mem_map.mp member
      exact canonical_dsat_items child env empty one
        (fun key hk => keys key (threshold_keys_member childMem key hk))
    · exact c_impossible P
termination_by sizeOf fragment
decreasing_by
  all_goals simp_all
  all_goals first | omega | (have small := List.sizeOf_lt_of_mem childMem; omega)

private theorem canonical_assemble {P : StackElement → Prop} (positions : List Nat)
    (children : List CandidatePair) (supported : ∀ child ∈ children, CanonicalPairItems P child)
    (endIndex count : Nat) :
    CanonicalItems P (CandidatePair.assembleThreshold positions endIndex count children) := by
  induction children generalizing endIndex count with
  | nil =>
    cases count with
    | zero => exact c_usable (by simp [Items]) false
    | succ _ => exact c_impossible P
  | cons child tail ih =>
    have prior := ih (fun c h => supported c (List.mem_cons_of_mem _ h))
    have current := supported child (.head _)
    simp only [CandidatePair.assembleThreshold]
    split
    · cases count with
      | zero => exact c_impossible P
      | succ n => exact c_combine (prior _ n) current.1
    · exact c_combine (prior _ count) current.2

private theorem canonical_threshold_sat {P : StackElement → Prop} {children : List CandidatePair}
    (supported : ∀ child ∈ children, CanonicalPairItems P child) (count : Nat) :
    CanonicalItems P (CandidatePair.thresholdSatisfaction count children) := by
  rcases CandidatePair.thresholdSatisfaction_cases count children with fallback | ⟨positions, _, _, assembled, eq⟩
  · rw [fallback]
    intro candidate eq usable
    generalize (CandidatePair.selectExactly count children) = r at eq
    cases r <;> cases eq
    cases usable
  · rw [eq, ← assembled]
    exact canonical_assemble positions _ (fun c h => supported c (List.mem_reverse.mp h)) _ _

private theorem c_pair_wrap {P : StackElement → Prop} {env : SatEnv} {x : CoreFragment}
    (empty : P falseElement) (one : P trueElement)
    (hx : CanonicalPairItems P (satisfactionCandidates x env)) (op : Wrapper) :
    CanonicalPairItems P (satisfactionCandidates (wrap op x) env) := by
  cases op with
  | a | s | c | n => exact hx
  | v => exact ⟨hx.1, c_impossible P⟩
  | d => exact ⟨c_selector hx.1 one, c_usable (by simpa [Items] using empty) false⟩
  | j => exact ⟨hx.1, c_select (c_usable (by simpa [Items] using empty) false) (c_noncanonical P _)⟩

private theorem c_pair_join {P : StackElement → Prop} {env : SatEnv} {x y : CoreFragment}
    (empty : P falseElement) (one : P trueElement)
    (hx : CanonicalPairItems P (satisfactionCandidates x env)) (hy : CanonicalPairItems P (satisfactionCandidates y env))
    (op : Binary) : CanonicalPairItems P (satisfactionCandidates (join op x y) env) := by
  cases op with
  | and_v => exact ⟨c_combine hx.1 hy.1, c_noncanonical P _⟩
  | and_b => exact ⟨c_combine hx.1 hy.1,
      c_select (c_select (c_combine hx.2 hy.2) (c_overcomplete P _)) (c_overcomplete P _)⟩
  | or_b => exact ⟨c_select (c_select (c_combine hx.1 hy.2) (c_combine hx.2 hy.1)) (c_overcomplete P _),
      c_combine hx.2 hy.2⟩
  | or_c => exact ⟨c_select hx.1 (c_combine hx.2 hy.1), c_impossible P⟩
  | or_d => exact ⟨c_select hx.1 (c_combine hx.2 hy.1), c_combine hx.2 hy.2⟩
  | or_i => exact ⟨c_select (c_selector hx.1 one) (c_selector hy.1 empty),
      c_select (c_selector hx.2 one) (c_selector hy.2 empty)⟩

private theorem c_pair_andor {P : StackElement → Prop} {env : SatEnv} {x y z : CoreFragment}
    (hx : CanonicalPairItems P (satisfactionCandidates x env)) (hy : CanonicalPairItems P (satisfactionCandidates y env))
    (hz : CanonicalPairItems P (satisfactionCandidates z env)) :
    CanonicalPairItems P (satisfactionCandidates (.andor x y z) env) :=
  ⟨c_select (c_combine hx.1 hy.1) (c_combine hx.2 hz.1),
    c_select (c_combine hx.2 hz.2) (c_noncanonical P _)⟩

private theorem c_pair_thresh {P : StackElement → Prop} {env : SatEnv} {k : Nat} {children : List CoreFragment}
    (rows : ∀ row ∈ satisfactionCandidatesList children env, CanonicalPairItems P row) :
    CanonicalPairItems P (satisfactionCandidates (.thresh k children) env) := by
  simp only [satisfactionCandidates]
  split
  · exact ⟨canonical_threshold_sat rows k, c_threshold_dsat k (c_zero (fun row h => (rows row h).2))⟩
  · exact ⟨c_impossible P, c_impossible P⟩

private theorem c_foreign_pair {root : SaneFragment .tapscript} {target other : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} (context : ExecutionContext root target env flags pa po own)
    (keysIn : ∀ key ∈ other.keys, key ∈ root.checked.fragment.keys)
    (distinct : ∀ key ∈ target.keys, ∀ otherKey ∈ other.keys, key ≠ otherKey) :
    CanonicalPairItems (LocalSlot target env po expected) (satisfactionCandidates other env) :=
  ⟨c_of_supports (foreign_pair context keysIn distinct).1,
    c_of_supports (foreign_pair context keysIn distinct).2⟩

private theorem c_path_pair {root : SaneFragment .tapscript} {target parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} (path : FragmentPath target parent)
    (context : ExecutionContext root target env flags pa po own)
    (base : CanonicalPairItems (LocalSlot target env po expected) (satisfactionCandidates target env)) :
    (∀ key ∈ parent.keys, key ∈ root.checked.fragment.keys) → parent.keys.Nodup →
    CanonicalPairItems (LocalSlot target env po expected) (satisfactionCandidates parent env) := by
  have empty : LocalSlot target env po expected falseElement := localSlot_short (by decide)
  have one : LocalSlot target env po expected trueElement := localSlot_short (by decide)
  induction path with
  | here => intro _ _; exact base
  | wrapper op _ ih =>
    intro keysIn nodup
    exact c_pair_wrap empty one (ih (by simpa using keysIn) (by simpa using nodup)) op
  | @left x y op path ih =>
    intro keysIn nodup
    rw [join_keys] at keysIn nodup
    obtain ⟨nx, ny, separate⟩ := List.pairwise_append.mp nodup
    exact c_pair_join empty one (ih (fun key hk => keysIn key (List.mem_append_left _ hk)) nx)
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => separate key (path.keys key hk) other ho)) op
  | @right x y op path ih =>
    intro keysIn nodup
    rw [join_keys] at keysIn nodup
    obtain ⟨nx, ny, separate⟩ := List.pairwise_append.mp nodup
    exact c_pair_join empty one
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ hk))
        (fun key hk other ho => Ne.symm (separate other ho key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_right _ hk)) ny) op
  | @condition x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, ny, sx⟩ := List.pairwise_append.mp nxy
    exact c_pair_andor
      (ih (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk))) nx)
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun key hk other ho => sx key (path.keys key hk) other ho))
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => sxy key (List.mem_append_left _ (path.keys key hk)) other ho))
  | @thenBranch x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, ny, sx⟩ := List.pairwise_append.mp nxy
    exact c_pair_andor
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun key hk other ho => Ne.symm (sx other ho key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk))) ny)
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => sxy key (List.mem_append_right _ (path.keys key hk)) other ho))
  | @elseBranch x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    exact c_pair_andor
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun key hk other ho => Ne.symm (sxy other (List.mem_append_left _ ho) key (path.keys key hk))))
      (c_foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun key hk other ho => Ne.symm (sxy other (List.mem_append_right _ ho) key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_right _ hk)) nz)
  | @threshold x k before after path ih =>
    intro keysIn nodup
    simp only [CoreFragment.keys, keysList_append, CoreFragment.keysList] at keysIn nodup
    obtain ⟨nb, nxa, separateBefore⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, na, separateAfter⟩ := List.pairwise_append.mp nxa
    apply c_pair_thresh
    intro row member
    rw [satisfactionCandidatesList_eq_map] at member
    obtain ⟨fragment, fragmentMem, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp fragmentMem with beforeMem | tailMem
    · apply c_foreign_pair context
      · intro key hk
        exact keysIn key (List.mem_append_left _ (threshold_keys_member beforeMem key hk))
      · intro key hk other ho
        exact Ne.symm (separateBefore other (threshold_keys_member beforeMem other ho)
          key (List.mem_append_left _ (path.keys key hk)))
    · rcases List.mem_cons.mp tailMem with rfl | afterMem
      · exact ih (fun key hk => keysIn key (List.mem_append_right _ (List.mem_append_left _ hk))) nx
      · apply c_foreign_pair context
        · intro key hk
          exact keysIn key (List.mem_append_right _ (List.mem_append_right _ (threshold_keys_member afterMem key hk)))
        · intro key hk other ho
          exact separateAfter key (path.keys key hk) other (threshold_keys_member afterMem other ho)

private theorem c_hole {child : CoreFragment} {env : SatEnv} {own expected : Witness}
    (sizes : ∀ key ∈ child.keys, key.bytes.size = 32)
    (projection : satisfy child env = some expected) :
    CanonicalPairItems (LocalSlot child env own expected) (satisfactionCandidates child env) := by
  constructor
  · intro candidate eq usable _origin item member _actual _key _keyMem _valid _size
    have same : candidate.witness = expected := by
      simpa [satisfy, eq, CandidateResult.usableWitness?, usable] using projection
    simpa [same] using member
  · exact canonical_dsat_items child env (localSlot_short (by decide))
      (localSlot_short (by decide)) (fun key member => localSlot_short (by rw [sizes key member]; decide))

/-- A signature checked for a key of this subfragment and available to the
    third party occurs in the subfragment's own usable satisfaction. -/
theorem ExecutionContext.signature_in_satisfaction {root child env flags arguments other consumed expected}
    (ctx : ExecutionContext root child env flags arguments other consumed)
    (path : FragmentPath child root.checked.fragment) (canonical : satisfy child env = some expected)
    {sig : StackElement} {key : PubKey} (eligible : sig ∈ other) (keyMem : key ∈ child.keys)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    sig ∈ expected := by
  obtain ⟨_, wf, typed⟩ := root.validMiniscript
  have origin := (malleabilityCandidateSound env wf typed root.hasMalleability).canonicalSat root.nonMalleable
  have sizes := fun key hk => wellFormed_keySizes _ wf key (ctx.keys key hk)
  have supported := c_path_pair path ctx (c_hole sizes canonical) (fun _ h => h) root.noDuplicateKeys
  have valid := verifySigFor_of_checkSigWithEncoding checked
  have disclosed := ctx.thirdParty.2.1 sig eligible key (ctx.keys _ keyMem) valid
  have projection := ctx.canonical
  unfold satisfy at projection
  cases eq : (satisfactionCandidates root.checked.fragment env).sat with
  | impossible => simp [eq, CandidateResult.usableWitness?] at projection
  | candidate candidate =>
    cases status : candidate.status with
    | dontUse => simp [eq, CandidateResult.usableWitness?, status] at projection
    | usable =>
      have same : candidate.witness = arguments := by simpa [eq, CandidateResult.usableWitness?, status] using projection
      exact supported.1 candidate eq status (origin candidate eq status) sig
        (same.symm ▸ disclosed) eligible key keyMem valid
        (successful_slot_size ctx.version (sizes key keyMem) checked)

end LeanMiniscript.Extraction.TapscriptWitness
