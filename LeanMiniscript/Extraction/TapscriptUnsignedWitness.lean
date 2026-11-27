import LeanMiniscript.Extraction.TapscriptWitnessMaterial
import LeanMiniscript.Miniscript.MalleabilitySatisfactionProofs

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- Material support conditional on the actual candidate's HASSIG flag.
This includes DONTUSE rows and does not assert their usability. -/
def UnsignedItems (P : StackElement → Prop) (result : CandidateResult) : Prop :=
  ∀ candidate, result = .candidate candidate → candidate.hasSig = false → Items P candidate.witness

def UnsignedPairItems (P : StackElement → Prop) (pair : CandidatePair) : Prop :=
  UnsignedItems P pair.sat ∧ UnsignedItems P pair.dsat

private theorem unsigned_impossible (P : StackElement → Prop) : UnsignedItems P .impossible := by
  intro candidate eq
  cases eq

private theorem unsigned_usable {P : StackElement → Prop} {witness : Witness} {hasSig : Bool}
    (supported : hasSig = false → Items P witness) : UnsignedItems P (.usable witness hasSig) := by
  intro candidate eq unsigned
  cases eq
  exact supported unsigned

private theorem unsigned_dontUse {P : StackElement → Prop} {witness : Witness} {hasSig : Bool}
    {origin : CandidateOrigin} (supported : hasSig = false → Items P witness) :
    UnsignedItems P (.dontUse witness hasSig origin) := by
  intro candidate eq unsigned
  cases eq
  exact supported unsigned

private theorem UnsignedItems.combine {P : StackElement → Prop} {left right : CandidateResult}
    (hl : UnsignedItems P left) (hr : UnsignedItems P right) : UnsignedItems P (left.combine right) := by
  cases left with
  | impossible => exact unsigned_impossible P
  | candidate left =>
    cases right with
    | impossible => exact unsigned_impossible P
    | candidate right =>
      intro candidate eq unsigned
      cases eq
      have flags : left.hasSig = false ∧ right.hasSig = false := Bool.or_eq_false_iff.mp unsigned
      exact items_combine (hl left rfl flags.1) (hr right rfl flags.2)

private theorem UnsignedItems.select {P : StackElement → Prop} {left right : CandidateResult}
    (hl : UnsignedItems P left) (hr : UnsignedItems P right) : UnsignedItems P (left.select right) := by
  cases left with
  | impossible => exact hr
  | candidate left =>
    cases right with
    | impossible => exact hl
    | candidate right =>
      intro candidate eq unsigned
      cases eq
      have flags : (left.hasSig && right.hasSig) = false := by simpa using unsigned
      cases l : left.hasSig <;> cases r : right.hasSig
      · have hl' := hl left rfl l
        have hr' := hr right rfl r
        simp only [SatisfactionCandidate.select, l, r]
        change Items P (if left.cost ≤ right.cost then left else right).witness
        split <;> assumption
      · simpa [SatisfactionCandidate.select, l, r] using hl left rfl l
      · simpa [SatisfactionCandidate.select, l, r] using hr right rfl r
      · simp [l, r] at flags

private theorem UnsignedItems.selector {P : StackElement → Prop} {result : CandidateResult}
    {selector : StackElement} (supported : UnsignedItems P result) (hs : P selector) :
    UnsignedItems P (result.withSelector selector) := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner =>
    intro candidate eq unsigned
    cases eq
    intro item member
    rcases List.mem_append.mp member with member | member
    · exact supported inner rfl unsigned item member
    · exact List.mem_singleton.mp member ▸ hs

private theorem UnsignedItems.markDontUse {P : StackElement → Prop} {result : CandidateResult}
    (supported : UnsignedItems P result) : UnsignedItems P result.markDontUse := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner => intro candidate eq unsigned; cases eq; exact supported inner rfl unsigned

private theorem UnsignedItems.markNonCanonical {P : StackElement → Prop} {result : CandidateResult}
    (supported : UnsignedItems P result) : UnsignedItems P result.markNonCanonical := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner => intro candidate eq unsigned; cases eq; exact supported inner rfl unsigned

private theorem UnsignedItems.markOvercomplete {P : StackElement → Prop} {result : CandidateResult}
    (supported : UnsignedItems P result) : UnsignedItems P result.markOvercomplete := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner => intro candidate eq unsigned; cases eq; exact supported inner rfl unsigned

private theorem UnsignedItems.requireNonemptyRuntimeTop {P : StackElement → Prop} {result : CandidateResult}
    (supported : UnsignedItems P result) : UnsignedItems P result.requireNonemptyRuntimeTop := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner =>
    simp only [CandidateResult.requireNonemptyRuntimeTop]
    split
    · exact unsigned_impossible P
    · split
      · exact unsigned_impossible P
      · exact supported

private theorem UnsignedItems.finalizeLegacyMulti {P : StackElement → Prop} {result : CandidateResult}
    (supported : UnsignedItems P result) (empty : P falseElement) :
    UnsignedItems P (finalizeLegacyMulti result) := by
  cases result with
  | impossible => exact unsigned_impossible P
  | candidate inner =>
    intro candidate eq unsigned item member
    cases eq
    rcases List.mem_cons.mp member with rfl | member
    · exact empty
    · exact supported inner rfl unsigned item (List.mem_reverse.mp member)

private theorem zipWith_select_unsigned {P : StackElement → Prop} {left right : List CandidateResult}
    (hl : ∀ r ∈ left, UnsignedItems P r) (hr : ∀ r ∈ right, UnsignedItems P r) :
    ∀ r ∈ List.zipWith CandidateResult.select left right, UnsignedItems P r := by
  induction left generalizing right with
  | nil => simp
  | cons a as ih =>
    cases right with
    | nil => simp
    | cons b bs =>
      intro r member
      rcases List.mem_cons.mp member with rfl | member
      · exact (hl a (by simp)).select (hr b (by simp))
      · exact ih (fun r h => hl r (by simp [h])) (fun r h => hr r (by simp [h])) r member

private theorem extendCounts_unsigned {P : StackElement → Prop} {states : List CandidateResult} {child : CandidatePair}
    (hs : ∀ r ∈ states, UnsignedItems P r) (hc : UnsignedPairItems P child) :
    ∀ r ∈ CandidatePair.extendCounts states child, UnsignedItems P r := by
  apply zipWith_select_unsigned
  · intro r member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨previous, hp, rfl⟩ := List.mem_map.mp member
      exact (hs previous hp).combine hc.2
    · exact List.mem_singleton.mp member ▸ unsigned_impossible P
  · intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact unsigned_impossible P
    · obtain ⟨previous, hp, rfl⟩ := List.mem_map.mp member
      exact (hs previous hp).combine hc.1

private theorem foldCounts_unsigned {P : StackElement → Prop} {children : List CandidatePair}
    (hc : ∀ child ∈ children, UnsignedPairItems P child) (states : List CandidateResult)
    (hs : ∀ r ∈ states, UnsignedItems P r) :
    ∀ r ∈ children.foldl CandidatePair.extendCounts states, UnsignedItems P r := by
  induction children generalizing states with
  | nil => exact hs
  | cons child children ih =>
    exact ih (fun c h => hc c (by simp [h])) _ (extendCounts_unsigned hs (hc child (by simp)))

private theorem countCandidates_unsigned {P : StackElement → Prop} {children : List CandidatePair}
    (hc : ∀ child ∈ children, UnsignedPairItems P child) :
    ∀ r ∈ CandidatePair.countCandidates children, UnsignedItems P r := by
  apply foldCounts_unsigned hc
  intro r member
  have eq := List.mem_singleton.mp member
  subst r
  exact unsigned_usable (by simp [Items])

private theorem getD_unsigned {P : StackElement → Prop} {states : List CandidateResult}
    (hs : ∀ r ∈ states, UnsignedItems P r) (n : Nat) :
    UnsignedItems P (states.getD n .impossible) := by
  induction states generalizing n with
  | nil => exact unsigned_impossible P
  | cons head tail ih =>
    cases n with
    | zero => exact hs head (by simp)
    | succ n => exact ih (fun r h => hs r (by simp [h])) n

private theorem exact_unsigned {P : StackElement → Prop} {children : List CandidatePair}
    (hc : ∀ child ∈ children, UnsignedPairItems P child) (n : Nat) :
    UnsignedItems P (CandidatePair.selectExactly n children) :=
  getD_unsigned (countCandidates_unsigned hc) n

private theorem assembleThreshold_unsigned {P : StackElement → Prop} (positions : List Nat)
    (children : List CandidatePair) (supported : ∀ child ∈ children, UnsignedPairItems P child)
    (endIndex count : Nat) :
    UnsignedItems P (CandidatePair.assembleThreshold positions endIndex count children) := by
  induction children generalizing endIndex count with
  | nil =>
    cases count with
    | zero => exact unsigned_usable (by simp [Items])
    | succ _ => exact unsigned_impossible P
  | cons child tail ih =>
    have prior := ih (fun c h => supported c (List.mem_cons_of_mem _ h))
    have current := supported child (.head _)
    simp only [CandidatePair.assembleThreshold]
    split
    · cases count with
      | zero => exact unsigned_impossible P
      | succ n => exact (prior _ n).combine current.1
    · exact (prior _ count).combine current.2

private theorem threshold_sat_unsigned {P : StackElement → Prop} {children : List CandidatePair}
    (supported : ∀ child ∈ children, UnsignedPairItems P child) (count : Nat) :
    UnsignedItems P (CandidatePair.thresholdSatisfaction count children) := by
  rcases CandidatePair.thresholdSatisfaction_cases count children with fallback | ⟨positions, _, _, assembled, eq⟩
  · rw [fallback]
    exact (exact_unsigned supported count).markDontUse
  · rw [eq, ← assembled]
    exact assembleThreshold_unsigned positions _ (fun c h => supported c (List.mem_reverse.mp h)) _ _

private theorem threshold_fold_unsigned {P : StackElement → Prop} (k : Nat)
    (entries : List (CandidateResult × Nat)) (canonical : CandidateResult)
    (hs : ∀ entry ∈ entries, UnsignedItems P entry.1) (hc : UnsignedItems P canonical) :
    UnsignedItems P (entries.foldl
      (fun selected entry => if entry.2 = k then selected else selected.select entry.1.markOvercomplete) canonical) := by
  induction entries generalizing canonical with
  | nil => exact hc
  | cons entry entries ih =>
    apply ih _ (fun e h => hs e (by simp [h]))
    dsimp only
    split
    · exact hc
    · exact hc.select (hs entry (by simp)).markOvercomplete

private theorem threshold_dsat_unsigned {P : StackElement → Prop} {states : List CandidateResult}
    (hs : ∀ r ∈ states, UnsignedItems P r) (k : Nat) :
    UnsignedItems P (CandidatePair.thresholdDissatisfaction k states) := by
  cases states with
  | nil => exact unsigned_impossible P
  | cons head tail =>
    apply threshold_fold_unsigned k _ _ _ (hs head (by simp))
    intro entry member
    exact hs entry.1 (List.mem_cons_of_mem _ (List.fst_mem_of_mem_zipIdx member))

private theorem key_unsigned {P : StackElement → Prop} {env : SatEnv} {key : PubKey} {tail : Witness}
    (empty : P falseElement) (ht : Items P tail) : UnsignedPairItems P (keyCandidates key tail env) := by
  constructor
  · simp only [keyCandidates]
    cases selected : env.signatureFor key with
    | none => exact unsigned_impossible P
    | some sig => exact unsigned_usable (by intro h; cases h)
  · apply unsigned_usable
    intro _ item member
    rcases List.mem_cons.mp member with rfl | member
    · exact empty
    · exact ht item member

private theorem hash_unsigned {P : StackElement → Prop} {env : SatEnv} {lock : HashLock}
    (preimages : ∀ p, env.preimageFor lock = some p → P p)
    (nonpreimage : P (env.nonPreimageFor lock)) : UnsignedPairItems P (hashCandidates lock env) := by
  constructor
  · simp only [hashCandidates]
    cases selected : env.preimageFor lock with
    | none => exact unsigned_impossible P
    | some p =>
      apply unsigned_usable
      intro _ item member
      exact List.mem_singleton.mp member ▸ preimages p selected
  · apply unsigned_dontUse
    intro _ item member
    exact List.mem_singleton.mp member ▸ nonpreimage

private theorem multi_a_unsigned {P : StackElement → Prop} {env : SatEnv} {k : Nat} {keys : List PubKey}
    (empty : P falseElement) : UnsignedPairItems P (multiACandidates k keys env) := by
  unfold multiACandidates
  split
  · constructor
    · apply exact_unsigned
      intro child member
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
      exact key_unsigned empty (by simp [Items])
    · apply unsigned_usable
      intro _ item member
      exact (List.mem_replicate.mp member).2 ▸ empty
  · exact ⟨unsigned_impossible P, unsigned_impossible P⟩

private theorem legacy_unsigned {P : StackElement → Prop} {env : SatEnv} {k : Nat} {keys : List PubKey}
    (empty : P falseElement) : UnsignedPairItems P (legacyMultiCandidates k keys env) := by
  unfold legacyMultiCandidates
  split
  · exact ⟨unsigned_impossible P, unsigned_impossible P⟩
  · constructor
    · apply UnsignedItems.finalizeLegacyMulti _ empty
      apply exact_unsigned
      intro child member
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
      constructor
      · simp only [legacyMultiKeyChoice]
        cases selected : env.signatureFor key with
        | none => exact unsigned_impossible P
        | some sig => exact unsigned_usable (by intro h; cases h)
      · exact unsigned_usable (by simp [Items])
    · apply unsigned_usable
      intro _ item member
      exact (List.mem_replicate.mp member).2 ▸ empty

mutual
/-- Every unsigned candidate is assembled without signature-source material.
Nonpreimages are retained explicitly because raw DONTUSE rows are covered. -/
theorem all_unsigned_items (fragment : CoreFragment) {env : SatEnv} {P : StackElement → Prop}
    (empty : P falseElement) (one : P trueElement)
    (km : ∀ key ∈ fragment.keys, P key.bytes)
    (pm : ∀ lock ∈ fragment.hashLocks, ∀ p, env.preimageFor lock = some p → P p)
    (np : ∀ lock ∈ fragment.hashLocks, P (env.nonPreimageFor lock)) :
    UnsignedPairItems P (satisfactionCandidates fragment env) := by
  cases fragment with
  | zero => exact ⟨unsigned_impossible P, unsigned_usable (by simp [Items])⟩
  | one => exact ⟨unsigned_usable (by simp [Items]), unsigned_impossible P⟩
  | pk_k key => exact key_unsigned empty (by simp [Items])
  | pk_h key =>
    exact key_unsigned empty
      (by intro item h; exact List.mem_singleton.mp h ▸ km key (by simp [CoreFragment.keys]))
  | older n =>
    constructor
    · simp only [satisfactionCandidates]; split
      · exact unsigned_usable (by simp [Items])
      · exact unsigned_impossible P
    · exact unsigned_impossible P
  | after n =>
    constructor
    · simp only [satisfactionCandidates]; split
      · exact unsigned_usable (by simp [Items])
      · exact unsigned_impossible P
    · exact unsigned_impossible P
  | sha256 h | hash256 h | ripemd160 h | hash160 h =>
    exact hash_unsigned (pm _ (by simp [CoreFragment.hashLocks])) (np _ (by simp [CoreFragment.hashLocks]))
  | and_v X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨hx.1.combine hy.1, (hx.1.combine hy.2).markNonCanonical⟩
  | and_b X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨hx.1.combine hy.1, ((hx.2.combine hy.2).select
      (hx.2.combine hy.1).markOvercomplete).select (hx.1.combine hy.2).markOvercomplete⟩
  | or_b X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨((hx.1.combine hy.2).select (hx.2.combine hy.1)).select
      (hx.1.combine hy.1).markOvercomplete, hx.2.combine hy.2⟩
  | or_c X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨hx.1.select (hx.2.combine hy.1), unsigned_impossible P⟩
  | or_d X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨hx.1.select (hx.2.combine hy.1), hx.2.combine hy.2⟩
  | or_i X Y =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ h))
      (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨(hx.1.selector one).select (hy.1.selector empty), (hx.2.selector one).select (hy.2.selector empty)⟩
  | andor X Y Z =>
    have hx := all_unsigned_items X empty one
      (fun key h => km key (List.mem_append_left _ (List.mem_append_left _ h)))
      (fun lock h => pm lock (List.mem_append_left _ (List.mem_append_left _ h)))
      (fun lock h => np lock (List.mem_append_left _ (List.mem_append_left _ h)))
    have hy := all_unsigned_items Y empty one
      (fun key h => km key (List.mem_append_left _ (List.mem_append_right _ h)))
      (fun lock h => pm lock (List.mem_append_left _ (List.mem_append_right _ h)))
      (fun lock h => np lock (List.mem_append_left _ (List.mem_append_right _ h)))
    have hz := all_unsigned_items Z empty one
      (fun key h => km key (List.mem_append_right _ h))
      (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h))
    exact ⟨(hx.1.combine hy.1).select (hx.2.combine hz.1),
      (hx.2.combine hz.2).select (hx.1.combine hy.2).markNonCanonical⟩
  | a X | s X | c X | n X => exact all_unsigned_items X empty one km pm np
  | v X => exact ⟨(all_unsigned_items X empty one km pm np).1, unsigned_impossible P⟩
  | d X => exact ⟨(all_unsigned_items X empty one km pm np).1.selector one,
      unsigned_usable (by intro _ item h; exact List.mem_singleton.mp h ▸ empty)⟩
  | j X =>
    have hx := all_unsigned_items X empty one km pm np
    exact ⟨hx.1, (unsigned_usable
      (by intro _ item h; exact List.mem_singleton.mp h ▸ empty)).select
      hx.2.requireNonemptyRuntimeTop.markNonCanonical⟩
  | multi k keys => exact legacy_unsigned empty
  | multi_a k keys => exact multi_a_unsigned empty
  | thresh k children =>
    have hc := list_unsigned_items children empty one km pm np
    simp only [satisfactionCandidates]
    split
    · exact ⟨threshold_sat_unsigned hc k, threshold_dsat_unsigned (countCandidates_unsigned hc) k⟩
    · exact ⟨unsigned_impossible P, unsigned_impossible P⟩

theorem list_unsigned_items (children : List CoreFragment) {env : SatEnv} {P : StackElement → Prop}
    (empty : P falseElement) (one : P trueElement)
    (km : ∀ key ∈ CoreFragment.keysList children, P key.bytes)
    (pm : ∀ lock ∈ CoreFragment.hashLocksList children, ∀ p, env.preimageFor lock = some p → P p)
    (np : ∀ lock ∈ CoreFragment.hashLocksList children, P (env.nonPreimageFor lock)) :
    ∀ child ∈ satisfactionCandidatesList children env, UnsignedPairItems P child := by
  cases children with
  | nil => simp
  | cons head tail =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact all_unsigned_items head empty one
        (fun key h => km key (List.mem_append_left _ h))
        (fun lock h => pm lock (List.mem_append_left _ h)) (fun lock h => np lock (List.mem_append_left _ h))
    · exact list_unsigned_items tail empty one
        (fun key h => km key (List.mem_append_right _ h))
        (fun lock h => pm lock (List.mem_append_right _ h)) (fun lock h => np lock (List.mem_append_right _ h)) child member
end

/-- In a sound Tapscript environment the largest unsigned witness items are the
    32-byte public keys, preimages and nonpreimages. This also covers raw rows. -/
theorem unsigned_candidate_items_small (fragment : CoreFragment) {env : SatEnv}
    (sound : env.Sound) (keySizes : ∀ key ∈ fragment.keys, key.bytes.size = 32) :
    UnsignedPairItems (fun item => item.size ≤ 32) (satisfactionCandidates fragment env) :=
  all_unsigned_items fragment (by decide) (by decide)
    (fun key h => Nat.le_of_eq (keySizes key h))
    (fun _ _ _ selected => Nat.le_of_eq (sound.preimageMatches selected).1)
    (fun lock _ => Nat.le_of_eq (sound.nonPreimageMismatches lock).1)

/-- A usable dissatisfaction of an expressive, non-malleable fragment cannot
    disclose bytes that satisfy a signature check for any 32-byte key. -/
theorem expressive_dsat_excludes_signature {fragment : CoreFragment} {ty : MiniType}
    {mm : MalleabilityModifiers} {env : SatEnv} {flags : ScriptFlags} {frame : Witness}
    (typed : HasType .tapscript fragment ty) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (sound : env.Sound) (version : env.txCtx.sigVersion = .tapscript)
    (dsat : dissatisfy fragment env = some frame) {sig : StackElement} {key : PubKey}
    (keySize : key.bytes.size = 32)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    sig ∉ frame := by
  obtain ⟨candidate, eq, unsigned, _⟩ := (malleabilityCandidateSound env wf typed mal).expressiveDsat nm e
  have small := (unsigned_candidate_items_small fragment sound (wellFormed_keySizes fragment wf)).2 candidate eq unsigned
  change (satisfactionCandidates fragment env).dsat.usableWitness? = some frame at dsat
  rw [eq] at dsat
  cases status : candidate.status <;> simp [CandidateResult.usableWitness?, status] at dsat
  subst frame
  intro member
  have := small sig member
  have := successful_slot_size version keySize checked
  omega

end LeanMiniscript.Extraction.TapscriptWitness
