import LeanMiniscript.Extraction.TapscriptWitnessProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Multisig

/-! Provenance of usable candidate items and recovery of checked signatures. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

def Items (P : StackElement → Prop) (witness : Witness) : Prop :=
  ∀ item ∈ witness, P item

def PairItems (P : StackElement → Prop) (pair : CandidatePair) : Prop :=
  pair.sat.Supports (Items P) ∧ pair.dsat.Supports (Items P)

theorem items_combine {P : StackElement → Prop} {a b : Witness}
    (ha : Items P a) (hb : Items P b) : Items P (Witness.combine a b) := by
  intro item member
  rcases List.mem_append.mp member with member | member
  · exact hb item member
  · exact ha item member

theorem supports_items_combine {P : StackElement → Prop} {a b : CandidateResult}
    (ha : a.Supports (Items P)) (hb : b.Supports (Items P)) :
    (a.combine b).Supports (Items P) := by
  intro witness selected
  obtain ⟨wa, wb, sa, sb, rfl⟩ := CandidateResult.combine_usableWitness_iff.mp selected
  exact items_combine (ha wa sa) (hb wb sb)

theorem supports_items_selector {P : StackElement → Prop} {a : CandidateResult}
    {selector : StackElement} (ha : a.Supports (Items P)) (hs : P selector) :
    (a.withSelector selector).Supports (Items P) := by
  intro witness selected
  obtain ⟨inner, si, rfl⟩ := CandidateResult.withSelector_usableWitness_iff.mp selected
  intro item member
  rcases List.mem_append.mp member with member | member
  · exact ha inner si item member
  · exact List.mem_singleton.mp member ▸ hs

theorem trace_items {P : StackElement → Prop} {children : List CandidatePair}
    {count : Nat} {frames : List Witness} {witness : Witness}
    (trace : CandidatePair.ChoiceTrace children count frames witness)
    (supported : ∀ child ∈ children, PairItems P child) : Items P witness := by
  induction trace with
  | nil => simp [Items]
  | @sat children count frames witness child childWitness trace selected ih =>
      exact items_combine (ih (fun c hc => supported c (List.mem_append_left _ hc)))
        ((supported child (List.mem_append_right _ (by simp))).1 _ selected)
  | @dsat children count frames witness child childWitness trace selected ih =>
      exact items_combine (ih (fun c hc => supported c (List.mem_append_left _ hc)))
        ((supported child (List.mem_append_right _ (by simp))).2 _ selected)

theorem exact_items {P : StackElement → Prop} {children : List CandidatePair}
    (supported : ∀ child ∈ children, PairItems P child) (count : Nat) :
    (CandidatePair.selectExactly count children).Supports (Items P) := by
  intro witness selected
  obtain ⟨frames, trace⟩ := CandidatePair.selectExactly_choiceTrace selected
  exact trace_items trace supported

theorem threshold_dsat_items {P : StackElement → Prop} {children : List CandidatePair}
    (supported : ∀ child ∈ children, PairItems P child) (count : Nat) :
    (CandidatePair.thresholdDissatisfaction count
      (CandidatePair.countCandidates children)).Supports (Items P) := by
  intro witness selected
  obtain ⟨frames, trace⟩ := CandidatePair.thresholdDissatisfaction_choiceTrace selected
  exact trace_items trace supported

theorem key_items {P : StackElement → Prop} {env : SatEnv} {key : PubKey}
    {tail : Witness} (empty : P falseElement) (ht : Items P tail)
    (hs : ∀ sig, env.signatureFor key = some sig → P sig) :
    PairItems P (keyCandidates key tail env) := by
  constructor
  · cases selected : env.signatureFor key with
    | none => simpa [keyCandidates, selected] using CandidateResult.supports_impossible (Items P)
    | some sig =>
        simpa [keyCandidates, selected] using
          (CandidateResult.supports_usable (hasSig := true)
            (show Items P (sig :: tail) from by
              intro item member
              rcases List.mem_cons.mp member with rfl | member
              · exact hs _ selected
              · exact ht item member))
  · apply CandidateResult.supports_usable
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact empty
    · exact ht item member

theorem hash_items {P : StackElement → Prop} {env : SatEnv} {lock : HashLock}
    (hp : ∀ preimage, env.preimageFor lock = some preimage → P preimage) :
    PairItems P (hashCandidates lock env) := by
  constructor
  · cases selected : env.preimageFor lock with
    | none => simpa [hashCandidates, selected] using CandidateResult.supports_impossible (Items P)
    | some preimage =>
        simpa [hashCandidates, selected] using
          (CandidateResult.supports_usable (hasSig := false)
            (show Items P [preimage] from by
              intro item member
              exact List.mem_singleton.mp member ▸ hp preimage selected))
  · intro witness selected
    simp [hashCandidates, CandidateResult.dontUse, CandidateResult.usableWitness?] at selected

theorem multi_a_items {P : StackElement → Prop} {env : SatEnv}
    {k : Nat} {keys : List PubKey} (empty : P falseElement)
    (hs : ∀ key ∈ keys, ∀ sig, env.signatureFor key = some sig → P sig) :
    PairItems P (multiACandidates k keys env) := by
  unfold multiACandidates
  split
  · constructor
    · apply exact_items
      intro child member
      obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp member
      exact key_items empty (by simp [Items]) (hs key keyMem)
    · apply CandidateResult.supports_usable
      intro item member
      have equal := (List.mem_replicate.mp member).2
      exact equal ▸ empty
  · exact ⟨CandidateResult.supports_impossible _, CandidateResult.supports_impossible _⟩

theorem legacy_items {P : StackElement → Prop} {env : SatEnv}
    {k : Nat} {keys : List PubKey} (empty : P falseElement)
    (hs : ∀ key ∈ keys, ∀ sig, env.signatureFor key = some sig → P sig) :
    PairItems P (legacyMultiCandidates k keys env) := by
  unfold legacyMultiCandidates
  split
  · exact ⟨CandidateResult.supports_impossible _, CandidateResult.supports_impossible _⟩
  · constructor
    · intro witness selected
      obtain ⟨inner, si, rfl⟩ := CandidateResult.finalizeLegacyMulti_usableWitness_iff.mp selected
      have supported : Items P inner := by
        refine exact_items (P := P) ?_ k inner si
        intro child member
        obtain ⟨key, keyMem, rfl⟩ := List.mem_map.mp member
        constructor
        · cases choice : env.signatureFor key with
          | none => simpa [legacyMultiKeyChoice, choice] using CandidateResult.supports_impossible (Items P)
          | some sig =>
              simpa [legacyMultiKeyChoice, choice] using
                (CandidateResult.supports_usable (hasSig := true)
                  (show Items P [sig] from by
                    intro item member
                    exact List.mem_singleton.mp member ▸ hs key keyMem sig choice))
        · exact CandidateResult.supports_usable (by simp [Items])
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact empty
      · exact supported item (List.mem_reverse.mp member)
    · apply CandidateResult.supports_usable
      intro item member
      exact (List.mem_replicate.mp member).2 ▸ empty


mutual
/-- Every usable candidate is built from its fragment's keys, selected
signatures, selected preimages and fixed selectors. This does not need sanity. -/
theorem all_items (fragment : CoreFragment) {env : SatEnv} {P : StackElement → Prop}
    (empty : P falseElement) (one : P trueElement)
    (km : ∀ key ∈ fragment.keys, P key.bytes)
    (sm : ∀ key ∈ fragment.keys, ∀ sig, env.signatureFor key = some sig → P sig)
    (pm : ∀ lock ∈ fragment.hashLocks, ∀ p, env.preimageFor lock = some p → P p) :
    PairItems P (satisfactionCandidates fragment env) := by
  cases fragment with
  | zero => exact ⟨CandidateResult.supports_impossible _,
      CandidateResult.supports_usable (by simp [Items])⟩
  | one => exact ⟨CandidateResult.supports_usable (by simp [Items]),
      CandidateResult.supports_impossible _⟩
  | pk_k key => exact key_items empty (by simp [Items]) (sm key (by simp [CoreFragment.keys]))
  | pk_h key =>
      exact key_items empty
        (by intro item hi; exact List.mem_singleton.mp hi ▸ km key (by simp [CoreFragment.keys]))
        (sm key (by simp [CoreFragment.keys]))
  | older n =>
      constructor
      · simp only [satisfactionCandidates]
        split
        · exact CandidateResult.supports_usable (by simp [Items])
        · exact CandidateResult.supports_impossible _
      · exact CandidateResult.supports_impossible _
  | after n =>
      constructor
      · simp only [satisfactionCandidates]
        split
        · exact CandidateResult.supports_usable (by simp [Items])
        · exact CandidateResult.supports_impossible _
      · exact CandidateResult.supports_impossible _
  | sha256 h => exact hash_items (pm _ (by simp [CoreFragment.hashLocks]))
  | hash256 h => exact hash_items (pm _ (by simp [CoreFragment.hashLocks]))
  | ripemd160 h => exact hash_items (pm _ (by simp [CoreFragment.hashLocks]))
  | hash160 h => exact hash_items (pm _ (by simp [CoreFragment.hashLocks]))
  | and_v X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨supports_items_combine hX.1 hY.1,
        (supports_items_combine hX.1 hY.2).markNonCanonical⟩
  | and_b X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨supports_items_combine hX.1 hY.1,
        ((supports_items_combine hX.2 hY.2).select
          (CandidateResult.supports_markOvercomplete _ _)).select
          (CandidateResult.supports_markOvercomplete _ _)⟩
  | or_b X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨((supports_items_combine hX.1 hY.2).select
        (supports_items_combine hX.2 hY.1)).select
        (CandidateResult.supports_markOvercomplete _ _),
        supports_items_combine hX.2 hY.2⟩
  | or_c X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨hX.1.select (supports_items_combine hX.2 hY.1),
        CandidateResult.supports_impossible _⟩
  | or_d X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨hX.1.select (supports_items_combine hX.2 hY.1),
        supports_items_combine hX.2 hY.2⟩
  | or_i X Y =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ hk))
        (fun key hk => sm key (List.mem_append_left _ hk))
        (fun lock hl => pm lock (List.mem_append_left _ hl))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨(supports_items_selector hX.1 one).select
        (supports_items_selector hY.1 empty),
        (supports_items_selector hX.2 one).select (supports_items_selector hY.2 empty)⟩
  | andor X Y Z =>
      have hX := all_items X empty one
        (fun key hk => km key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun key hk => sm key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun lock hl => pm lock (List.mem_append_left _ (List.mem_append_left _ hl)))
      have hY := all_items Y empty one
        (fun key hk => km key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun key hk => sm key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun lock hl => pm lock (List.mem_append_left _ (List.mem_append_right _ hl)))
      have hZ := all_items Z empty one
        (fun key hk => km key (List.mem_append_right _ hk))
        (fun key hk => sm key (List.mem_append_right _ hk))
        (fun lock hl => pm lock (List.mem_append_right _ hl))
      exact ⟨(supports_items_combine hX.1 hY.1).select (supports_items_combine hX.2 hZ.1),
        (supports_items_combine hX.2 hZ.2).select
          (supports_items_combine hX.1 hY.2).markNonCanonical⟩
  | a X | s X | c X | n X => exact all_items X empty one km sm pm
  | v X => exact ⟨(all_items X empty one km sm pm).1,
      CandidateResult.supports_impossible _⟩
  | d X => exact ⟨supports_items_selector (all_items X empty one km sm pm).1 one,
      CandidateResult.supports_usable (by intro item hi; exact List.mem_singleton.mp hi ▸ empty)⟩
  | j X =>
      have hX := all_items X empty one km sm pm
      exact ⟨hX.1, (CandidateResult.supports_usable
        (by intro item hi; exact List.mem_singleton.mp hi ▸ empty)).select
        (hX.2.requireNonemptyRuntimeTop.mono (fun _ h => h.1)).markNonCanonical⟩
  | multi k keys => exact legacy_items empty sm
  | multi_a k keys => exact multi_a_items empty sm
  | thresh k fragments =>
      have children := list_items fragments empty one km sm pm
      simp only [satisfactionCandidates]
      split
      · refine ⟨?_, threshold_dsat_items children k⟩
        intro witness selected
        obtain ⟨frames, trace⟩ := CandidatePair.thresholdSatisfaction_choiceTrace selected
        exact trace_items trace children
      · exact ⟨CandidateResult.supports_impossible _, CandidateResult.supports_impossible _⟩

theorem list_items (fragments : List CoreFragment) {env : SatEnv} {P : StackElement → Prop}
    (empty : P falseElement) (one : P trueElement)
    (km : ∀ key ∈ CoreFragment.keysList fragments, P key.bytes)
    (sm : ∀ key ∈ CoreFragment.keysList fragments,
      ∀ sig, env.signatureFor key = some sig → P sig)
    (pm : ∀ lock ∈ CoreFragment.hashLocksList fragments,
      ∀ p, env.preimageFor lock = some p → P p) :
    ∀ child ∈ satisfactionCandidatesList fragments env, PairItems P child := by
  cases fragments with
  | nil => simp
  | cons X Xs =>
      intro child member
      simp only [satisfactionCandidatesList, List.mem_cons] at member
      rcases member with rfl | member
      · exact all_items X empty one
          (fun key hk => km key (List.mem_append_left _ hk))
          (fun key hk => sm key (List.mem_append_left _ hk))
          (fun lock hl => pm lock (List.mem_append_left _ hl))
      · exact list_items Xs empty one
          (fun key hk => km key (List.mem_append_right _ hk))
          (fun key hk => sm key (List.mem_append_right _ hk))
          (fun lock hl => pm lock (List.mem_append_right _ hl)) child member
end

/-- Classification of every item in a usable standard candidate. DONTUSE
nonpreimages do not appear in this classification. -/
def Material (fragment : CoreFragment) (env : SatEnv) (item : StackElement) : Prop :=
  item = falseElement ∨ item = trueElement ∨
  (∃ key ∈ fragment.keys, item = key.bytes) ∨
  (∃ key ∈ fragment.keys, env.signatureFor key = some item) ∨
  (∃ lock ∈ fragment.hashLocks, env.preimageFor lock = some item)

theorem candidates_material (fragment : CoreFragment) (env : SatEnv) :
    PairItems (Material fragment env) (satisfactionCandidates fragment env) := by
  apply all_items fragment
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · intro key hk
    exact Or.inr (Or.inr (Or.inl ⟨key, hk, rfl⟩))
  · intro key hk sig selected
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨key, hk, selected⟩)))
  · intro lock hl p selected
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lock, hl, selected⟩)))

theorem satisfy_material {fragment : CoreFragment} {env : SatEnv} {witness : Witness}
    (selected : satisfy fragment env = some witness) :
    Items (Material fragment env) witness :=
  (candidates_material fragment env).1 witness selected


/-- A 64/65-byte item in any usable standard candidate must be a selected
signature, assuming 32-byte keys and sound preimages. -/
theorem material_signature_of_size {fragment : CoreFragment} {env : SatEnv}
    {item : StackElement} (sound : env.Sound)
    (keySizes : ∀ key ∈ fragment.keys, key.bytes.size = 32)
    (material : Material fragment env item) (size : item.size = 64 ∨ item.size = 65) :
    ∃ key ∈ fragment.keys, env.signatureFor key = some item := by
  rcases material with rfl | rfl | ⟨key, hk, rfl⟩ | signature | ⟨lock, _, selected⟩
  · have zero : (falseElement : StackElement).size = 0 := rfl
    omega
  · have one : (trueElement : StackElement).size = 1 := rfl
    omega
  · have := keySizes key hk
    omega
  · exact signature
  · have := (sound.preimageMatches selected).1
    omega

theorem allKeysValid_size {keys : List PubKey}
    (valid : CoreFragment.allKeysValid .tapscript keys) :
    ∀ key ∈ keys, key.bytes.size = 32 := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
      intro item hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact valid.1
      · exact ih valid.2 item hi

mutual
/-- The key-size premise of the frame contracts is supplied by the existing
Tapscript well-formedness boundary. -/
theorem wellFormed_keySizes (fragment : CoreFragment)
    (wellFormed : fragment.WellFormed .tapscript) :
    ∀ key ∈ fragment.keys, key.bytes.size = 32 := by
  cases fragment with
  | zero | one | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _ =>
      simp [CoreFragment.keys]
  | pk_k key | pk_h key =>
      intro item hi
      have equal : item = key := List.mem_singleton.mp hi
      subst item
      exact wellFormed
  | and_v X Y | and_b X Y =>
      intro key hk
      rcases List.mem_append.mp hk with hx | hy
      · exact wellFormed_keySizes X wellFormed.1 key hx
      · exact wellFormed_keySizes Y wellFormed.2.1 key hy
  | or_b X Y | or_c X Y | or_d X Y | or_i X Y =>
      intro key hk
      rcases List.mem_append.mp hk with hx | hy
      · exact wellFormed_keySizes X wellFormed.1 key hx
      · exact wellFormed_keySizes Y wellFormed.2 key hy
  | andor X Y Z =>
      intro key hk
      rcases List.mem_append.mp hk with hxy | hz
      · rcases List.mem_append.mp hxy with hx | hy
        · exact wellFormed_keySizes X wellFormed.1 key hx
        · exact wellFormed_keySizes Y wellFormed.2.1 key hy
      · exact wellFormed_keySizes Z wellFormed.2.2.1 key hz
  | a X | s X | c X | d X | v X | j X | n X =>
      exact wellFormed_keySizes X wellFormed
  | thresh k fragments => exact wellFormed_list_keySizes fragments wellFormed.2.1
  | multi _ _ => exact False.elim wellFormed.1
  | multi_a _ _ => exact allKeysValid_size wellFormed.2.2.2

theorem wellFormed_list_keySizes (fragments : List CoreFragment)
    (wellFormed : CoreFragment.allWellFormed .tapscript fragments) :
    ∀ key ∈ CoreFragment.keysList fragments, key.bytes.size = 32 := by
  cases fragments with
  | nil => simp [CoreFragment.keysList]
  | cons X Xs =>
      intro key hk
      rcases List.mem_append.mp hk with hx | hxs
      · exact wellFormed_keySizes X wellFormed.1 key hx
      · exact wellFormed_list_keySizes Xs wellFormed.2 key hxs
end

theorem successful_slot_size {flags : ScriptFlags} {ctx : TxContext}
    {item : StackElement} {key : PubKey} (version : ctx.sigVersion = .tapscript)
    (keySize : key.bytes.size = 32)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx item key.bytes = .ok true) :
    item.size = 64 ∨ item.size = 65 := by
  have encoded : checkSigEncodingFor flags ctx.sigVersion item key.bytes = .ok () := by
    unfold checkSigWithEncoding at checked
    cases h : checkSigEncodingFor flags ctx.sigVersion item key.bytes with
    | error error => simp [h] at checked
    | ok value => cases value; rfl
  exact valid_sig_size keySize version encoded
    (verifySigFor_of_checkSigWithEncoding checked)

/-- A successful signature check on disclosed material identifies the exact
environment-selected signature for its actual key. -/
theorem disclosed_signature_selected {parent : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {arguments other : Witness} {sig : StackElement} {key : PubKey}
    (sound : env.Sound) (version : env.txCtx.sigVersion = .tapscript)
    (keySizes : ∀ k ∈ parent.keys, k.bytes.size = 32)
    (canonical : satisfy parent env = some arguments)
    (thirdParty : ThirdPartyWitness parent env.txCtx arguments other)
    (member : sig ∈ other) (keyMem : key ∈ parent.keys)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    env.signatureFor key = some sig := by
  have valid := verifySigFor_of_checkSigWithEncoding checked
  have inArgs := thirdParty.2.1 sig member key keyMem valid
  obtain ⟨selectedKey, selectedMem, selected⟩ := material_signature_of_size sound keySizes
    (satisfy_material canonical sig inArgs)
    (successful_slot_size version (keySizes key keyMem) checked)
  by_cases equal : selectedKey = key
  · simpa [equal] using selected
  · exact False.elim (thirdParty.1 sig member key keyMem selectedKey selectedMem
      (Ne.symm equal) valid (sound.signatureValid selected))

end LeanMiniscript.Extraction.TapscriptWitness
