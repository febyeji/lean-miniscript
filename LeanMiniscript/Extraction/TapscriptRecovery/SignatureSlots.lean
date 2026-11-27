import LeanMiniscript.Extraction.TapscriptRecovery.FalseExecution

/-! Recover checked witness slots using the path to the root and its signature selection. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.CheckedRows

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Active OrI BWrappers ThresholdRun
  OriginCounts

theorem context_signature_selected {parent child : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {pa po own : Witness} {sig : StackElement} {key : PubKey}
    (context : ExecutionContext parent child env flags pa po own)
    (member : sig ∈ own) (keyMem : key ∈ child.keys)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    env.signatureFor key = some sig :=
  disclosed_signature_selected context.sound context.version context.keySizes context.canonical
    context.thirdParty (context.consumedIn sig member) (context.childKeys key keyMem) checked

theorem checkedTrue_c_pk_k (key : PubKey) (parent : CoreFragment) (env : SatEnv)
    (flags : ScriptFlags) (pa po : Witness) :
    CheckedTrueRowAgreementB (.c (.pk_k key)) parent env flags pa po := by
  intro own expected top rest context _nodup canonical _bounded run truth _checked
  obtain ⟨sig, eq, checked⟩ := accepts_c_pk_k_inversion run truth
  have ownEq : own = [sig] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right eq)
  have selected := context_signature_selected context (by simp [ownEq])
    (by simp [CoreFragment.keys]) checked
  obtain ⟨sig0, selected0, expectedEq⟩ := satisfy_c_pk_k canonical
  have equal : sig = sig0 := Option.some.inj (selected.symm.trans selected0)
  rw [ownEq, expectedEq, equal]

theorem checkedTrue_c_pk_h (key : PubKey) (parent : CoreFragment) (env : SatEnv)
    (flags : ScriptFlags) (pa po : Witness) :
    CheckedTrueRowAgreementB (.c (.pk_h key)) parent env flags pa po := by
  intro own expected top rest context _nodup canonical _bounded run truth _checked
  obtain ⟨sig, pubkey, eq, imageEq, checked⟩ := accepts_c_pk_h_inversion run truth
  have ownEq : own = [sig, pubkey] := witness_eq_pair_of_toInitialStack (List.append_cancel_right eq)
  have pubkeyEq : pubkey = key.bytes := context.thirdParty.2.2.2 pubkey
    (context.consumedIn pubkey (by simp [ownEq]))
    key (context.childKeys key (by simp [CoreFragment.keys])) imageEq
  rw [pubkeyEq] at checked
  have selected := context_signature_selected context (by simp [ownEq])
    (by simp [CoreFragment.keys]) checked
  obtain ⟨sig0, selected0, expectedEq⟩ := satisfy_c_pk_h canonical
  have equal : sig = sig0 := Option.some.inj (selected.symm.trans selected0)
  rw [ownEq, expectedEq, equal, pubkeyEq]

theorem thirdParty_of_local_material {parent child : CoreFragment} {env : SatEnv}
    {flags : ScriptFlags} {pa po own expected : Witness}
    (context : ExecutionContext parent child env flags pa po own)
    (signatures : ∀ item ∈ own, ∀ key ∈ child.keys,
      verifySigFor checkSig checkSchnorrSig env.txCtx item key.bytes = true → item ∈ expected)
    (preimages : ∀ item ∈ own, ∀ lock ∈ child.hashLocks, lock.Matches item → item ∈ expected) :
    ThirdPartyWitness child env.txCtx expected own := by
  refine ⟨?_, signatures, preimages, ?_⟩
  · intro item member first hf second hs different valid
    exact context.thirdParty.1 item (context.consumedIn item member)
      first (context.childKeys first hf) second (context.childKeys second hs) different valid
  · intro item member key hk imageEq
    exact context.thirdParty.2.2.2 item (context.consumedIn item member)
      key (context.childKeys key hk) imageEq

theorem agreement_multi_a_of_signature_membership {k : Nat} {keys : List PubKey}
    {parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags} {pa po own expected : Witness}
    {top : StackElement} {rest : Stack}
    (wf : (CoreFragment.multi_a k keys).WellFormed .tapscript)
    (context : ExecutionContext parent (.multi_a k keys) env flags pa po own)
    (nodup : keys.Nodup) (canonical : satisfy (.multi_a k keys) env = some expected)
    (signatures : ∀ item ∈ own, ∀ key ∈ keys,
      verifySigFor checkSig checkSchnorrSig env.txCtx item key.bytes = true → item ∈ expected)
    (_bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.multi_a k keys)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) : own = expected := by
  exact unique_multi_a_frame context.sound nodup wf.2.1 wf.2.2.1 context.version run truth canonical
    (thirdParty_of_local_material context signatures (by simp [CoreFragment.hashLocks]))

theorem checkedTrue_j {child parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} (smaller : CheckedTrueRowAgreementB child parent env flags pa po) :
    CheckedTrueRowAgreementB (.j child) parent env flags pa po := by
  intro own expected top rest context nodup canonical bounded run truth checked
  exact smaller own expected top rest
    (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup (by simpa using canonical) bounded (j_success_child bounded run truth) truth checked

theorem checkedTrue_n {child parent : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po : Witness} (smaller : CheckedTrueRowAgreementB child parent env flags pa po) :
    CheckedTrueRowAgreementB (.n child) parent env flags pa po := by
  intro own expected top rest context nodup canonical bounded run truth checked
  obtain ⟨value, childRun, childTruth⟩ := n_success_child run truth
  exact smaller own expected value rest
    (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup (by simpa using canonical) bounded childRun childTruth checked

end LeanMiniscript.Extraction.TapscriptRecovery.CheckedRows

namespace LeanMiniscript.Extraction.TapscriptRecovery.SlotLocal

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport OrI ThresholdRows ThresholdCanonical
  CheckedRows OriginCounts

export _root_.LeanMiniscript.Extraction.TapscriptWitness (LocalSlot)

theorem localSlot_short {target : CoreFragment} {env : SatEnv} {own expected : Witness}
    {item : StackElement} (short : item.size < 64) : LocalSlot target env own expected item := by
  intro _ _ _ _ size
  omega

theorem foreign_pair {root target other : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} (context : ExecutionContext root target env flags pa po own)
    (keysIn : ∀ key ∈ other.keys, key ∈ root.keys)
    (distinct : ∀ key ∈ target.keys, ∀ otherKey ∈ other.keys, key ≠ otherKey) :
    PairItems (LocalSlot target env own expected) (satisfactionCandidates other env) := by
  apply all_items other
  · exact localSlot_short (by decide)
  · exact localSlot_short (by decide)
  · intro key member
    exact localSlot_short (by rw [context.keySizes key (keysIn key member)]; decide)
  · intro otherKey otherMem sig selected actual key keyMem valid _size
    exact (context.thirdParty.1 sig (context.consumedIn sig actual)
      key (context.childKeys key keyMem) otherKey (keysIn otherKey otherMem)
      (distinct key keyMem otherKey otherMem) valid (context.sound.signatureValid selected)).elim
  · intro lock _member preimage selected
    exact localSlot_short (by rw [(context.sound.preimageMatches selected).1]; decide)

theorem multi_a_pair {k : Nat} {keys : List PubKey} {env : SatEnv} {own expected : Witness}
    (canonical : satisfy (.multi_a k keys) env = some expected) :
    PairItems (LocalSlot (.multi_a k keys) env own expected)
      (satisfactionCandidates (.multi_a k keys) env) := by
  constructor
  · intro witness projection item member _actual _key _keyMem _valid _size
    have equal : witness = expected := Option.some.inj (projection.symm.trans canonical)
    simpa [equal] using member
  · intro witness projection
    change (multiACandidates k keys env).dsat.usableWitness? = some witness at projection
    unfold multiACandidates at projection
    split at projection
    · have equal : witness = List.replicate keys.length falseElement := by
        simpa [CandidateResult.usable, CandidateResult.usableWitness?] using projection.symm
      intro item member
      have itemEq : item = falseElement := (List.mem_replicate.mp (equal ▸ member)).2
      subst item
      exact localSlot_short (by decide)
    · simp [CandidateResult.usableWitness?] at projection

export _root_.LeanMiniscript.Extraction.TapscriptWitness (Wrapper)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (wrap)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (Binary)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (join)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (wrap_keys)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (join_keys)

theorem pair_wrap {P : StackElement → Prop} {env : SatEnv} {x : CoreFragment}
    (empty : P falseElement) (one : P trueElement)
    (hx : PairItems P (satisfactionCandidates x env)) (op : Wrapper) :
    PairItems P (satisfactionCandidates (wrap op x) env) := by
  cases op with
  | a | s | c | n => exact hx
  | v => exact ⟨hx.1, CandidateResult.supports_impossible _⟩
  | d => exact ⟨supports_items_selector hx.1 one,
      CandidateResult.supports_usable (by intro item member; exact List.mem_singleton.mp member ▸ empty)⟩
  | j => exact ⟨hx.1, (CandidateResult.supports_usable
      (by intro item member; exact List.mem_singleton.mp member ▸ empty)).select
      (hx.2.requireNonemptyRuntimeTop.mono (fun _ h => h.1)).markNonCanonical⟩

theorem pair_join {P : StackElement → Prop} {env : SatEnv} {x y : CoreFragment}
    (empty : P falseElement) (one : P trueElement)
    (hx : PairItems P (satisfactionCandidates x env))
    (hy : PairItems P (satisfactionCandidates y env)) (op : Binary) :
    PairItems P (satisfactionCandidates (join op x y) env) := by
  cases op with
  | and_v => exact ⟨supports_items_combine hx.1 hy.1, (supports_items_combine hx.1 hy.2).markNonCanonical⟩
  | and_b => exact ⟨supports_items_combine hx.1 hy.1,
      ((supports_items_combine hx.2 hy.2).select (CandidateResult.supports_markOvercomplete _ _)).select
      (CandidateResult.supports_markOvercomplete _ _)⟩
  | or_b => exact ⟨((supports_items_combine hx.1 hy.2).select
      (supports_items_combine hx.2 hy.1)).select (CandidateResult.supports_markOvercomplete _ _),
      supports_items_combine hx.2 hy.2⟩
  | or_c => exact ⟨hx.1.select (supports_items_combine hx.2 hy.1), CandidateResult.supports_impossible _⟩
  | or_d => exact ⟨hx.1.select (supports_items_combine hx.2 hy.1), supports_items_combine hx.2 hy.2⟩
  | or_i => exact ⟨(supports_items_selector hx.1 one).select (supports_items_selector hy.1 empty),
      (supports_items_selector hx.2 one).select (supports_items_selector hy.2 empty)⟩

theorem pair_andor {P : StackElement → Prop} {env : SatEnv} {x y z : CoreFragment}
    (hx : PairItems P (satisfactionCandidates x env))
    (hy : PairItems P (satisfactionCandidates y env))
    (hz : PairItems P (satisfactionCandidates z env)) :
    PairItems P (satisfactionCandidates (.andor x y z) env) :=
  ⟨(supports_items_combine hx.1 hy.1).select (supports_items_combine hx.2 hz.1),
    (supports_items_combine hx.2 hz.2).select (supports_items_combine hx.1 hy.2).markNonCanonical⟩

export _root_.LeanMiniscript.Extraction.TapscriptWitness (keysList_append)

theorem pair_thresh {P : StackElement → Prop} {env : SatEnv} {k : Nat} {children : List CoreFragment}
    (supported : ∀ child ∈ satisfactionCandidatesList children env, PairItems P child) :
    PairItems P (satisfactionCandidates (.thresh k children) env) := by
  simp only [satisfactionCandidates]
  split
  · exact ⟨(fun _ sel => let ⟨_, trace⟩ := CandidatePair.thresholdSatisfaction_choiceTrace sel; TapscriptWitness.trace_items trace supported), threshold_dsat_items supported k⟩
  · exact ⟨CandidateResult.supports_impossible _, CandidateResult.supports_impossible _⟩

abbrev SlotPath := _root_.LeanMiniscript.Extraction.TapscriptWitness.FragmentPath

theorem SlotPath.keys {target parent : CoreFragment} (path : SlotPath target parent) :
    ∀ key ∈ target.keys, key ∈ parent.keys := by
  exact TapscriptWitness.FragmentPath.keys path

theorem SlotPath.wellFormed {target parent : CoreFragment} (path : SlotPath target parent) :
    parent.WellFormed .tapscript → target.WellFormed .tapscript := by
  induction path with
  | here => exact id
  | wrapper op _ ih => cases op <;> exact ih
  | left op _ ih => cases op <;> exact fun wf => ih wf.1
  | right op _ ih =>
    cases op with
    | and_v | and_b => exact fun wf => ih wf.2.1
    | or_b | or_c | or_d | or_i => exact fun wf => ih wf.2
  | condition _ ih => exact fun wf => ih wf.1
  | thenBranch _ ih => exact fun wf => ih wf.2.1
  | elseBranch _ ih => exact fun wf => ih wf.2.2.1
  | threshold k before after _ ih =>
    intro wf
    exact ih (allWF_member wf.2.1 (List.mem_append_right _ (by simp)))

theorem SlotPath.noDup {target parent : CoreFragment} (path : SlotPath target parent) :
    parent.keys.Nodup → target.keys.Nodup := by
  exact TapscriptWitness.FragmentPath.noDup path

theorem path_pair {target parent root : CoreFragment} {env : SatEnv} {flags : ScriptFlags}
    {pa po own expected : Witness} (path : SlotPath target parent)
    (context : ExecutionContext root target env flags pa po own)
    (base : PairItems (LocalSlot target env own expected) (satisfactionCandidates target env)) :
    (∀ key ∈ parent.keys, key ∈ root.keys) → parent.keys.Nodup →
    PairItems (LocalSlot target env own expected) (satisfactionCandidates parent env) := by
  have empty : LocalSlot target env own expected falseElement := localSlot_short (by decide)
  have one : LocalSlot target env own expected trueElement := localSlot_short (by decide)
  induction path with
  | here => intro _ _; exact base
  | wrapper op _ ih =>
    intro keysIn nodup
    exact pair_wrap empty one (ih (by simpa using keysIn) (by simpa using nodup)) op
  | @left x y op path ih =>
    intro keysIn nodup
    rw [join_keys] at keysIn nodup
    obtain ⟨nx, ny, separate⟩ := List.pairwise_append.mp nodup
    exact pair_join empty one (ih (fun key hk => keysIn key (List.mem_append_left _ hk)) nx)
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => separate key (path.keys key hk) other ho)) op
  | @right x y op path ih =>
    intro keysIn nodup
    rw [join_keys] at keysIn nodup
    obtain ⟨nx, ny, separate⟩ := List.pairwise_append.mp nodup
    exact pair_join empty one
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ hk))
        (fun key hk other ho => Ne.symm (separate other ho key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_right _ hk)) ny) op
  | @condition x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, ny, sx⟩ := List.pairwise_append.mp nxy
    exact pair_andor
      (ih (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk))) nx)
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun key hk other ho => sx key (path.keys key hk) other ho))
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => sxy key (List.mem_append_left _ (path.keys key hk)) other ho))
  | @thenBranch x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, ny, sx⟩ := List.pairwise_append.mp nxy
    exact pair_andor
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun key hk other ho => Ne.symm (sx other ho key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk))) ny)
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_right _ hk))
        (fun key hk other ho => sxy key (List.mem_append_right _ (path.keys key hk)) other ho))
  | @elseBranch x y z path ih =>
    intro keysIn nodup
    obtain ⟨nxy, nz, sxy⟩ := List.pairwise_append.mp nodup
    exact pair_andor
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_left _ hk)))
        (fun key hk other ho => Ne.symm (sxy other (List.mem_append_left _ ho) key (path.keys key hk))))
      (foreign_pair context (fun key hk => keysIn key (List.mem_append_left _ (List.mem_append_right _ hk)))
        (fun key hk other ho => Ne.symm (sxy other (List.mem_append_right _ ho) key (path.keys key hk))))
      (ih (fun key hk => keysIn key (List.mem_append_right _ hk)) nz)
  | @threshold x k before after path ih =>
    intro keysIn nodup
    simp only [CoreFragment.keys, keysList_append, CoreFragment.keysList] at keysIn nodup
    obtain ⟨nb, nxa, separateBefore⟩ := List.pairwise_append.mp nodup
    obtain ⟨nx, na, separateAfter⟩ := List.pairwise_append.mp nxa
    apply pair_thresh
    intro row member
    rw [satisfactionCandidatesList_eq_map] at member
    obtain ⟨fragment, fragmentMem, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp fragmentMem with beforeMem | tailMem
    · apply foreign_pair context
      · intro key hk
        exact keysIn key (List.mem_append_left _ (threshold_keys_member beforeMem key hk))
      · intro key hk other ho
        exact Ne.symm (separateBefore other (threshold_keys_member beforeMem other ho)
          key (List.mem_append_left _ (path.keys key hk)))
    · rcases List.mem_cons.mp tailMem with rfl | afterMem
      · exact ih (fun key hk => keysIn key (List.mem_append_right _ (List.mem_append_left _ hk))) nx
      · apply foreign_pair context
        · intro key hk
          exact keysIn key (List.mem_append_right _ (List.mem_append_right _ (threshold_keys_member afterMem key hk)))
        · intro key hk other ho
          exact separateAfter key (path.keys key hk) other (threshold_keys_member afterMem other ho)

theorem multi_a_signature_membership {k : Nat} {keys : List PubKey} {parent : CoreFragment}
    {env : SatEnv} {flags : ScriptFlags} {pa po own expected : Witness} {top : StackElement} {rest : Stack}
    (path : SlotPath (.multi_a k keys) parent) (wf : parent.WellFormed .tapscript)
    (context : ExecutionContext parent (.multi_a k keys) env flags pa po own)
    (nodup : parent.keys.Nodup) (canonical : satisfy (.multi_a k keys) env = some expected)
    (run : Eval (compile (.multi_a k keys)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) :
    ∀ item ∈ own, ∀ key ∈ keys,
      verifySigFor checkSig checkSchnorrSig env.txCtx item key.bytes = true → item ∈ expected := by
  have childWF := path.wellFormed wf
  have supported := path_pair path context (multi_a_pair canonical) (fun _ h => h) nodup
  have items := signatureFrameB_multi_a k keys childWF.2.1 childWF.2.2.1 env flags own top rest
    context.version (fun key hk => context.keySizes key (context.childKeys key hk)) run truth
  intro item member key keyMem valid
  rcases items item member with equal | size
  · subst item
    rw [context.sound.emptySignatureInvalid key] at valid
    cases valid
  · have inParent := context.thirdParty.2.1 item (context.consumedIn item member)
      key (context.childKeys key keyMem) valid
    exact supported.1 pa context.canonical item inParent member key keyMem valid size

theorem multi_a_agreement_from_path {k : Nat} {keys : List PubKey} {parent : CoreFragment}
    {env : SatEnv} {flags : ScriptFlags} {pa po own expected : Witness} {top : StackElement} {rest : Stack}
    (path : SlotPath (.multi_a k keys) parent) (wf : parent.WellFormed .tapscript)
    (context : ExecutionContext parent (.multi_a k keys) env flags pa po own)
    (nodup : parent.keys.Nodup) (canonical : satisfy (.multi_a k keys) env = some expected)
    (bounded : ∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.multi_a k keys)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) : own = expected :=
  agreement_multi_a_of_signature_membership (path.wellFormed wf) context (path.noDup nodup) canonical
    (multi_a_signature_membership path wf context nodup canonical run truth) bounded run truth

theorem checkedTrue_multi_a_from_path {k : Nat} {keys : List PubKey} {parent : CoreFragment}
    (env : SatEnv) (flags : ScriptFlags) (pa po : Witness)
    (path : SlotPath (.multi_a k keys) parent) (wf : parent.WellFormed .tapscript)
    (nodup : parent.keys.Nodup) :
    CheckedTrueRowAgreementB (.multi_a k keys) parent env flags pa po := by
  intro own expected top rest context _childNoDup canonical bounded run truth _checked
  exact multi_a_agreement_from_path path wf context nodup canonical bounded run truth

theorem SlotPath.of_threshold_member {target child : CoreFragment} {children : List CoreFragment}
    (k : Nat) (member : child ∈ children) (path : SlotPath target child) :
    SlotPath target (.thresh k children) := by
  exact TapscriptWitness.FragmentPath.of_threshold_member k member path

end LeanMiniscript.Extraction.TapscriptRecovery.SlotLocal
