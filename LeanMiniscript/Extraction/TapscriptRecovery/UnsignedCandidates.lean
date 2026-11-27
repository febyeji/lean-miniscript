import LeanMiniscript.Extraction.TapscriptRecovery.ThresholdExecution

/-! Recover the raw unsigned candidates of active branches and classify forced branches. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.DsatMaterial

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Transport OrI OrDC ThresholdRun

export _root_.LeanMiniscript.Extraction.TapscriptWitness (UnsignedItems)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (UnsignedPairItems)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (all_unsigned_items)

def UnsignedMaterial (fragment : CoreFragment) (env : SatEnv) (item : StackElement) : Prop :=
  item = falseElement ∨ item = trueElement ∨
  (∃ key ∈ fragment.keys, item = key.bytes) ∨
  (∃ lock ∈ fragment.hashLocks, env.preimageFor lock = some item) ∨
  (∃ lock ∈ fragment.hashLocks, item = env.nonPreimageFor lock)

theorem unsigned_candidates_material (fragment : CoreFragment) (env : SatEnv) :
    UnsignedPairItems (UnsignedMaterial fragment env) (satisfactionCandidates fragment env) := by
  apply all_unsigned_items fragment
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · intro key member
    exact Or.inr (Or.inr (Or.inl ⟨key, member, rfl⟩))
  · intro lock member item selected
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lock, member, selected⟩)))
  · intro lock member
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lock, member, rfl⟩)))

theorem unsigned_material_small {fragment : CoreFragment} {env : SatEnv} {item : StackElement}
    (sound : env.Sound) (keySizes : ∀ key ∈ fragment.keys, key.bytes.size = 32)
    (material : UnsignedMaterial fragment env item) : item.size ≤ 32 := by
  rcases material with rfl | rfl | ⟨key, hk, rfl⟩ | ⟨lock, _, selected⟩ | ⟨lock, _, rfl⟩
  · decide
  · decide
  · exact Nat.le_of_eq (keySizes key hk)
  · exact Nat.le_of_eq (sound.preimageMatches selected).1
  · exact Nat.le_of_eq (sound.nonPreimageMismatches lock).1

theorem UnsignedItems.usable {P : StackElement → Prop} {result : CandidateResult} {witness : Witness}
    (supported : UnsignedItems P result) (unsigned : RawUnsigned result)
    (selected : result.usableWitness? = some witness) : Items P witness := by
  obtain ⟨candidate, eq, flag⟩ := unsigned
  rw [eq] at selected
  have witnessEq : candidate.witness = witness := by
    cases status : candidate.status <;> simp [CandidateResult.usableWitness?, status] at selected
    exact selected
  rw [← witnessEq]
  exact supported candidate eq flag

theorem expressive_dsat_material {fragment : CoreFragment} {ty : MiniType}
    {mm : MalleabilityModifiers} {env : SatEnv} {arguments : Witness}
    (typed : HasType .tapscript fragment ty) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true) (expressive : mm.e = true)
    (canonical : dissatisfy fragment env = some arguments) : Items (UnsignedMaterial fragment env) arguments :=
  UnsignedItems.usable (unsigned_candidates_material fragment env).2 (expressive_rawUnsigned wf typed mal nm expressive env) canonical

theorem expressive_dsat_items_small {fragment : CoreFragment} {ty : MiniType}
    {mm : MalleabilityModifiers} {env : SatEnv} {arguments : Witness}
    (typed : HasType .tapscript fragment ty) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true) (expressive : mm.e = true)
    (sound : env.Sound) (keySizes : ∀ key ∈ fragment.keys, key.bytes.size = 32)
    (canonical : dissatisfy fragment env = some arguments) : ∀ item ∈ arguments, item.size ≤ 32 := by
  intro item member
  exact unsigned_material_small sound keySizes (expressive_dsat_material typed wf mal nm expressive canonical item member)

end LeanMiniscript.Extraction.TapscriptRecovery.DsatMaterial

namespace LeanMiniscript.Extraction.TapscriptRecovery.UnsignedSelection

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI ThresholdRun ThresholdCanonical
  ThresholdSelection DsatMaterial

inductive UnsignedLayout : List CandidatePair → List Bool → List Witness → Prop where
  | nil : UnsignedLayout [] [] []
  | cons {child : CandidatePair} {children : List CandidatePair} {truth : Bool} {truths : List Bool}
      {own : Witness} {frames : List Witness}
      (raw : RawUnsigned (rowResult child truth))
      (usable : (rowResult child truth).usableWitness? = some own)
      (tail : UnsignedLayout children truths frames) :
      UnsignedLayout (child :: children) (truth :: truths) (own :: frames)

theorem UnsignedLayout.layout {children : List CandidatePair} {truths : List Bool} {frames : List Witness}
    (rows : UnsignedLayout children truths frames) : RowLayout children truths frames := by
  induction rows with
  | nil => exact .nil
  | cons _ usable _ ih => exact .cons usable ih

theorem assemble_snoc (frames : List Witness) (own : Witness) :
    assemble (frames ++ [own]) = Witness.combine (assemble frames) own := by
  simp [assemble, Witness.toInitialStack, Witness.combine]

theorem not_flags_count (flags : List Bool) :
    ((flags.map Bool.not).map Bool.toNat).sum = CandidatePair.countUnsigned flags := by
  induction flags with
  | nil => rfl
  | cons flag flags ih => cases flag <;> simp_all [CandidatePair.countUnsigned]

theorem unsigned_layout_included_nonS {children : List CandidatePair} {flags truths : List Bool}
    {frames : List Witness} (security : CandidatePair.SignatureSecurityList children flags)
    (rows : UnsignedLayout children truths frames) : TruthIncluded truths (flags.map Bool.not) := by
  induction security generalizing truths frames with
  | nil => cases rows; exact .nil
  | @cons child flag children flags head tail ih =>
    cases rows with
    | @cons _ _ truth truths _ frames raw usable rest =>
      apply TruthIncluded.cons _ (ih rest)
      intro ht
      subst truth
      cases flag with
      | false => rfl
      | true => exact (signed_excludes_unsigned (head.satSigned rfl) raw).elim

theorem unsigned_layout_eq_nonS {children : List CandidatePair} {flags truths : List Bool}
    {frames : List Witness} {k : Nat}
    (security : CandidatePair.SignatureSecurityList children flags)
    (rows : UnsignedLayout children truths frames)
    (count : (truths.map Bool.toNat).sum = k) (bound : CandidatePair.countUnsigned flags ≤ k) :
    truths = flags.map Bool.not ∧ CandidatePair.countUnsigned flags = k := by
  have included := unsigned_layout_included_nonS security rows
  have upper := truthIncluded_count_le included
  rw [count, not_flags_count] at upper
  have eq : CandidatePair.countUnsigned flags = k := by omega
  exact ⟨truthIncluded_eq_of_count included (by rw [count, not_flags_count, eq]), eq⟩

theorem threshold_security {k : Nat} {children : List CoreFragment}
    {mods : CorrectnessModifiers} {childMods : List MalleabilityModifiers} {env : SatEnv}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    (mal : HasMalleabilityList .tapscript children childMods) :
    CandidatePair.SignatureSecurityList (satisfactionCandidatesList children env) (malleabilitySignedFlags childMods) := by
  cases typed with
  | thresh ft _ _ tt _ _ _ => exact (malleabilityCandidateSoundList env wf.2.1 (.cons ft tt) mal).signatureSecurity

end LeanMiniscript.Extraction.TapscriptRecovery.UnsignedSelection

namespace LeanMiniscript.Extraction.TapscriptRecovery.SignedExchange

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI BWrappers WBoolean ThresholdAlt
  DsatMaterial

def AmbientUnsignedSatCompleteB (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (top : StackElement) (rest : Stack),
    ExecutionContext parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success (top :: rest) []) →
    castToBool top = true → ¬ CheckedSignature fragment env flags own → satisfy fragment env = some own

def AmbientUnsignedSatCompleteW (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (saved top : StackElement) (rest : Stack) (order : BaseWOutputOrder),
    ExecutionContext parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ saved :: (own.toInitialStack ++ rest), item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (saved :: (own.toInitialStack ++ rest)) [] flags env.txCtx
      (.success (order.outputs saved top ++ rest) []) →
    castToBool top = true → ¬ CheckedSignature fragment env flags own → satisfy fragment env = some own

theorem unsignedSatComplete_n {child : CoreFragment} (complete : AmbientUnsignedSatCompleteB child) :
    AmbientUnsignedSatCompleteB (.n child) := by
  intro parent env flags pa po own top rest context nodup bounded run truth noChecked
  obtain ⟨inner, childRun, childTruth⟩ := n_success_child run truth
  exact complete parent env flags pa po own inner rest
    (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded childRun childTruth noChecked

theorem unsignedSatComplete_j {child : CoreFragment} (complete : AmbientUnsignedSatCompleteB child) :
    AmbientUnsignedSatCompleteB (.j child) := by
  intro parent env flags pa po own top rest context nodup bounded run truth noChecked
  exact complete parent env flags pa po own top rest
    (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
    nodup bounded (j_success_child bounded run truth) truth noChecked

theorem unsignedSatCompleteW_from_smaller_B {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {mm : MalleabilityModifiers}
    (typed : HasType .tapscript fragment ⟨.W, mods⟩) (wf : fragment.WellFormed .tapscript)
    (mal : HasMalleability .tapscript fragment mm) (nm : mm.nonMalleable = true) (expressive : mm.e = true)
    (ih : ∀ child, sizeOf child < sizeOf fragment → ∀ cm hm,
      HasType .tapscript child ⟨.B, cm⟩ → child.WellFormed .tapscript →
      HasMalleability .tapscript child hm → hm.nonMalleable = true → hm.e = true → AmbientUnsignedSatCompleteB child) :
    AmbientUnsignedSatCompleteW fragment := by
  cases typed_W_shape typed with
  | @a child cm ct =>
    cases mal
    rename_i childMal
    intro parent env flags pa po own saved top rest order context nodup bounded run truth noChecked
    have childRun := uniform_savedAltTransfer child _ _ saved flags env.txCtx (a_run_child ct wf run)
    exact ih child (by simp) cm _ ct wf childMal nm expressive parent env flags pa po own top rest
      (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
      nodup (fun item h => bounded item (List.mem_cons_of_mem _ h)) childRun truth noChecked
  | @s child cm ct one =>
    cases mal
    rename_i childMal
    intro parent env flags pa po own saved top rest order context nodup bounded run truth noChecked
    obtain ⟨_, childRun⟩ := s_run_child ct one wf run
    apply ih child (by simp) cm _ ct wf childMal nm expressive parent env flags pa po own top (saved :: rest)
      (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
      nodup _ childRun truth noChecked
    intro item member
    apply bounded item
    simp only [List.mem_cons, List.mem_append] at member ⊢
    rcases member with member | rfl | member
    · exact Or.inr (Or.inl member)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr member)

theorem usable_projection_candidate {result : CandidateResult} {witness : Witness}
    (usable : result.usableWitness? = some witness) :
    ∃ candidate, result = .candidate candidate ∧ candidate.status = .usable ∧ candidate.witness = witness := by
  cases result with
  | impossible => cases usable
  | candidate candidate =>
    cases status : candidate.status <;> simp [CandidateResult.usableWitness?, status] at usable
    exact ⟨candidate, rfl, status, usable⟩

end LeanMiniscript.Extraction.TapscriptRecovery.SignedExchange

namespace LeanMiniscript.Extraction.TapscriptRecovery.UnsignedComplete

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction Frames Active OrI Dsat BLeaves BWrappers
  ThresholdRun ThresholdUnit DsatMaterial SignedExchange

theorem complete_of_signed {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {mm : MalleabilityModifiers} (typed : HasType .tapscript fragment ⟨.B, cm⟩)
    (wf : fragment.WellFormed .tapscript) (mal : HasMalleability .tapscript fragment mm)
    (nm : mm.nonMalleable = true) (signed : mm.s = true) : AmbientUnsignedSatCompleteB fragment := by
  intro parent env flags pa po own top rest context _nodup bounded run truth free
  exact (free (signed_consumption_of_malleability wf typed mal signed
    (uniform_B_execution fragment cm mm typed wf mal nm parent env flags pa po own top rest
      context bounded run truth))).elim

theorem zero_B_consumed {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {top : StackElement} {rest : Stack}
    (typed : HasType .tapscript fragment ⟨.B, cm⟩) (wf : fragment.WellFormed .tapscript)
    (zero : cm.z = true)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) : own = [] := by
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf _ _ _ _ _ run
  obtain ⟨args, tail, value, eq, outEq, arity⟩ := effect.b_inv
  have empty : args = [] := List.eq_nil_of_length_eq_zero (arity.1 zero)
  have tailEq := (List.cons.inj outEq).2
  have initial : own.toInitialStack = [] := by simpa [empty, tailEq] using eq
  simpa [Witness.toInitialStack] using congrArg List.reverse initial

theorem complete_sha256 (hash : Hash256) : AmbientUnsignedSatCompleteB (.sha256 hash) := by
  intro parent env flags pa po own top rest context _nodup bounded run truth _free
  obtain ⟨p, eq, matched⟩ := accepts_sha256_inversion bounded run truth
  have ownEq : own = [p] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [ownEq])) (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  simp [satisfy, satisfactionCandidates, hashCandidates, selected, CandidateResult.usable,
    CandidateResult.usableWitness?, ownEq]

theorem complete_hash256 (hash : Hash256) : AmbientUnsignedSatCompleteB (.hash256 hash) := by
  intro parent env flags pa po own top rest context _nodup bounded run truth _free
  obtain ⟨p, eq, matched⟩ := accepts_hash256_inversion bounded run truth
  have ownEq : own = [p] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [ownEq])) (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  simp [satisfy, satisfactionCandidates, hashCandidates, selected, CandidateResult.usable,
    CandidateResult.usableWitness?, ownEq]

theorem complete_hash160 (hash : Hash160) : AmbientUnsignedSatCompleteB (.hash160 hash) := by
  intro parent env flags pa po own top rest context _nodup bounded run truth _free
  obtain ⟨p, eq, matched⟩ := accepts_hash160_inversion bounded run truth
  have ownEq : own = [p] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [ownEq])) (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  simp [satisfy, satisfactionCandidates, hashCandidates, selected, CandidateResult.usable,
    CandidateResult.usableWitness?, ownEq]

theorem complete_ripemd160 (hash : Hash160) : AmbientUnsignedSatCompleteB (.ripemd160 hash) := by
  intro parent env flags pa po own top rest context _nodup bounded run truth _free
  obtain ⟨p, eq, matched⟩ := accepts_ripemd160_inversion bounded run truth
  have ownEq : own = [p] := witness_eq_singleton_of_toInitialStack (List.append_cancel_right eq)
  have selected := disclosed_preimage_selected context.recover context.thirdParty
    (context.consumedIn p (by simp [ownEq])) (context.childLocks _ (by simp [CoreFragment.hashLocks])) matched
  simp [satisfy, satisfactionCandidates, hashCandidates, selected, CandidateResult.usable,
    CandidateResult.usableWitness?, ownEq]

def AmbientUnsignedSatCompleteV (fragment : CoreFragment) : Prop :=
  ∀ (parent : CoreFragment) (env : SatEnv) (flags : ScriptFlags)
    (pa po own : Witness) (rest : Stack),
    ExecutionContext parent fragment env flags pa po own → fragment.keys.Nodup →
    (∀ item ∈ own.toInitialStack ++ rest, item.size ≤ maxScriptElementSize) →
    Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest []) →
    ¬ CheckedSignature fragment env flags own → satisfy fragment env = some own

theorem zero_V_consumed {fragment : CoreFragment} {cm : CorrectnessModifiers}
    {env : SatEnv} {flags : ScriptFlags} {own : Witness} {rest : Stack}
    (typed : HasType .tapscript fragment ⟨.V, cm⟩) (wf : fragment.WellFormed .tapscript)
    (zero : cm.z = true)
    (run : Eval (compile fragment) (own.toInitialStack ++ rest) [] flags env.txCtx (.success rest [])) :
    own = [] := by
  obtain ⟨_, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wf _ _ _ _ _ run
  obtain ⟨args, eq, arity⟩ := effect.v_inv
  have empty : args = [] := List.eq_nil_of_length_eq_zero (arity.1 zero)
  have initial : own.toInitialStack = [] := by simpa [empty] using eq
  simpa [Witness.toInitialStack] using congrArg List.reverse initial

theorem complete_v {child : CoreFragment} (complete : AmbientUnsignedSatCompleteB child) :
    AmbientUnsignedSatCompleteV (.v child) := by
  intro parent env flags pa po own rest context nodup bounded run free
  have unfused := LeanMiniscript.Miniscript.Eval.compileVerify_success_inverse
    (compile_balancedControlFlow child) run
  obtain ⟨mid, midAlt, childRun, verifyRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow child) unfused
  cases verifyRun with
  | verify_success top rest' script alt flags ctx result truth final =>
    cases final
    exact complete parent env flags pa po own top rest
      (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) (fun _ h => h))
      nodup bounded childRun truth free
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem complete_d {child : CoreFragment} {cm : CorrectnessModifiers}
    (typed : HasType .tapscript child ⟨.V, cm⟩) (wf : child.WellFormed .tapscript)
    (zero : cm.z = true) (complete : AmbientUnsignedSatCompleteV child) :
    AmbientUnsignedSatCompleteB (.d child) := by
  intro parent env flags pa po own top rest context nodup bounded run truth free
  have topEq := unit_d typed wf zero env flags _ rest top context.version bounded run truth
  obtain ⟨active, ownEq, childRun⟩ := d_run_frame typed wf run truth
  subst own
  have inChild : ∀ item ∈ active, item ∈ [top] ++ active := fun _ h => List.mem_append_right _ h
  have childBound : ∀ item ∈ active.toInitialStack ++ (top :: rest), item.size ≤ maxScriptElementSize := by
    simpa [Witness.toInitialStack, List.reverse_append, List.append_assoc] using bounded
  have selected := complete parent env flags pa po active (top :: rest)
    (executionContext_restrict context (active := child) (fun _ h => h) (fun _ h => h) inChild)
    nodup childBound childRun (fun checked => free (checkedSignature_mono (fun _ h => h) inChild checked))
  obtain ⟨candidate, eq, usable, witness⟩ := usable_projection_candidate selected
  have activeEq := zero_V_consumed typed wf zero childRun
  simp [satisfy, satisfactionCandidates, eq, CandidateResult.withSelector, CandidateResult.usableWitness?,
    SatisfactionCandidate.withSelector, Witness.withSelector, usable, witness, topEq, activeEq]

theorem allS_count_zero {mods : List MalleabilityModifiers} (all : MalleabilityModifiers.allS mods = true) :
    MalleabilityModifiers.countNonS mods = 0 := by
  induction mods with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp all
    simp [MalleabilityModifiers.countNonS, hs, ih ht]

theorem complete_or_i {X Y : CoreFragment} {cx cy : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.B, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.or_i X Y) mm) (nm : mm.nonMalleable = true)
    (ix : AmbientUnsignedSatCompleteB X) (iy : AmbientUnsignedSatCompleteB Y) :
    AmbientUnsignedSatCompleteB (.or_i X Y) := by
  obtain ⟨mx, my, hx, hy, nx, ny, signed⟩ := or_i_malleability_children mal nm
  intro parent env flags pa po own top rest context nodup bounded run truth free
  rcases or_i_run_B tx ty wx wy context.version run with ⟨active, eq, childRun⟩ | ⟨active, eq, childRun⟩
  · subst own
    have inChild : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
    have keys : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_left _ h
    have cc := executionContext_restrict context keys (fun _ h => List.mem_append_left _ h) inChild
    have absent : ¬ CheckedSignature X env flags active := fun checked => free (checkedSignature_mono keys inChild checked)
    have raw := execution_without_checked_signature
      (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po active top rest cc
        (bounded_without_selector bounded) childRun truth) absent
    have otherSigned : (satisfactionCandidates Y env).sat.Signed := by
      rcases signed with sx | sy
      · exact (signed_excludes_unsigned ((malleabilityCandidateSound env wx tx hx).signedSat sx) raw).elim
      · exact (malleabilityCandidateSound env wy ty hy).signedSat sy
    have selected := ix parent env flags pa po active top rest cc (List.pairwise_append.mp nodup).1
      (bounded_without_selector bounded) childRun truth absent
    change ((satisfactionCandidates X env).sat.withSelector trueElement |>.select
      ((satisfactionCandidates Y env).sat.withSelector falseElement)).usableWitness? = some (active ++ [trueElement])
    rw [rawUnsigned_select_signed_eq (unsigned_withSelector raw) (otherSigned.withSelector _)]
    exact CandidateResult.withSelector_usableWitness_iff.mpr ⟨active, selected, rfl⟩
  · subst own
    have inChild : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
    have keys : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_right _ h
    have cc := executionContext_restrict context keys (fun _ h => List.mem_append_right _ h) inChild
    have absent : ¬ CheckedSignature Y env flags active := fun checked => free (checkedSignature_mono keys inChild checked)
    have raw := execution_without_checked_signature
      (uniform_B_execution Y cy my ty wy hy ny parent env flags pa po active top rest cc
        (bounded_without_selector bounded) childRun truth) absent
    have otherSigned : (satisfactionCandidates X env).sat.Signed := by
      rcases signed with sx | sy
      · exact (malleabilityCandidateSound env wx tx hx).signedSat sx
      · exact (signed_excludes_unsigned ((malleabilityCandidateSound env wy ty hy).signedSat sy) raw).elim
    have selected := iy parent env flags pa po active top rest cc (List.pairwise_append.mp nodup).2.1
      (bounded_without_selector bounded) childRun truth absent
    change ((satisfactionCandidates X env).sat.withSelector trueElement |>.select
      ((satisfactionCandidates Y env).sat.withSelector falseElement)).usableWitness? = some (active ++ [falseElement])
    rw [signed_select_rawUnsigned_eq (otherSigned.withSelector _) (unsigned_withSelector raw)]
    exact CandidateResult.withSelector_usableWitness_iff.mpr ⟨active, selected, rfl⟩

def CompleteVz (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType .tapscript fragment ⟨.V, cm⟩ → fragment.WellFormed .tapscript →
    HasMalleability .tapscript fragment mm → mm.nonMalleable = true → cm.z = true →
    AmbientUnsignedSatCompleteV fragment

end LeanMiniscript.Extraction.TapscriptRecovery.UnsignedComplete

namespace LeanMiniscript.Extraction.TapscriptRecovery.OrDFalseFamily

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat BExecution ThresholdUnit
  UnsignedComplete

theorem andor_dsat_selector {X Y Z : CoreFragment} {cx cz : CorrectnessModifiers}
    {mx mz : MalleabilityModifiers} (tx : HasType .tapscript X ⟨.B, cx⟩)
    (tz : HasType .tapscript Z ⟨.B, cz⟩) (wx : X.WellFormed .tapscript)
    (wz : Z.WellFormed .tapscript) (hx : HasMalleability .tapscript X mx)
    (hz : HasMalleability .tapscript Z mz) (nx : mx.nonMalleable = true)
    (nz : mz.nonMalleable = true) (ex : mx.e = true) (ez : mz.e = true)
    (sx : mx.s = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  exact rawUnsigned_select_signed_eq
    (unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env)
      (expressive_rawUnsigned wz tz hz nz ez env))
    ((malleabilityCandidateSound env wx tx hx).signedSat sx).combine_left.markNonCanonical

theorem andor_dsat_projection {X Y Z : CoreFragment} {env : SatEnv} {x z : Witness}
    (selector : (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat)
    (dx : dissatisfy X env = some x) (dz : dissatisfy Z env = some z) :
    dissatisfy (.andor X Y Z) env = some (z ++ x) := by
  change (satisfactionCandidates (.andor X Y Z) env).dsat.usableWitness? = _
  rw [selector]
  exact CandidateResult.combine_usableWitness_iff.mpr ⟨x, z, dx, dz, rfl⟩

theorem ambientDsatComplete_andor_signed {X Y Z : CoreFragment}
    {cx cy cz : CorrectnessModifiers} {mx mz : MalleabilityModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.B, cy⟩)
    (tz : HasType .tapscript Z ⟨.B, cz⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript) (wz : Z.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (hz : HasMalleability .tapscript Z mz)
    (nx : mx.nonMalleable = true) (nz : mz.nonMalleable = true)
    (ex : mx.e = true) (ez : mz.e = true) (sx : mx.s = true)
    (completeX : AmbientDsatComplete X) (completeZ : AmbientDsatComplete Z) :
    AmbientDsatComplete (.andor X Y Z) := by
  intro parent env flags pa po own resultTop rest context nodup bounded run falsehood free
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  have nodupX : X.keys.Nodup := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).1
  have nodupZ : Z.keys.Nodup := (List.pairwise_append.mp nodup).2.1
  rcases andor_run_B_frame tx ty tz wx wy wz run with
    ⟨left, right, value, eq, runX, falseX, runZ⟩ | ⟨left, right, value, eq, runX, trueX, _runY⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have contextZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have dx := completeX parent env flags pa po left value (right.toInitialStack ++ rest)
      contextX nodupX bounds runX falseX (fun checked => free (checkedSignature_mono keysX inX checked))
    have dz := completeZ parent env flags pa po right resultTop rest contextZ nodupZ
      (fun item h => bounds item (List.mem_append_right _ h)) runZ falsehood
      (fun checked => free (checkedSignature_mono keysZ inZ checked))
    exact andor_dsat_projection (andor_dsat_selector tx tz wx wz hx hz nx nz ex ez sx env) dx dz
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have contextX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have checked := signed_consumption_of_malleability wx tx hx sx
      (uniform_B_execution X cx mx tx wx hx nx parent env flags pa po left value
        (right.toInitialStack ++ rest) contextX bounds runX trueX)
    exact (free (checkedSignature_mono keysX inX checked)).elim

theorem ambientDsatComplete_zero : AmbientDsatComplete .zero := by
  intro parent env flags pa po own top rest _context _nodup _bounded run _falsehood _free
  rw [zero_B_consumed .zero trivial rfl run]
  rfl

end LeanMiniscript.Extraction.TapscriptRecovery.OrDFalseFamily

namespace LeanMiniscript.Extraction.TapscriptRecovery.AndorForced

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI OrDC Dsat BExecution OrDFalseFamily

theorem andor_malleability_split {X Y Z : CoreFragment} {mm : MalleabilityModifiers}
    (mal : HasMalleability .tapscript (.andor X Y Z) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) (s : mm.s = true) :
    ∃ mx my mz, HasMalleability .tapscript X mx ∧ HasMalleability .tapscript Y my ∧
      HasMalleability .tapscript Z mz ∧ mx.nonMalleable = true ∧
      my.nonMalleable = true ∧ mz.nonMalleable = true ∧ mx.e = true ∧
      mz.e = true ∧ mz.s = true ∧
      (mx.s = true ∨ (mx.s = false ∧ my.s = true ∧ my.f = true)) := by
  cases mal with
  | @andor X Y Z mx my mz hx hy hz =>
    obtain ⟨nx, ny, nz, ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    obtain ⟨ez, sf⟩ := Bool.and_eq_true_iff.mp e
    obtain ⟨sz, ss⟩ := Bool.and_eq_true_iff.mp s
    refine ⟨mx, my, mz, hx, hy, hz, nx, ny, nz, ex, ez, sz, ?_⟩
    cases sx : mx.s with
    | true => exact Or.inl rfl
    | false =>
      have sy : my.s = true := by simpa [sx] using ss
      have fy : my.f = true := by simpa [sx] using sf
      exact Or.inr ⟨rfl, sy, fy⟩

theorem andor_dsat_selector_forced {X Y Z : CoreFragment}
    {cx cy cz : CorrectnessModifiers} {mx my mz : MalleabilityModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.B, cy⟩)
    (tz : HasType .tapscript Z ⟨.B, cz⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript) (wz : Z.WellFormed .tapscript)
    (hx : HasMalleability .tapscript X mx) (hy : HasMalleability .tapscript Y my)
    (hz : HasMalleability .tapscript Z mz) (nx : mx.nonMalleable = true)
    (nz : mz.nonMalleable = true) (ex : mx.e = true) (ez : mz.e = true)
    (fy : my.f = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  exact rawUnsigned_select_signed_eq
    (unsigned_combine (expressive_rawUnsigned wx tx hx nx ex env)
      (expressive_rawUnsigned wz tz hz nz ez env))
    ((malleabilityCandidateSound env wy ty hy).forcedDsat fy).combine_right.markNonCanonical

theorem andor_dsat_selector_expressive {X Y Z : CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.andor X Y Z) ⟨.B, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.andor X Y Z) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true) (env : SatEnv) :
    (satisfactionCandidates (.andor X Y Z) env).dsat =
      (satisfactionCandidates X env).dsat.combine (satisfactionCandidates Z env).dsat := by
  obtain ⟨cx, cy, cz, tx, _dx, _ux, ty, tz⟩ := andor_B_typed_children typed
  cases mal with
  | andor hx hy hz =>
    obtain ⟨nx, _ny, nz, ex, _⟩ := (boolAnd5_eq_true _ _ _ _ _).mp nm
    obtain ⟨ez, choice⟩ := Bool.and_eq_true_iff.mp e
    rcases Bool.or_eq_true_iff.mp choice with sx | fy
    · exact andor_dsat_selector tx tz wf.1 wf.2.2.1 hx hz nx nz ex ez sx env
    · exact andor_dsat_selector_forced tx ty tz wf.1 wf.2.1 wf.2.2.1 hx hy hz nx nz ex ez fy env

theorem ambientDsatComplete_andor_forced_middle {X Y Z : CoreFragment}
    {cm : CorrectnessModifiers} {mm : MalleabilityModifiers}
    (typed : HasType .tapscript (.andor X Y Z) ⟨.B, cm⟩)
    (wf : (CoreFragment.andor X Y Z).WellFormed .tapscript)
    (mal : HasMalleability .tapscript (.andor X Y Z) mm)
    (nm : mm.nonMalleable = true) (e : mm.e = true)
    (completeX : AmbientDsatComplete X) (completeZ : AmbientDsatComplete Z)
    (forcedY : AmbientForcedFalse Y) : AmbientDsatComplete (.andor X Y Z) := by
  obtain ⟨cx, cy, cz, tx, _dx, _ux, ty, tz⟩ := andor_B_typed_children typed
  intro parent env flags pa po own resultTop rest context nodup bounded run falsehood free
  have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
  have keysZ : ∀ key ∈ Z.keys, key ∈ (CoreFragment.andor X Y Z).keys :=
    fun _ h => List.mem_append_right _ h
  have nodupX : X.keys.Nodup := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).1
  have nodupY : Y.keys.Nodup := (List.pairwise_append.mp (List.pairwise_append.mp nodup).1).2.1
  have nodupZ : Z.keys.Nodup := (List.pairwise_append.mp nodup).2.1
  rcases andor_run_B_frame tx ty tz wf.1 wf.2.1 wf.2.2.1 run with
    ⟨left, right, value, eq, runX, falseX, runZ⟩ | ⟨left, right, value, eq, _runX, _trueX, runY⟩
  · subst own
    have inX : ∀ item ∈ left, item ∈ right ++ left := fun _ h => List.mem_append_right _ h
    have inZ : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextX := executionContext_restrict context keysX
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) inX
    have contextZ := executionContext_restrict context keysZ (fun _ h => List.mem_append_right _ h) inZ
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have dx := completeX parent env flags pa po left value (right.toInitialStack ++ rest)
      contextX nodupX bounds runX falseX (fun checked => free (checkedSignature_mono keysX inX checked))
    have dz := completeZ parent env flags pa po right resultTop rest contextZ nodupZ
      (fun item h => bounds item (List.mem_append_right _ h)) runZ falsehood
      (fun checked => free (checkedSignature_mono keysZ inZ checked))
    exact andor_dsat_projection (andor_dsat_selector_expressive typed wf mal nm e env) dx dz
  · subst own
    have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
    have contextY := executionContext_restrict context keysY
      (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) inY
    have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
        item.size ≤ maxScriptElementSize := by
      simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
    have checked := forcedY parent env flags pa po right resultTop rest contextY nodupY
      (fun item h => bounds item (List.mem_append_right _ h)) runY falsehood
    exact (free (checkedSignature_mono keysY inY checked)).elim

def UnsignedFalse (fragment : CoreFragment) : Prop :=
  ∀ cm mm, HasType .tapscript fragment ⟨.B, cm⟩ → fragment.WellFormed .tapscript →
    HasMalleability .tapscript fragment mm → mm.nonMalleable = true →
    cm.d = true → cm.u = true → mm.e = true → mm.s = false →
    AmbientDsatComplete fragment

end LeanMiniscript.Extraction.TapscriptRecovery.AndorForced

namespace LeanMiniscript.Extraction.TapscriptRecovery.ForcedMiddle

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction OrI Dsat ForcedAndV SignedV ThresholdUnit

theorem forced_and_v_signed_prefix {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    {mx : MalleabilityModifiers} (tx : HasType .tapscript X ⟨.V, cx⟩)
    (ty : HasType .tapscript Y ⟨.B, cy⟩) (wx : X.WellFormed .tapscript)
    (wy : Y.WellFormed .tapscript) (hx : HasMalleability .tapscript X mx)
    (nx : mx.nonMalleable = true) (sx : mx.s = true) : AmbientForcedFalse (.and_v X Y) :=
  forced_and_v_of_signed_prefix tx ty wx wy
    (uniform_signedV_of_uniform_B uniform_B_execution X cx mx tx wx hx nx sx)

theorem forced_or_d {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.B, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (forcedY : AmbientForcedFalse Y) : AmbientForcedFalse (.or_d X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  obtain ⟨left, right, value, eq, _runX, _falseX, runY⟩ := or_d_false_run_frame tx ty wx wy run falsehood
  subst own
  have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_d X Y).keys := fun _ h => List.mem_append_right _ h
  have inY : ∀ item ∈ right, item ∈ right ++ left := fun _ h => List.mem_append_left _ h
  have contextY := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
  have bounds : ∀ item ∈ left.toInitialStack ++ (right.toInitialStack ++ rest),
      item.size ≤ maxScriptElementSize := by
    simpa only [Witness.toInitialStack_append, List.append_assoc] using bounded
  exact checkedSignature_mono keysY inY
    (forcedY parent env flags pa po right top rest contextY (List.pairwise_append.mp nodup).2.1
      (fun item h => bounds item (List.mem_append_right _ h)) runY falsehood)

theorem forced_or_i {X Y : CoreFragment} {cx cy : CorrectnessModifiers}
    (tx : HasType .tapscript X ⟨.B, cx⟩) (ty : HasType .tapscript Y ⟨.B, cy⟩)
    (wx : X.WellFormed .tapscript) (wy : Y.WellFormed .tapscript)
    (forcedX : AmbientForcedFalse X) (forcedY : AmbientForcedFalse Y) :
    AmbientForcedFalse (.or_i X Y) := by
  intro parent env flags pa po own top rest context nodup bounded run falsehood
  rcases or_i_run_B tx ty wx wy context.version run with
    ⟨active, eq, runX⟩ | ⟨active, eq, runY⟩
  · subst own
    have keysX : ∀ key ∈ X.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_left _ h
    have inX : ∀ item ∈ active, item ∈ active ++ [trueElement] := fun _ h => List.mem_append_left _ h
    have child := executionContext_restrict context keysX (fun _ h => List.mem_append_left _ h) inX
    exact checkedSignature_mono keysX inX (forcedX parent env flags pa po active top rest child
      (List.pairwise_append.mp nodup).1 (bounded_without_selector bounded) runX falsehood)
  · subst own
    have keysY : ∀ key ∈ Y.keys, key ∈ (CoreFragment.or_i X Y).keys := fun _ h => List.mem_append_right _ h
    have inY : ∀ item ∈ active, item ∈ active ++ [falseElement] := fun _ h => List.mem_append_left _ h
    have child := executionContext_restrict context keysY (fun _ h => List.mem_append_right _ h) inY
    exact checkedSignature_mono keysY inY (forcedY parent env flags pa po active top rest child
      (List.pairwise_append.mp nodup).2.1 (bounded_without_selector bounded) runY falsehood)

end LeanMiniscript.Extraction.TapscriptRecovery.ForcedMiddle
