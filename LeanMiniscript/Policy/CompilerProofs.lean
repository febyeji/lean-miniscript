import LeanMiniscript.Policy.Compiler
import LeanMiniscript.Miniscript.SatisfactionPossibilityProofs
import LeanMiniscript.Miniscript.SatisfactionCorrectnessProofs
import LeanMiniscript.Miniscript.TypeInferenceProofs

/-!
# Policy compiler correctness

`Preserves policy fragment` states that a Miniscript fragment means exactly
what the policy means: for every atom material, the fragment is structurally
satisfiable (`CoreFragment.isSatisfiableWith`) precisely when the material
satisfies the policy (`Policy.eval`). Both directions are proved for the
structural translation and for every candidate of the cost-based compiler,
hence for every result of `compilePolicy` and `compilePolicyChecked`.

Combined with `satisfactionPossible_iff_isSatisfiableWith`, the meaning lifts
to the concrete satisfier: a compiled policy has a raw satisfaction candidate
in an environment exactly when the environment's signatures, preimages, and
timelocks satisfy the policy, and every final witness produced for it is
accepted by the compiled Script.
-/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-- A fragment preserves a policy's meaning under every atom material. -/
def Preserves (policy : Policy) (fragment : CoreFragment) : Prop :=
  ∀ material : Material,
    fragment.isSatisfiableWith material.atom = policy.eval material

/-- Pointwise meaning preservation for threshold children. -/
def PreservesList : List Policy → List CoreFragment → Prop
  | [], [] => True
  | policy :: policies, fragment :: fragments =>
      Preserves policy fragment ∧ PreservesList policies fragments
  | _, _ => False

theorem PreservesList.count {policies : List Policy} {fragments : List CoreFragment}
    (preserves : PreservesList policies fragments) (material : Material) :
    CoreFragment.countSatisfiableWith material.atom fragments =
      Policy.evalCount material policies := by
  induction policies generalizing fragments with
  | nil =>
      cases fragments with
      | nil => rfl
      | cons => exact absurd preserves id
  | cons policy policies ih =>
      cases fragments with
      | nil => exact absurd preserves id
      | cons fragment fragments =>
          simp only [CoreFragment.countSatisfiableWith, Policy.evalCount,
            preserves.1 material, ih preserves.2]

theorem preserves_thresh {k : Nat} {policies : List Policy}
    {fragments : List CoreFragment} (preserves : PreservesList policies fragments) :
    Preserves (.thresh k policies) (.thresh k fragments) := by
  intro material
  simp [CoreFragment.isSatisfiableWith, Policy.eval, preserves.count material]

/-! ## Structural translation -/

namespace Policy

mutual
  /-- The structural translation preserves the policy's meaning. -/
  theorem toMiniscript_preserves : (policy : Policy) →
      Preserves policy policy.toMiniscript
    | .unsatisfiable => by
        intro material; simp [toMiniscript, CoreFragment.isSatisfiableWith, eval]
    | .trivial => by
        intro material; simp [toMiniscript, CoreFragment.isSatisfiableWith, eval]
    | .key _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .after _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .older _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .sha256 _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .hash256 _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .ripemd160 _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .hash160 _ => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval, Material.atom]
    | .and left right => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval,
          toMiniscript_preserves left material, toMiniscript_preserves right material]
    | .or _ left _ right => by
        intro material
        simp [toMiniscript, CoreFragment.isSatisfiableWith, eval,
          toMiniscript_preserves left material, toMiniscript_preserves right material]
    | .thresh _ subs => by
        simpa [toMiniscript] using preserves_thresh (toMiniscriptList_preserves subs)

  /-- Threshold children of the structural translation. -/
  theorem toMiniscriptList_preserves : (subs : List Policy) →
      PreservesList subs (toMiniscriptList subs)
    | [] => True.intro
    | sub :: subs => ⟨toMiniscript_preserves sub, toMiniscriptTail_preserves subs⟩

  /-- `a:`-wrapped threshold children of the structural translation. -/
  theorem toMiniscriptTail_preserves : (subs : List Policy) →
      PreservesList subs (toMiniscriptTail subs)
    | [] => True.intro
    | sub :: subs => ⟨by
        intro material
        simpa [CoreFragment.isSatisfiableWith] using
          toMiniscript_preserves sub material,
        toMiniscriptTail_preserves subs⟩
end

end Policy

/-! ## Cost-based candidates -/

/-- Every candidate in a list preserves the policy's meaning. -/
def AllPreserve (policy : Policy) (candidates : List Candidate) : Prop :=
  ∀ candidate ∈ candidates, Preserves policy candidate.fragment

theorem realizeTemplate_fragment {ctx : ScriptContext} {template : Template}
    {candidate : Candidate} (realized : realizeTemplate ctx template = some candidate) :
    candidate.fragment = template.fragment := by
  unfold realizeTemplate at realized
  cases hType : inferType ctx template.fragment with
  | none => simp [hType] at realized
  | some ty =>
      cases hMall : inferMalleability ctx template.fragment with
      | none =>
          simp only [hType, hMall, Option.some.injEq] at realized
          rw [← realized]
      | some mods =>
          by_cases hNon : mods.nonMalleable = true
          · simp only [hType, hMall, hNon, if_true, Option.some.injEq] at realized
            rw [← realized]
          · simp [hType, hMall, hNon] at realized

theorem mem_realize {ctx : ScriptContext} {templates : List Template}
    {candidate : Candidate} (member : candidate ∈ realize ctx templates) :
    ∃ template ∈ templates, candidate.fragment = template.fragment := by
  simp only [realize, List.mem_filterMap] at member
  obtain ⟨template, templateMember, realized⟩ := member
  exact ⟨template, templateMember, realizeTemplate_fragment realized⟩

theorem realize_preserves {ctx : ScriptContext} {policy : Policy}
    {templates : List Template}
    (preserves : ∀ template ∈ templates, Preserves policy template.fragment) :
    AllPreserve policy (realize ctx templates) := by
  intro candidate member
  obtain ⟨template, templateMember, fragmentEq⟩ := mem_realize member
  rw [fragmentEq]
  exact preserves template templateMember

theorem mem_insertCheapest {satProb dsatProb : Float} {kept : List Candidate}
    {candidate other : Candidate}
    (member : other ∈ insertCheapest satProb dsatProb kept candidate) :
    other ∈ kept ∨ other = candidate := by
  unfold insertCheapest at member
  split at member
  · simp only [List.mem_append, List.mem_singleton] at member
    exact member
  · split at member
    · simp only [List.mem_cons, List.mem_filter] at member
      rcases member with rfl | ⟨member, _⟩
      · exact Or.inr rfl
      · exact Or.inl member
    · exact Or.inl member

theorem mem_prune {satProb dsatProb : Float} {candidates : List Candidate}
    {candidate : Candidate} (member : candidate ∈ prune satProb dsatProb candidates) :
    candidate ∈ candidates := by
  unfold prune at member
  have general : ∀ (remaining kept : List Candidate),
      candidate ∈ remaining.foldl (insertCheapest satProb dsatProb) kept →
        candidate ∈ kept ∨ candidate ∈ remaining := by
    intro remaining
    induction remaining with
    | nil => intro kept member; exact Or.inl member
    | cons head tail ih =>
        intro kept member
        rcases ih _ member with inserted | inTail
        · rcases mem_insertCheapest inserted with inKept | rfl
          · exact Or.inl inKept
          · exact Or.inr (by simp)
        · exact Or.inr (by simp [inTail])
  rcases general candidates [] member with inKept | inCandidates
  · simp at inKept
  · exact inCandidates

theorem prune_preserves {policy : Policy} {satProb dsatProb : Float}
    {candidates : List Candidate} (preserves : AllPreserve policy candidates) :
    AllPreserve policy (prune satProb dsatProb candidates) :=
  fun candidate member => preserves candidate (mem_prune member)

theorem wrapTemplates_preserves {policy : Policy} {candidate : Candidate}
    (preserves : Preserves policy candidate.fragment) :
    ∀ template ∈ wrapTemplates candidate, Preserves policy template.fragment := by
  intro template member material
  simp only [wrapTemplates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CoreFragment.isSatisfiableWith, preserves material]

theorem closeOnce_preserves {ctx : ScriptContext} {policy : Policy}
    {satProb dsatProb : Float} {candidates : List Candidate}
    (preserves : AllPreserve policy candidates) :
    AllPreserve policy (closeOnce ctx satProb dsatProb candidates) := by
  apply prune_preserves
  intro candidate member
  simp only [List.mem_append, List.mem_flatMap] at member
  rcases member with member | ⟨source, sourceMember, wrapped⟩
  · exact preserves candidate member
  · exact realize_preserves (wrapTemplates_preserves (preserves source sourceMember))
      candidate wrapped

theorem closeWrappers_preserves {ctx : ScriptContext} {policy : Policy}
    {satProb dsatProb : Float} {candidates : List Candidate}
    (preserves : AllPreserve policy candidates) :
    AllPreserve policy (closeWrappers ctx satProb dsatProb candidates) :=
  closeOnce_preserves (closeOnce_preserves (closeOnce_preserves
    (prune_preserves preserves)))

theorem leafTemplates_preserves (ctx : ScriptContext) (policy : Policy) :
    ∀ template ∈ leafTemplates ctx policy, Preserves policy template.fragment := by
  intro template member material
  cases policy <;>
    simp only [leafTemplates, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    (try rcases member with rfl | rfl) <;>
    (try subst member) <;>
    simp [CoreFragment.isSatisfiableWith, Policy.eval, Material.atom]

theorem andTemplates_preserves {left right : Policy} {x y : Candidate}
    (preservesX : Preserves left x.fragment) (preservesY : Preserves right y.fragment) :
    ∀ template ∈ andTemplates x y,
      Preserves (.and left right) template.fragment := by
  intro template member material
  simp only [andTemplates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [CoreFragment.isSatisfiableWith, Policy.eval, preservesX material,
      preservesY material]

theorem andTemplates_swap_preserves {left right : Policy} {x y : Candidate}
    (preservesX : Preserves left x.fragment) (preservesY : Preserves right y.fragment) :
    ∀ template ∈ andTemplates y x,
      Preserves (.and left right) template.fragment := by
  intro template member material
  simp only [andTemplates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [CoreFragment.isSatisfiableWith, Policy.eval, preservesX material,
      preservesY material, Bool.and_comm]

theorem orTemplates_preserves {leftWeight rightWeight : Nat} {left right : Policy}
    {x z : Candidate} {px pz : Float}
    (preservesX : Preserves left x.fragment) (preservesZ : Preserves right z.fragment) :
    ∀ template ∈ orTemplates x z px pz,
      Preserves (.or leftWeight left rightWeight right) template.fragment := by
  intro template member material
  simp only [orTemplates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [CoreFragment.isSatisfiableWith, Policy.eval, preservesX material,
      preservesZ material]

theorem orTemplates_swap_preserves {leftWeight rightWeight : Nat}
    {left right : Policy} {x z : Candidate} {px pz : Float}
    (preservesX : Preserves left x.fragment) (preservesZ : Preserves right z.fragment) :
    ∀ template ∈ orTemplates z x pz px,
      Preserves (.or leftWeight left rightWeight right) template.fragment := by
  intro template member material
  simp only [orTemplates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [CoreFragment.isSatisfiableWith, Policy.eval, preservesX material,
      preservesZ material, Bool.or_comm]

theorem pickBest_mem {satProb dsatProb : Float} {predicate : Candidate → Bool} :
    {candidates : List Candidate} → {best : Candidate} →
      pickBest satProb dsatProb predicate candidates = some best → best ∈ candidates
  | [], _, picked => by simp [pickBest] at picked
  | candidate :: candidates, best, picked => by
      unfold pickBest at picked
      split at picked
      · split at picked
        · simp at picked; simp [picked]
        · simp at picked
      · rename_i previous hPrevious
        split at picked
        · simp at picked; simp [picked]
        · simp at picked
          subst picked
          exact List.mem_cons_of_mem _ (pickBest_mem hPrevious)

/-- Candidate lists for threshold children, pointwise preserving. -/
def ChildrenPreserve : List Policy → List (List Candidate) → Prop
  | [], [] => True
  | policy :: policies, candidates :: rest =>
      AllPreserve policy candidates ∧ ChildrenPreserve policies rest
  | _, _ => False

theorem chooseThreshTail_preserves {satProb dsatProb : Float} :
    {policies : List Policy} → {choices : List (List Candidate)} →
      {chosen : List Candidate} →
      ChildrenPreserve policies choices →
      chooseThreshTail satProb dsatProb choices = some chosen →
      PreservesList policies (chosen.map Candidate.fragment)
  | [], [], chosen, _, picked => by
      simp [chooseThreshTail] at picked
      subst picked
      trivial
  | [], _ :: _, _, preserves, _ => absurd preserves id
  | _ :: _, [], _, preserves, _ => absurd preserves id
  | policy :: policies, choices :: rest, chosen, preserves, picked => by
      simp only [chooseThreshTail] at picked
      cases hBest : pickBest satProb dsatProb isWdu choices with
      | none => simp [hBest] at picked
      | some best =>
          cases hTail : chooseThreshTail satProb dsatProb rest with
          | none => simp [hBest, hTail] at picked
          | some tail =>
              simp only [hBest, hTail, Option.bind_some, Option.pure_def,
                Option.some.injEq, bind] at picked
              subst picked
              exact ⟨preserves.1 best (pickBest_mem hBest),
                chooseThreshTail_preserves preserves.2 hTail⟩

theorem chooseThreshChildren_preserves {satProb dsatProb : Float}
    {policies : List Policy} {choices : List (List Candidate)}
    {chosen : List Candidate} (preserves : ChildrenPreserve policies choices)
    (picked : chooseThreshChildren satProb dsatProb choices = some chosen) :
    PreservesList policies (chosen.map Candidate.fragment) := by
  cases policies with
  | nil =>
      cases choices with
      | nil => simp [chooseThreshChildren] at picked
      | cons => exact absurd preserves id
  | cons policy policies =>
      cases choices with
      | nil => exact absurd preserves id
      | cons choices rest =>
          simp only [chooseThreshChildren] at picked
          cases hFirst : pickBest satProb dsatProb isBdu choices with
          | none => simp [hFirst] at picked
          | some first =>
              cases hTail : chooseThreshTail satProb dsatProb rest with
              | none => simp [hFirst, hTail] at picked
              | some tail =>
                  simp only [hFirst, hTail, Option.bind_some, Option.pure_def,
                    Option.some.injEq, bind] at picked
                  subst picked
                  exact ⟨preserves.1 first (pickBest_mem hFirst),
                    chooseThreshTail_preserves preserves.2 hTail⟩

theorem threshTemplates_preserves {satProb dsatProb : Float} {k : Nat}
    {policies : List Policy} {choices : List (List Candidate)}
    (preserves : ChildrenPreserve policies choices) :
    ∀ template ∈ threshTemplates satProb dsatProb k choices,
      Preserves (.thresh k policies) template.fragment := by
  intro template member
  unfold threshTemplates at member
  split at member
  · simp at member
  · rename_i chosen hChosen
    simp only [List.mem_singleton] at member
    subst member
    exact preserves_thresh (chooseThreshChildren_preserves preserves hChosen)

theorem allKeys_eq {subs : List Policy} {keys : List PubKey}
    (allKeysEq : allKeys subs = some keys) : subs = keys.map Policy.key := by
  induction subs generalizing keys with
  | nil => simp [allKeys] at allKeysEq; subst allKeysEq; rfl
  | cons sub subs ih =>
      cases sub with
      | key pubKey =>
          simp only [allKeys, Option.map_eq_some_iff] at allKeysEq
          obtain ⟨rest, hRest, rfl⟩ := allKeysEq
          simp [ih hRest]
      | _ => simp [allKeys] at allKeysEq

theorem evalCount_keys (material : Material) (keys : List PubKey) :
    Policy.evalCount material (keys.map Policy.key) = material.signerCount keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp [Policy.evalCount, Material.signerCount, Policy.eval, ih]

theorem multiTemplates_preserves (ctx : ScriptContext) (k : Nat) (subs : List Policy) :
    ∀ template ∈ multiTemplates ctx k subs,
      Preserves (.thresh k subs) template.fragment := by
  intro template member material
  unfold multiTemplates at member
  split at member
  · simp at member
  · rename_i keys hKeys
    rw [allKeys_eq hKeys]
    cases ctx <;>
      simp only [List.mem_singleton] at member <;> subst member <;>
      simp [CoreFragment.isSatisfiableWith, Material.atom, Policy.eval,
        evalCount_keys]

mutual
  /-- Every cost-based compilation candidate preserves the policy's meaning. -/
  theorem compileCandidates_preserves (ctx : ScriptContext) :
      (policy : Policy) → (satProb dsatProb : Float) →
        AllPreserve policy (compileCandidates ctx policy satProb dsatProb)
    | .and left right, satProb, dsatProb => by
        rw [compileCandidates]
        apply closeWrappers_preserves
        apply realize_preserves
        intro template member
        simp only [List.mem_append, List.mem_flatMap] at member
        rcases member with ⟨x, xMember, y, yMember, member⟩ |
            ⟨y, yMember, x, xMember, member⟩
        · exact andTemplates_preserves
            (compileCandidates_preserves ctx left satProb dsatProb x xMember)
            (compileCandidates_preserves ctx right satProb dsatProb y yMember)
            template member
        · exact andTemplates_swap_preserves
            (compileCandidates_preserves ctx left satProb dsatProb x xMember)
            (compileCandidates_preserves ctx right satProb dsatProb y yMember)
            template member
    | .or leftWeight left rightWeight right, satProb, dsatProb => by
        rw [compileCandidates]
        apply closeWrappers_preserves
        apply realize_preserves
        intro template member
        simp only [List.mem_append, List.mem_flatMap] at member
        rcases member with ⟨x, xMember, z, zMember, member⟩ |
            ⟨z, zMember, x, xMember, member⟩
        · exact orTemplates_preserves
            (compileCandidates_preserves ctx left _ _ x xMember)
            (compileCandidates_preserves ctx right _ _ z zMember)
            template member
        · exact orTemplates_swap_preserves
            (compileCandidates_preserves ctx left _ _ x xMember)
            (compileCandidates_preserves ctx right _ _ z zMember)
            template member
    | .thresh k subs, satProb, dsatProb => by
        rw [compileCandidates]
        apply closeWrappers_preserves
        apply realize_preserves
        intro template member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact threshTemplates_preserves
            (compileCandidatesList_preserves ctx subs _ _) template member
        · exact multiTemplates_preserves ctx k subs template member
    | .unsatisfiable, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .trivial, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .key _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .after _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .older _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .sha256 _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .hash256 _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .ripemd160 _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))
    | .hash160 _, satProb, dsatProb => by
        simp only [compileCandidates]
        exact closeWrappers_preserves
          (realize_preserves (leafTemplates_preserves ctx _))

  /-- Threshold children candidate lists preserve their branches. -/
  theorem compileCandidatesList_preserves (ctx : ScriptContext) :
      (subs : List Policy) → (satProb dsatProb : Float) →
        ChildrenPreserve subs (compileCandidatesList ctx subs satProb dsatProb)
    | [], _, _ => by simp [compileCandidatesList, ChildrenPreserve]
    | sub :: subs, satProb, dsatProb => by
        rw [compileCandidatesList]
        exact ⟨compileCandidates_preserves ctx sub satProb dsatProb,
          compileCandidatesList_preserves ctx subs satProb dsatProb⟩
end

theorem rankedFragments_preserves (ctx : ScriptContext) (policy : Policy) :
    ∀ fragment ∈ rankedFragments ctx policy, Preserves policy fragment := by
  intro fragment member
  simp only [rankedFragments, List.mem_map, List.mem_mergeSort,
    List.mem_filter] at member
  obtain ⟨candidate, ⟨candidateMember, _⟩, rfl⟩ := member
  exact compileCandidates_preserves ctx policy 1 0 candidate candidateMember

/-! ## Compilation boundaries -/

theorem checkSane_fragment {ctx : ScriptContext} {fragment : CoreFragment}
    {sane : SaneFragment ctx} (checked : checkSane ctx fragment = .ok sane) :
    sane.checked.fragment = fragment := by
  unfold checkSane at checked
  split at checked
  · split at checked
    · cases checked
    · dsimp only at checked
      split at checked
      · split at checked
        · split at checked
          · cases checked
          · split at checked
            · split at checked
              · split at checked
                · cases checked
                  rfl
                · cases checked
              · cases checked
            · cases checked
        · cases checked
      · cases checked
  · cases checked

theorem firstSane_mem {ctx : ScriptContext} :
    {fragments : List CoreFragment} → {sane : SaneFragment ctx} →
      firstSane ctx fragments = some sane → sane.checked.fragment ∈ fragments
  | [], _, found => by simp [firstSane] at found
  | fragment :: fragments, sane, found => by
      unfold firstSane at found
      split at found
      · rename_i result hResult
        simp at found
        subst found
        simp [checkSane_fragment hResult]
      · exact List.mem_cons_of_mem _ (firstSane_mem found)

theorem ofRaw_fragment {ctx : ScriptContext} {fragment : CoreFragment}
    {checked : CheckedFragment ctx}
    (found : CheckedFragment.ofRaw? ctx fragment = some checked) :
    checked.fragment = fragment := by
  unfold CheckedFragment.ofRaw? at found
  split at found
  · split at found
    · simp at found; rw [← found]
    · simp at found
  · simp at found

theorem firstChecked_mem {ctx : ScriptContext} :
    {fragments : List CoreFragment} → {checked : CheckedFragment ctx} →
      firstChecked ctx fragments = some checked → checked.fragment ∈ fragments
  | [], _, found => by simp [firstChecked] at found
  | fragment :: fragments, checked, found => by
      unfold firstChecked at found
      split at found
      · rename_i result hResult
        simp at found
        subst found
        simp [ofRaw_fragment hResult]
      · exact List.mem_cons_of_mem _ (firstChecked_mem found)

/-- Every sane Miniscript returned by `compilePolicy` preserves the policy's
    meaning. -/
theorem compilePolicy_preserves {ctx : ScriptContext} {policy : Policy}
    {sane : SaneFragment ctx} (compiled : compilePolicy ctx policy = .ok sane) :
    Preserves policy sane.checked.fragment := by
  unfold compilePolicy at compiled
  simp only at compiled
  split at compiled
  · rename_i found hFound
    simp at compiled
    subst compiled
    exact rankedFragments_preserves ctx policy _ (firstSane_mem hFound)
  · split at compiled
    · rename_i best rest hRanked
      rw [checkSane_fragment compiled]
      exact rankedFragments_preserves ctx policy best (by simp [hRanked])
    · rw [checkSane_fragment compiled]
      exact Policy.toMiniscript_preserves policy

/-- Every valid Miniscript returned by `compilePolicyChecked` preserves the
    policy's meaning. -/
theorem compilePolicyChecked_preserves {ctx : ScriptContext} {policy : Policy}
    {checked : CheckedFragment ctx}
    (compiled : compilePolicyChecked ctx policy = some checked) :
    Preserves policy checked.fragment := by
  unfold compilePolicyChecked at compiled
  split at compiled
  · rename_i found hFound
    simp at compiled
    subst compiled
    exact rankedFragments_preserves ctx policy _ (firstChecked_mem hFound)
  · rw [ofRaw_fragment compiled]
    exact Policy.toMiniscript_preserves policy

/-! ## Validity of the structural translation -/

namespace Policy

mutual
  theorem toMiniscript_timelocks : (policy : Policy) →
      policy.toMiniscript.timelocks = policy.timelocks
    | .unsatisfiable | .trivial | .key _ | .sha256 _ | .hash256 _
    | .ripemd160 _ | .hash160 _ => by
        simp [toMiniscript, timelocks, CoreFragment.timelocks,
          TimelockUsage.union, TimelockUsage.empty]
    | .after _ | .older _ => by
        simp [toMiniscript, timelocks, CoreFragment.timelocks]
    | .and left right => by
        simp [toMiniscript, timelocks, CoreFragment.timelocks,
          toMiniscript_timelocks left, toMiniscript_timelocks right]
    | .or _ left _ right => by
        simp [toMiniscript, timelocks, CoreFragment.timelocks,
          toMiniscript_timelocks left, toMiniscript_timelocks right]
    | .thresh _ subs => by
        simp [toMiniscript, timelocks, CoreFragment.timelocks,
          toMiniscriptList_timelocks subs]

  theorem toMiniscriptList_timelocks : (subs : List Policy) →
      CoreFragment.listTimelocks (toMiniscriptList subs) = listTimelocks subs
    | [] => rfl
    | sub :: subs => by
        simp [toMiniscriptList, CoreFragment.listTimelocks, listTimelocks,
          toMiniscript_timelocks sub, toMiniscriptTail_timelocks subs]

  theorem toMiniscriptTail_timelocks : (subs : List Policy) →
      CoreFragment.listTimelocks (toMiniscriptTail subs) = listTimelocks subs
    | [] => rfl
    | sub :: subs => by
        simp [toMiniscriptTail, CoreFragment.listTimelocks, listTimelocks,
          CoreFragment.timelocks, toMiniscript_timelocks sub,
          toMiniscriptTail_timelocks subs]
end

theorem toMiniscriptTail_length (subs : List Policy) :
    (toMiniscriptTail subs).length = subs.length := by
  induction subs with
  | nil => rfl
  | cons sub subs ih => simp [toMiniscriptTail, ih]

theorem toMiniscriptList_length (subs : List Policy) :
    (toMiniscriptList subs).length = subs.length := by
  cases subs with
  | nil => rfl
  | cons sub subs => simp [toMiniscriptList, toMiniscriptTail_length]

theorem toMiniscriptTail_pairwise (subs : List Policy)
    (pairwise : listTimelocksPairwiseCompatible subs) :
    CoreFragment.listTimelocksPairwiseCompatible (toMiniscriptTail subs) := by
  induction subs with
  | nil => trivial
  | cons sub subs ih =>
      simp only [toMiniscriptTail, CoreFragment.listTimelocksPairwiseCompatible,
        CoreFragment.timelocks, toMiniscript_timelocks,
        toMiniscriptTail_timelocks]
      exact ⟨pairwise.1, ih pairwise.2⟩

theorem toMiniscriptList_pairwise (subs : List Policy)
    (pairwise : listTimelocksPairwiseCompatible subs) :
    CoreFragment.listTimelocksPairwiseCompatible (toMiniscriptList subs) := by
  cases subs with
  | nil => trivial
  | cons sub subs =>
      simp only [toMiniscriptList, CoreFragment.listTimelocksPairwiseCompatible,
        toMiniscript_timelocks, toMiniscriptTail_timelocks]
      exact ⟨pairwise.1, toMiniscriptTail_pairwise subs pairwise.2⟩

/-- A context-valid `Bdu` fragment. -/
structure BduValid (ctx : ScriptContext) (fragment : CoreFragment) : Prop where
  wellFormed : fragment.WellFormed ctx
  typed : ∃ mods, HasType ctx fragment ⟨.B, mods⟩ ∧ mods.d = true ∧ mods.u = true

mutual
  /-- The structural translation of a well-formed policy is a well-formed
      `Bdu` Miniscript in the same context. -/
  theorem toMiniscript_valid (ctx : ScriptContext) : (policy : Policy) →
      policy.WellFormed ctx → BduValid ctx policy.toMiniscript
    | .unsatisfiable, _ => ⟨True.intro, ⟨_, HasType.zero, rfl, rfl⟩⟩
    | .trivial, _ =>
        ⟨⟨True.intro, True.intro⟩,
          ⟨_, HasType.or_i HasType.one HasType.zero True.intro rfl, rfl, rfl⟩⟩
    | .key pubKey, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.c_wrap (HasType.pk_k pubKey), rfl, rfl⟩⟩
    | .after n, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.n_wrap (HasType.d_wrap
          (HasType.v_wrap (HasType.after n)) rfl), rfl, rfl⟩⟩
    | .older n, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.n_wrap (HasType.d_wrap
          (HasType.v_wrap (HasType.older n)) rfl), rfl, rfl⟩⟩
    | .sha256 hash, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.sha256 hash, rfl, rfl⟩⟩
    | .hash256 hash, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.hash256 hash, rfl, rfl⟩⟩
    | .ripemd160 hash, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.ripemd160 hash, rfl, rfl⟩⟩
    | .hash160 hash, wellFormed =>
        ⟨wellFormed, ⟨_, HasType.hash160 hash, rfl, rfl⟩⟩
    | .and left right, wellFormed => by
        obtain ⟨leftValid, rightValid, compatible⟩ := wellFormed
        obtain ⟨leftWellFormed, leftMods, leftTyped, leftD, _⟩ :=
          toMiniscript_valid ctx left leftValid
        obtain ⟨rightWellFormed, rightMods, rightTyped, rightD, _⟩ :=
          toMiniscript_valid ctx right rightValid
        refine ⟨⟨leftWellFormed, rightWellFormed, ?_⟩,
          ⟨_, HasType.and_b leftTyped (HasType.a_wrap rightTyped), ?_, rfl⟩⟩
        · simpa [CoreFragment.andTimelocksCompatible, CoreFragment.timelocks,
            toMiniscript_timelocks] using compatible
        · simp [leftD, rightD]
    | .or _ left _ right, wellFormed => by
        obtain ⟨leftValid, rightValid⟩ := wellFormed
        obtain ⟨leftWellFormed, leftMods, leftTyped, leftD, leftU⟩ :=
          toMiniscript_valid ctx left leftValid
        obtain ⟨rightWellFormed, rightMods, rightTyped, rightD, rightU⟩ :=
          toMiniscript_valid ctx right rightValid
        exact ⟨⟨leftWellFormed, rightWellFormed⟩,
          ⟨_, HasType.or_d leftTyped leftD leftU rightTyped, rightD, rightU⟩⟩
    | .thresh k subs, wellFormed => by
        obtain ⟨⟨positive, atMost⟩, subsValid, pairwise, bound⟩ := wellFormed
        cases subs with
        | nil => simp at atMost; omega
        | cons sub rest =>
            obtain ⟨subValid, restValid⟩ := subsValid
            obtain ⟨subWellFormed, subMods, subTyped, subD, subU⟩ :=
              toMiniscript_valid ctx sub subValid
            obtain ⟨restWellFormed, restTypes, restTyped, restShape⟩ :=
              toMiniscriptTail_valid ctx rest restValid
            refine ⟨⟨?_, ⟨subWellFormed, restWellFormed⟩, ?_, bound⟩,
              ⟨_, HasType.thresh subTyped subD subU restTyped restShape positive
                (by simpa [toMiniscriptList, toMiniscriptTail_length] using atMost),
                rfl, rfl⟩⟩
            · exact ⟨positive, by
                simpa [toMiniscriptList_length] using atMost⟩
            · intro twoLe
              exact toMiniscriptList_pairwise (sub :: rest) (pairwise twoLe)

  /-- `a:`-wrapped threshold children are well-formed `Wdu` fragments. -/
  theorem toMiniscriptTail_valid (ctx : ScriptContext) : (subs : List Policy) →
      allWellFormed ctx subs →
      CoreFragment.allWellFormed ctx (toMiniscriptTail subs) ∧
        ∃ types, HasTypeList ctx (toMiniscriptTail subs) types ∧
          thresholdRestTypes types
    | [], _ => ⟨True.intro, ⟨[], HasTypeList.nil, True.intro⟩⟩
    | sub :: subs, valid => by
        obtain ⟨subValid, restValid⟩ := valid
        obtain ⟨subWellFormed, subMods, subTyped, subD, subU⟩ :=
          toMiniscript_valid ctx sub subValid
        obtain ⟨restWellFormed, restTypes, restTyped, restShape⟩ :=
          toMiniscriptTail_valid ctx subs restValid
        exact ⟨⟨subWellFormed, restWellFormed⟩,
          ⟨_ :: restTypes, HasTypeList.cons (HasType.a_wrap subTyped) restTyped,
            ⟨rfl, subD, subU, restShape⟩⟩⟩
end

/-- The structural translation of a well-formed policy is a valid top-level
    Miniscript carrying the `d` guarantee. -/
theorem toMiniscript_validDissatisfiable {ctx : ScriptContext} {policy : Policy}
    (wellFormed : policy.WellFormed ctx) :
    ValidDissatisfiableMiniscript ctx policy.toMiniscript := by
  obtain ⟨fragmentWellFormed, mods, typed, dissatisfiable, _⟩ :=
    toMiniscript_valid ctx policy wellFormed
  exact ⟨mods, ⟨fragmentWellFormed, typed⟩, dissatisfiable⟩

end Policy

/-- `compilePolicyChecked` succeeds on every well-formed policy. -/
theorem compilePolicyChecked_isSome {ctx : ScriptContext} {policy : Policy}
    (wellFormed : policy.WellFormed ctx) :
    (compilePolicyChecked ctx policy).isSome = true := by
  unfold compilePolicyChecked
  split
  · rfl
  · obtain ⟨fragmentWellFormed, mods, typed, _, _⟩ :=
      Policy.toMiniscript_valid ctx policy wellFormed
    simp [CheckedFragment.ofRaw?, fragmentWellFormed, inferTyped_complete typed]

/-! ## Satisfier-level semantics -/

/-- A valid Miniscript that preserves a policy has a raw satisfaction
    candidate exactly when the environment's material satisfies the policy. -/
theorem satisfactionPossible_iff_eval {ctx : ScriptContext} {policy : Policy}
    {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType ctx fragment ty) (wellFormed : fragment.WellFormed ctx)
    (preserves : Preserves policy fragment) (env : SatEnv) :
    (satisfactionCandidates fragment env).sat.Possible ↔
      policy.eval env.material = true := by
  rw [satisfactionPossible_iff_isSatisfiableWith typed wellFormed env,
    preserves env.material]

/-- Satisfier-level meaning of `compilePolicy`: the compiled sane Miniscript
    has a raw satisfaction candidate exactly when the environment satisfies
    the policy. -/
theorem compilePolicy_satisfactionPossible_iff {ctx : ScriptContext}
    {policy : Policy} {sane : SaneFragment ctx}
    (compiled : compilePolicy ctx policy = .ok sane) (env : SatEnv) :
    (satisfactionCandidates sane.checked.fragment env).sat.Possible ↔
      policy.eval env.material = true :=
  satisfactionPossible_iff_eval sane.checked.hasType sane.checked.wellFormed
    (compilePolicy_preserves compiled) env

/-- Satisfier-level meaning of `compilePolicyChecked`. -/
theorem compilePolicyChecked_satisfactionPossible_iff {ctx : ScriptContext}
    {policy : Policy} {checked : CheckedFragment ctx}
    (compiled : compilePolicyChecked ctx policy = some checked) (env : SatEnv) :
    (satisfactionCandidates checked.fragment env).sat.Possible ↔
      policy.eval env.material = true :=
  satisfactionPossible_iff_eval checked.hasType checked.wellFormed
    (compilePolicyChecked_preserves compiled) env

/-- End-to-end soundness of `compilePolicy`: any witness returned by the
    satisfier for the compiled Miniscript comes from material satisfying the
    policy, and the compiled Script accepts it under the modeled context. -/
theorem compilePolicy_satisfy_sound {ctx : ScriptContext} {policy : Policy}
    {sane : SaneFragment ctx} {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (compiled : compilePolicy ctx policy = .ok sane)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (satisfied : satisfy sane.checked.fragment env = some witness) :
    policy.eval env.material = true ∧
      Accepts ctx (compile sane.checked.fragment) witness flags env.txCtx := by
  refine ⟨?_, satisfactionCorrectnessCore sane.validMiniscript sound encodings
    version modeled satisfied⟩
  apply (compilePolicy_satisfactionPossible_iff compiled env).mp
  unfold satisfy at satisfied
  intro impossible
  rw [impossible] at satisfied
  simp at satisfied

/-- The final BIP 379 projection, which additionally requires a usable
    signed candidate, inherits the same soundness. -/
theorem compilePolicy_satisfyFinal_sound {ctx : ScriptContext} {policy : Policy}
    {sane : SaneFragment ctx} {env : SatEnv} {witness : Witness}
    {flags : ScriptFlags}
    (compiled : compilePolicy ctx policy = .ok sane)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (satisfied : satisfyFinal sane.checked.fragment env = some witness) :
    policy.eval env.material = true ∧
      Accepts ctx (compile sane.checked.fragment) witness flags env.txCtx :=
  compilePolicy_satisfy_sound compiled sound encodings version modeled
    (satisfyFinal_some_satisfy satisfied)

end LeanMiniscript.Policy
