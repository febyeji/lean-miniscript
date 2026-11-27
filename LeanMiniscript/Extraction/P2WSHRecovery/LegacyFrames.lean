import LeanMiniscript.Extraction.P2WSHRecovery.Frames
import LeanMiniscript.Extraction.P2WSHRecovery.LegacySignatures
import LeanMiniscript.Extraction.TapscriptMultiAWitnessProofs

/-! Match the keys selected by the legacy multisignature generator to the
keys consumed by the evaluator, in their common top-first order. -/

namespace LeanMiniscript.Extraction.P2WSHRecovery

open LeanMiniscript.Script LeanMiniscript.Miniscript TapscriptWitness P2WSHNonMalleabilityInversion

private theorem encoded_match_of_versioned {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .witnessV0) (keys sigs : Stack)
    (matched : checkMultiSigFor checkSig flags ctx sigs keys = .ok true) :
    checkMultiSigWithEncoding checkSig flags ctx.sigHash sigs keys = .ok true := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> simp_all [checkMultiSigFor, checkMultiSigWithEncoding]
  | cons key keys ih =>
    cases sigs with
    | nil => simp [checkMultiSigWithEncoding]
    | cons sig sigs =>
      cases encoded : checkSigEncodingFor flags ctx.sigVersion sig key with
      | error err => simp [checkMultiSigFor, encoded, bind, Except.bind] at matched
      | ok v =>
        cases v
        have ecdsa : checkECDSAEncoding flags sig key = .ok () := by
          cases h : checkECDSAEncoding flags sig key with
          | ok v => cases v; rfl
          | error err => simp [checkSigEncodingFor, version, h, bind, Except.bind] at encoded
        simp only [checkMultiSigFor, encoded, bind, Except.bind] at matched
        simp only [checkMultiSigWithEncoding, ecdsa, bind, Except.bind]
        generalize (if checkSig sig key ctx.sigHash then sigs else sig :: sigs) = remaining at matched ⊢
        split at matched <;> rename_i bound
        · contradiction
        · rw [if_neg bound]
          exact ih _ matched

private theorem ordered_frame {env : SatEnv} {sigs : Stack} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env sigs keys) :
    ∃ used, used.Sublist keys ∧ SignatureFrame (fun s k => env.signatureFor k = some s) sigs used := by
  induction ordered with
  | nil => exact ⟨[], List.nil_sublist _, .nil⟩
  | skip _ ih =>
    obtain ⟨used, sub, frame⟩ := ih
    exact ⟨used, sub.cons _, frame⟩
  | take selected _ ih =>
    obtain ⟨used, sub, frame⟩ := ih
    exact ⟨_ :: used, sub.cons_cons _, .cons selected frame⟩

private theorem frame_key {P : StackElement → PubKey → Prop} {sigs : Stack} {keys : List PubKey}
    (frame : SignatureFrame P sigs keys) {key : PubKey} (hk : key ∈ keys) :
    ∃ sig ∈ sigs, P sig key := by
  induction frame with
  | nil => contradiction
  | cons h _ ih =>
    rcases List.mem_cons.mp hk with rfl | mem
    · exact ⟨_, .head _, h⟩
    · obtain ⟨s, hs, p⟩ := ih mem
      exact ⟨s, .tail _ hs, p⟩

private theorem frame_length {P : StackElement → PubKey → Prop} {sigs : Stack} {keys : List PubKey}
    (frame : SignatureFrame P sigs keys) : sigs.length = keys.length := by
  induction frame <;> simp_all

private theorem frame_eq {env : SatEnv} {a b : Stack} {keys : List PubKey}
    (fa : SignatureFrame (fun s k => env.signatureFor k = some s) a keys)
    (fb : SignatureFrame (fun s k => env.signatureFor k = some s) b keys) : a = b := by
  induction fa generalizing b with
  | nil => cases fb; rfl
  | cons ha _ ih =>
    cases fb with
    | cons hb tail => rw [Option.some.inj (ha.symm.trans hb), ih tail]

/-- Membership determines the relative order of two subsequences of an
    ambient list of distinct keys. -/
private theorem sublist_of_common {α : Type} {a b keys : List α}
    (ha : a.Sublist keys) (hb : b.Sublist keys) (nd : keys.Nodup)
    (incl : a ⊆ b) : a.Sublist b := by
  induction hb generalizing a with
  | slnil => exact ha
  | @cons k b rest sub ih =>
    have hnd := List.nodup_cons.mp nd
    cases ha with
    | cons _ ha => exact ih ha hnd.2 incl
    | cons_cons _ ha => exact (hnd.1 (sub.subset (incl (.head _)))).elim
  | @cons_cons k b rest sub ih =>
    have hnd := List.nodup_cons.mp nd
    cases ha with
    | cons _ ha =>
      apply List.Sublist.cons _ (ih ha hnd.2 _)
      intro x hx
      exact (List.mem_cons.mp (incl hx)).resolve_left (fun eq => hnd.1 (eq ▸ ha.subset hx))
    | cons_cons _ ha =>
      apply List.Sublist.cons_cons _ (ih ha hnd.2 _)
      intro x hx
      exact (List.mem_cons.mp (incl (.tail _ hx))).resolve_left (fun eq => hnd.1 (eq ▸ ha.subset hx))

/-- On either truth value the input is exactly the threshold signatures and
    the canonical NULLDUMMY item. NULLFAIL fixes all signatures on false. -/
theorem multi_frame {k : Nat} {keys : List PubKey} {own : Witness} {rest : Stack}
    {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (wf : (CoreFragment.multi k keys).WellFormed .p2wsh)
    (modeled : ModeledContextFlags .p2wsh flags)
    (run : Eval (compile (.multi k keys)) (own.toInitialStack ++ rest) [] flags ctx
      (.success (top :: rest) [])) :
    ∃ sigs, own = falseElement :: sigs.reverse ∧ sigs.length = k ∧
      checkMultiSigFor checkSig flags ctx sigs (keys.map PubKey.bytes).reverse = .ok (castToBool top) ∧
      (castToBool top = false → ∀ s ∈ sigs, s = falseElement) := by
  obtain ⟨_, sigs, dummy, tail, result, input, output, count, dummyOk, checked, allowed⟩ :=
    Miniscript.Eval.legacyMulti_checked_frame wf.2.2.1 wf.2.1.2 run
  obtain ⟨rfl, rfl⟩ := List.cons.inj output
  have empty : dummy = falseElement := by
    have ok : nullDummySatisfied flags dummy := by
      by_cases h : nullDummySatisfied flags dummy
      · exact h
      · simp [checkMultiSigDummy, h] at dummyOk
    have eq := ok.resolve_left (by simp [modeled.2.2.1])
    exact ByteArray.ext (beq_iff_eq.mp eq)
  subst dummy
  have args : own.toInitialStack = (sigs ++ [falseElement]) :=
    List.append_cancel_right (by simpa using input)
  refine ⟨sigs, by simpa [Witness.toInitialStack] using congrArg List.reverse args, count, ?_, ?_⟩
  · simpa [P2WSHNonMalleabilitySubcase.castToBool_boolToElement] using checked
  · intro neg sig mem
    rw [P2WSHNonMalleabilitySubcase.castToBool_boolToElement] at neg
    have nullFail := allowed.resolve_left (by simp [neg])
    exact eq_falseElement_of_size_zero (nullFail.resolve_left (by simp [modeled.2.2.2.1]) sig mem)

/-- For every occurrence of a legacy multi, the matching key subsequence and
    the generator's exact-count subsequence coincide. -/
theorem multi_agreement {root env flags args other own expected k keys rest top}
    (ctx : ExecutionContext root (.multi k keys) env flags args other own)
    (path : FragmentPath (.multi k keys) root.checked.fragment)
    (wf : (CoreFragment.multi k keys).WellFormed .p2wsh) (encoding : env.EncodingSound flags)
    (selected : satisfy (.multi k keys) env = some expected)
    (run : Eval (compile (.multi k keys)) (own.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) : own = expected := by
  obtain ⟨sigs, wire, count, checked, _⟩ := multi_frame wf ctx.modeled run
  rw [truth] at checked
  have observed (s) (hs : s ∈ sigs) : s ∈ own := by simp [wire, hs]
  have matched := encoded_match_of_versioned ctx.version _ _ checked
  rw [← List.map_reverse] at matched
  obtain ⟨used, usedSub, usedFrame⟩ := multisig_lookup_frame_of_satisfy root ctx.sound ctx.version
    ctx.modeled ctx.canonical (agreement_of_disjoint ctx.recover.2) ctx.thirdParty
    (fun s hs => ctx.items s (observed s hs)) (fun k hk => ctx.keys k (List.mem_reverse.mp hk)) matched
  have projection := selected
  change (legacyMultiCandidates k keys env).sat.usableWitness? = some expected at selected
  unfold legacyMultiCandidates at selected
  split at selected
  · contradiction
  · obtain ⟨inner, choice, eq⟩ := CandidateResult.finalizeLegacyMulti_usableWitness_iff.mp selected
    obtain ⟨frames, trace⟩ := CandidatePair.selectExactly_choiceTrace choice
    obtain ⟨ordered, innerCount⟩ := trace.toOrderedMultiSignatures
    obtain ⟨chosen, chosenSub, chosenFrame⟩ := ordered_frame ordered
    have incl : used ⊆ chosen := by
      intro key hk
      obtain ⟨sig, hs, lookup⟩ := frame_key usedFrame hk
      have keyMem : key ∈ keys := List.mem_reverse.mp (usedSub.subset hk)
      have valid := ctx.sound.signatureValid lookup
      have inRow := signature_in_satisfaction ctx path
        projection
        (observed sig hs) keyMem (checkSigWithEncoding_true (encoding _ _ lookup) valid)
      rw [eq] at inRow
      rcases List.mem_cons.mp inRow with empty | inInner
      · rw [empty, ctx.sound.emptySignatureInvalid] at valid
        contradiction
      · obtain ⟨source, hsource, selectedSig⟩ := chosenFrame.origin (List.mem_reverse.mp inInner)
        by_cases same : key = source
        · exact same ▸ hsource
        · exact (ctx.thirdParty.1 sig (ctx.items _ (observed _ hs)) key (ctx.keys _ keyMem)
            source (ctx.keys _ (List.mem_reverse.mp (chosenSub.subset hsource))) same
            valid (ctx.sound.signatureValid selectedSig)).elim
    have nd : keys.Nodup := path.noDup root.noDuplicateKeys
    have sameKeys := (sublist_of_common usedSub chosenSub (by simpa [CoreFragment.keys, List.Nodup, List.pairwise_reverse, ne_comm] using nd) incl).eq_of_length
      ((frame_length usedFrame).symm.trans (count.trans (innerCount.symm.trans (frame_length chosenFrame))))
    subst chosen
    rw [wire, eq, frame_eq usedFrame chosenFrame]

end LeanMiniscript.Extraction.P2WSHRecovery
