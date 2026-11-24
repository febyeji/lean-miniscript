import LeanMiniscript.Extraction.P2WSHNonMalleabilityInversion

/-!
# P2WSH witness uniqueness for recursive key-choice trees

Key-choice trees satisfy the model witness-uniqueness conclusion by structural
induction: the signature, selected key and complete selector path coincide.
The Core theorem uses the original contracts without additional premises.

The tree grammar consists of `c:pk_k` leaves and recursive `or_i` choices.
Sanity supplies unique keys, while the run contract supplies MINIMALIF,
STRICTENC and environment soundness. The unrestricted
`P2WSHNonMalleability` obligation remains unproved.
-/

namespace LeanMiniscript.Extraction.P2WSHNonMalleabilityKeyChoice

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open P2WSHNonMalleabilitySubcase P2WSHNonMalleabilityInversion

/-- The recursive family of key leaves and explicit IF choices. -/
inductive KeyChoiceTree : CoreFragment → Prop
  | key (key : PubKey) : KeyChoiceTree (.c (.pk_k key))
  | branch {left right : CoreFragment} (first : KeyChoiceTree left)
      (second : KeyChoiceTree right) : KeyChoiceTree (.or_i left right)

/-- Canonical selectors in serialized witness order on a path to one key. -/
inductive KeyChoicePath : CoreFragment → PubKey → Witness → Prop
  | key (key : PubKey) : KeyChoicePath (.c (.pk_k key)) key []
  | left {first second : CoreFragment} {key : PubKey} {selectors : Witness}
      (path : KeyChoicePath first key selectors) :
      KeyChoicePath (.or_i first second) key (selectors ++ [trueElement])
  | right {first second : CoreFragment} {key : PubKey} {selectors : Witness}
      (path : KeyChoicePath second key selectors) :
      KeyChoicePath (.or_i first second) key (selectors ++ [falseElement])

theorem KeyChoicePath.key_mem {fragment : CoreFragment} {key : PubKey} {selectors : Witness}
    (path : KeyChoicePath fragment key selectors) : key ∈ fragment.keys := by
  induction path with
  | key => simp [CoreFragment.keys]
  | left path ih => simp [CoreFragment.keys, ih]
  | right path ih => simp [CoreFragment.keys, ih]

theorem KeyChoicePath.selectors {fragment : CoreFragment} {key : PubKey} {selectors : Witness}
    (path : KeyChoicePath fragment key selectors) :
    ∀ item ∈ selectors, item = falseElement ∨ item = trueElement := by
  induction path with
  | key => simp
  | left path ih =>
      intro item member
      exact (List.mem_append.mp member).elim (ih item) (fun h => Or.inr (List.mem_singleton.mp h))
  | right path ih =>
      intro item member
      exact (List.mem_append.mp member).elim (ih item) (fun h => Or.inl (List.mem_singleton.mp h))

/-- Global key uniqueness fixes the entire branch path, not just its leaf. -/
theorem KeyChoicePath.unique {fragment : CoreFragment} {key : PubKey}
    {first second : Witness} (path : KeyChoicePath fragment key first)
    (other : KeyChoicePath fragment key second) (unique : fragment.NoDuplicateKeys) :
    first = second := by
  induction path generalizing second with
  | key => cases other; rfl
  | @left left right key selectors path ih =>
      have separate := List.nodup_append.mp unique
      cases other with
      | left other => rw [ih other separate.1]
      | right other => exact (separate.2.2 key path.key_mem key other.key_mem rfl).elim
  | @right left right key selectors path ih =>
      have separate := List.nodup_append.mp unique
      cases other with
      | left other => exact (separate.2.2 key other.key_mem key path.key_mem rfl).elim
      | right other => rw [ih other separate.2.1]

/-- Generation exposes one environment signature and its exact branch path. -/
theorem keyChoice_generated {fragment : CoreFragment} (tree : KeyChoiceTree fragment)
    {env : SatEnv} {witness : Witness} (generated : satisfy fragment env = some witness) :
    ∃ sig key selectors, witness = sig :: selectors ∧
      env.signatureFor key = some sig ∧ KeyChoicePath fragment key selectors := by
  induction tree generalizing witness with
  | key key =>
      cases selected : env.signatureFor key with
      | none => simp [satisfy, satisfactionCandidates, keyCandidates, selected] at generated
      | some sig =>
          simp only [satisfy, satisfactionCandidates, keyCandidates, selected,
            CandidateResult.usable_witness?, Option.some.injEq] at generated
          exact ⟨sig, key, [], generated.symm, selected, .key key⟩
  | @branch left right first second leftIH rightIH =>
      change (((satisfactionCandidates left env).sat.withSelector trueElement).select
        ((satisfactionCandidates right env).sat.withSelector falseElement)).usableWitness? =
          some witness at generated
      rcases CandidateResult.select_usableWitness_cases generated with fromLeft | fromRight
      · obtain ⟨inner, selected, witnessEq⟩ :=
          CandidateResult.withSelector_usableWitness_iff.mp fromLeft
        obtain ⟨sig, key, selectors, innerEq, signed, path⟩ := leftIH selected
        exact ⟨sig, key, selectors ++ [trueElement], by simp [witnessEq, innerEq, Witness.withSelector],
          signed, .left path⟩
      · obtain ⟨inner, selected, witnessEq⟩ :=
          CandidateResult.withSelector_usableWitness_iff.mp fromRight
        obtain ⟨sig, key, selectors, innerEq, signed, path⟩ := rightIH selected
        exact ⟨sig, key, selectors ++ [falseElement], by simp [witnessEq, innerEq, Witness.withSelector],
          signed, .right path⟩

/-- Arbitrary successful key-choice execution recovers one checked signature
    and the complete canonical path consumed from the witness. -/
theorem keyChoice_inversion {fragment : CoreFragment} (tree : KeyChoiceTree fragment)
    {witness : Witness} {flags : ScriptFlags} {ctx : TxContext} {top : StackElement}
    {alt : Stack} (minimal : flags.minimalIf = true) (version : ctx.sigVersion = .witnessV0)
    (executed : Eval (compile fragment) witness.reverse [] flags ctx (.success [top] alt))
    (truth : castToBool top = true) :
    ∃ sig key selectors, witness = sig :: selectors ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key.bytes = .ok true ∧
      KeyChoicePath fragment key selectors := by
  induction tree generalizing witness with
  | key key =>
      obtain ⟨sig, pubkey, childRun, checked⟩ := c_inversion (.pk_k key) executed truth
      have pushed := evaluate_eq_of_eval CryptoOracle.model_refines childRun
      simp only [compile, compileWithKeyHash, evaluate, ExecResult.success.injEq,
        List.cons.injEq] at pushed
      obtain ⟨⟨rfl, stackEq⟩, _⟩ := pushed
      have witnessEq := congrArg List.reverse stackEq
      simp only [List.reverse_reverse, List.reverse_singleton] at witnessEq
      exact ⟨sig, key, [], witnessEq, checked, .key key⟩
  | @branch left right first second leftIH rightIH =>
      obtain ⟨rest, selected | selected⟩ := or_i_inversion left right minimal version executed
      · obtain ⟨sig, key, selectors, restEq, checked, path⟩ :=
          leftIH (witness := rest.reverse) (by simpa using selected.2)
        have witnessEq := congrArg List.reverse selected.1
        simp only [List.reverse_reverse, List.reverse_cons] at witnessEq
        exact ⟨sig, key, selectors ++ [trueElement], by simp [witnessEq, restEq], checked, .left path⟩
      · obtain ⟨sig, key, selectors, restEq, checked, path⟩ :=
          rightIH (witness := rest.reverse) (by simpa using selected.2)
        have witnessEq := congrArg List.reverse selected.1
        simp only [List.reverse_reverse, List.reverse_cons] at witnessEq
        exact ⟨sig, key, selectors ++ [falseElement], by simp [witnessEq, restEq], checked, .right path⟩

/-- The nonempty canonical selector cannot pass a STRICTENC signature check. -/
theorem checked_signature_ne_true
    {flags : ScriptFlags} {ctx : TxContext} {sig pubkey : StackElement}
    (strict : flags.strictEncoding = true) (version : ctx.sigVersion = .witnessV0)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true) :
    sig ≠ trueElement := by
  intro same
  subst sig
  have encoded := encoding_of_checkSigWithEncoding_ok checked
  simp [checkSigEncodingFor, version, checkECDSAEncoding, checkSignatureEncoding,
    strict, isValidSignatureEncoding, trueElement, bind, Except.bind] at encoded

/-- The model-level uniqueness obligation holds for every key-choice tree.
    Soundness excludes the empty selector as a signature and STRICTENC excludes
    the true selector; distinct-key exclusion and unique paths finish the proof. -/
theorem keyChoice_modelWitnessUnique
    {fragment : CoreFragment} (tree : KeyChoiceTree fragment)
    (unique : fragment.NoDuplicateKeys)
    (env : SatEnv) (flags : ScriptFlags) (arguments other : Witness)
    (modeled : ModeledContextFlags .p2wsh flags)
    (version : ModeledContextVersion .p2wsh env.txCtx) (sound : env.Sound)
    (generated : satisfyFinal fragment env = some arguments)
    (thirdParty : ThirdPartyWitness fragment env.txCtx arguments other)
    (accepted : ∃ top, Eval (compile fragment) other.reverse [] flags env.txCtx
      (.success [top] []) ∧ castToBool top = true) :
    other = arguments := by
  obtain ⟨top, evaluated, truth⟩ := accepted
  obtain ⟨sig, key, selectors, otherEq, checked, path⟩ :=
    keyChoice_inversion tree modeled.1 version evaluated truth
  obtain ⟨sig0, key0, selectors0, argsEq, selected, path0⟩ :=
    keyChoice_generated tree (satisfyFinal_some_satisfy generated)
  have valid := verifySigFor_of_checkSigWithEncoding_true checked
  have member : sig ∈ other := by simp [otherEq]
  have revealed := thirdParty.2.1 sig member key path.key_mem valid
  have sigEq : sig = sig0 := by
    rw [argsEq] at revealed
    rcases List.mem_cons.mp revealed with equal | selector
    · exact equal
    · rcases path0.selectors sig selector with empty | truthy
      · have invalid := sound.emptySignatureInvalid key
        rw [empty, invalid] at valid
        contradiction
      · exact (checked_signature_ne_true modeled.2.2.2.2 version checked truthy).elim
  have keyEq : key = key0 := by
    apply Classical.byContradiction
    intro different
    exact thirdParty.1 sig member key path.key_mem key0 path0.key_mem different valid
      (sigEq ▸ sound.signatureValid selected)
  subst key0
  have selectorsEq := path.unique path0 unique
  rw [otherEq, argsEq, sigEq, selectorsEq]

/-- Every sane key-choice tree has a unique accepted third-party witness
    under the existing compilation and run contracts. -/
theorem p2wshNonMalleability_keyChoice
    (sane : SaneFragment .p2wsh) (tree : KeyChoiceTree sane.checked.fragment)
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (thirdParty : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) : other = arguments := by
  obtain ⟨top, evaluated, truth, _⟩ := p2wshAccepted_frame sane bytes scriptPubKey suffix
    env flags ctx oracles keyPath other serialized spend run accepted
  obtain ⟨_, _, _, _, modeled, sound, _, context, _⟩ := run
  have version : ModeledContextVersion .p2wsh env.txCtx := by rw [context]; rfl
  exact keyChoice_modelWitnessUnique tree sane.noDuplicateKeys env flags.script arguments other
    modeled version sound generated thirdParty ⟨top, evaluated, truth⟩

end LeanMiniscript.Extraction.P2WSHNonMalleabilityKeyChoice
