import LeanMiniscript.Extraction.TapscriptSignatureDisclosure

/-! Recover material in a descendant's generated row and lift frame recovery
through the native witness-v0 VerifyScript boundary. -/

namespace LeanMiniscript.Extraction.P2WSHRecovery

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript TapscriptWitness

abbrev ExecutionContext := ExecutionContextIn .p2wsh

/-- A successful checked signature from the observed witness occurs in the
    selected satisfaction of its own child, including a nested threshold row. -/
theorem signature_in_satisfaction {root child env flags args other consumed expected}
    (ctx : ExecutionContext root child env flags args other consumed)
    (path : FragmentPath child root.checked.fragment) (selected : satisfy child env = some expected)
    {sig : StackElement} {key : PubKey} (observed : sig ∈ other) (hk : key ∈ child.keys)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    sig ∈ expected := by
  have keyMem := ctx.keys _ hk
  have valid := verifySigFor_of_checkSigWithEncoding checked
  have published := ctx.thirdParty.2.1 sig observed key keyMem valid
  let P := fun item : StackElement => item = sig → sig ∈ expected
  have strict := ctx.modeled.2.2.2.2
  have empty : P falseElement := by
    rintro rfl
    rw [ctx.sound.emptySignatureInvalid] at valid
    contradiction
  have one : P trueElement := fun eq =>
    (P2WSHNonMalleabilityKeyChoice.checked_signature_ne_true strict ctx.version checked eq.symm).elim
  have hole : CanonicalPairItems P (satisfactionCandidates child env) := by
    constructor
    · rintro c eq usable _ item inRow rfl
      have same : c.witness = expected := by
        simpa [satisfy, eq, CandidateResult.usableWitness?, usable] using selected
      exact same ▸ inRow
    · exact canonical_dsat_items child env empty one (fun k mem eq =>
        (checked_ne_key root ctx.version strict (ctx.keys _ mem) checked eq.symm).elim)
  have foreign {sibling : CoreFragment} (sub : FragmentPath sibling root.checked.fragment)
      (distinct : ∀ k ∈ child.keys, ∀ k' ∈ sibling.keys, k ≠ k') :
      CanonicalPairItems P (satisfactionCandidates sibling env) := by
    have trace := candidates_material sibling env
    have lift {result : CandidateResult} (h : result.Supports (Items (Material sibling env))) :
        CanonicalItems P result := by
      rintro c eq usable _ item mem rfl
      have material := h c.witness (by simp [eq, CandidateResult.usableWitness?, usable]) item mem
      have origin := checked_source_signature root ctx.sound ctx.version ctx.modeled ctx.thirdParty
        ctx.recover.2 observed keyMem sub.keys sub.locks material checked
      exact (distinct key hk key origin.1 rfl).elim
    exact ⟨lift trace.1, lift trace.2⟩
  have atRoot := canonical_path_items path empty one foreign hole .here root.noDuplicateKeys
  obtain ⟨_, wf, typed⟩ := root.validMiniscript
  have origin := (malleabilityCandidateSound env wf typed root.hasMalleability).canonicalSat root.nonMalleable
  have projection := ctx.canonical
  unfold satisfy at projection
  cases eq : (satisfactionCandidates root.checked.fragment env).sat with
  | impossible => simp [eq, CandidateResult.usableWitness?] at projection
  | candidate c =>
    cases status : c.status with
    | dontUse => simp [eq, CandidateResult.usableWitness?, status] at projection
    | usable =>
      have same : c.witness = args := by simpa [eq, CandidateResult.usableWitness?, status] using projection
      exact atRoot.1 c eq status (origin c eq status) sig (same.symm ▸ published) rfl

/-- Every usable expressive dissatisfaction is canonical. Its selectors and
    compressed keys cannot supply the signature of an executed row. -/
theorem expressive_dsat_excludes_checked {root child env flags args other consumed}
    (ctx : ExecutionContext root child env flags args other consumed)
    {source : CoreFragment} {ty : MiniType} {mm : MalleabilityModifiers}
    (typed : HasType .p2wsh source ty) (wf : source.WellFormed .p2wsh)
    (mal : HasMalleability .p2wsh source mm) (nm : mm.nonMalleable = true) (e : mm.e = true)
    (keys : ∀ k ∈ source.keys, k ∈ root.checked.fragment.keys)
    {frame : Witness} (projection : dissatisfy source env = some frame)
    {sig : StackElement} {key : PubKey}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true) :
    sig ∉ frame := by
  let P := fun item : StackElement => sig ≠ item
  have valid := verifySigFor_of_checkSigWithEncoding checked
  have strict := ctx.modeled.2.2.2.2
  have empty : P falseElement := by
    rintro rfl
    rw [ctx.sound.emptySignatureInvalid] at valid
    contradiction
  have items := canonical_dsat_items source env empty
    (P2WSHNonMalleabilityKeyChoice.checked_signature_ne_true strict ctx.version checked)
    (fun k hk => checked_ne_key root ctx.version strict (keys _ hk) checked)
  obtain ⟨c, eq, _, canonical⟩ := (malleabilityCandidateSound env wf typed mal).expressiveDsat nm e
  change (satisfactionCandidates source env).dsat.usableWitness? = some frame at projection
  cases status : c.status <;> simp [eq, CandidateResult.usableWitness?, status] at projection
  subst frame
  exact fun mem => items c eq status (canonical c eq status) sig mem rfl

/-- An accepted native P2WSH spend supplies a bounded, typed B execution and
    the local material facts used by frame recovery. -/
theorem nonMalleability_of_rootFrameUnique (sane : SaneFragment .p2wsh)
    (unique : ∀ {env flags arguments other cm},
      HasType .p2wsh sane.checked.fragment ⟨.B, cm⟩ →
      ExecutionContext sane sane.checked.fragment env flags arguments other other →
      env.EncodingSound flags → (∀ item ∈ other.toInitialStack, item.size ≤ maxScriptElementSize) →
      ∀ top, Eval (compile sane.checked.fragment) other.toInitialStack [] flags env.txCtx
        (.success [top] []) → castToBool top = true → other = arguments)
    (bytes scriptPubKey : ByteArray) (suffix : Witness) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (third : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (slots : LocalHashSlotRecovery sane.checked.fragment env arguments)
    (disjoint : LocalPreimageSignatureDisjoint sane.checked.fragment env flags.script arguments)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) : other = arguments := by
  obtain ⟨top, _, evaluated, truth⟩ := P2WSHNonMalleabilitySubcase.p2wshAccepted_eval sane bytes
    scriptPubKey suffix env flags ctx oracles keyPath other serialized spend run accepted
  obtain ⟨rfl, rfl, programTruth⟩ := spend
  rw [P2WSHNonMalleabilitySubcase.coreVerifyScript_p2wsh_eq_witnessScript flags ctx oracles
    keyPath other bytes programTruth run.1] at accepted
  have small := (P2WSHNonMalleabilitySubcase.executeCoreWitnessScript_ok_of_witnessV0 _ flags _
    rfl accepted).1
  obtain ⟨_, _, _, _, modeled, sound, encoding, context, _⟩ := run
  obtain ⟨_, _, typed⟩ := sane.validMiniscript
  have localCtx : ExecutionContext sane sane.checked.fragment env flags.script arguments other other :=
    ⟨sound, by rw [ModeledContextVersion, context]; rfl, modeled, satisfyFinal_some_satisfy generated,
      third, ⟨slots, disjoint⟩, fun _ h => h, fun _ h => h, fun _ h => h⟩
  apply unique typed localCtx encoding _ top (Miniscript.Eval.compile_erase_altStack evaluated) truth
  simpa [Witness.toInitialStack, List.any_eq_false] using small

end LeanMiniscript.Extraction.P2WSHRecovery
