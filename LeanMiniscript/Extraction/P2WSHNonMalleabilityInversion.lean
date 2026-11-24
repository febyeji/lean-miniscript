import LeanMiniscript.Extraction.P2WSHNonMalleabilitySubcase
import LeanMiniscript.Miniscript.TypeSoundnessProofs

/-!
# P2WSH execution decomposition and signature witness uniqueness

`compiled_prefix_inversion` covers every well-formed typed fragment inside an
arbitrary successful continuation. The `and_v`, `v`, `c` and `or_i` inversions
recover child executions and their relevant checks. `p2wshAccepted_frame`
transfers the typed frame guarantees to an arbitrary accepted P2WSH witness.

Witness uniqueness is proved for `c:pk_h` and for every sane `signatureChain`.
The chain proof uses a positional signature-frame lemma applicable to any
fragment with aligned generated and accepted signature frames. Mixed witnesses
also contain preimages, selectors or public keys; that lemma alone does not
establish their positional provenance.

The unrestricted `P2WSHNonMalleability` obligation remains unproved.
-/

namespace LeanMiniscript.Extraction.P2WSHNonMalleabilityInversion

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open LeanMiniscript.Properties P2WSHNonMalleabilitySubcase

/-- Every typed fragment can be inverted inside an arbitrary successful
    continuation, retaining its execution and exact typed argument frame. -/
theorem compiled_prefix_inversion
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {suffix : Script} {stack alt out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (typed : HasType scriptCtx fragment ty) (wellFormed : fragment.WellFormed scriptCtx)
    (executed : Eval (compile fragment ++ suffix) stack alt flags ctx (.success out outAlt)) :
    ∃ middle,
      Eval (compile fragment) stack alt flags ctx (.success middle alt) ∧
      RefinedBaseStackEffect ty stack middle ∧
      Eval suffix middle alt flags ctx (.success out outAlt) := by
  obtain ⟨middle, middleAlt, first, rest⟩ :=
    Eval.splitBalancedAppend_success (compile_balancedControlFlow fragment) executed
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType typed wellFormed
    stack alt flags ctx _ first
  subst middleAlt
  exact ⟨middle, first, effect, rest⟩

/-- An arbitrary sane accepted fragment restores the empty alt stack and
    consumes the whole witness with the argument-count guarantees of its type. -/
theorem p2wshAccepted_frame
    (sane : SaneFragment .p2wsh)
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray) (env : SatEnv)
    (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh env flags ctx oracles bytes)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    ∃ top, Eval (compile sane.checked.fragment) other.reverse [] flags.script env.txCtx
      (.success [top] []) ∧ castToBool top = true ∧
      ArgumentFrameMatches .B sane.checked.ty.mods other.reverse := by
  obtain ⟨top, alt, evaluated, truth⟩ := p2wshAccepted_eval sane bytes scriptPubKey suffix
    env flags ctx oracles keyPath other serialized spend run accepted
  obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType sane.checked.hasType
    sane.checked.wellFormed other.reverse [] flags.script env.txCtx _ evaluated
  subst alt
  have tyEq : sane.checked.ty = ⟨.B, sane.checked.ty.mods⟩ := by
    cases h : sane.checked.ty with
    | mk base mods => have := sane.topLevel; simp_all
  rw [tyEq] at effect
  obtain ⟨args, rest, result, inputEq, outputEq, matchesFrame⟩ := effect.b_inv
  have restEq : rest = [] := (List.cons.inj outputEq).2.symm
  subst rest
  simp only [List.append_nil] at inputEq
  exact ⟨top, evaluated, truth, inputEq ▸ matchesFrame⟩

/-- Sequential fragments expose both successful executions for arbitrary
    children, flags and input frames. -/
theorem and_v_inversion
    (first second : CoreFragment) {stack alt out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : Eval (compile (.and_v first second)) stack alt flags ctx
      (.success out outAlt)) :
    ∃ middle middleAlt,
      Eval (compile first) stack alt flags ctx (.success middle middleAlt) ∧
      Eval (compile second) middle middleAlt flags ctx (.success out outAlt) := by
  exact Eval.splitBalancedAppend_success (compile_balancedControlFlow first) executed

/-- A successful `v:` wrapper exposes the child's truthy result even when
    compilation fused the terminal verification opcode. -/
theorem v_inversion
    (child : CoreFragment) {stack alt out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : Eval (compile (.v child)) stack alt flags ctx (.success out outAlt)) :
    ∃ top, Eval (compile child) stack alt flags ctx (.success (top :: out) outAlt) ∧
      castToBool top = true := by
  have expanded := Eval.compileVerify_success_inverse (compile_balancedControlFlow child)
    (show Eval (compileVerify (compile child)) stack alt flags ctx (.success out outAlt)
      from executed)
  obtain ⟨middle, middleAlt, childRun, verifyRun⟩ :=
    Eval.splitBalancedAppend_success (compile_balancedControlFlow child) expanded
  have checked := evaluate_eq_of_eval CryptoOracle.model_refines verifyRun
  cases middle with
  | nil => simp [evaluate] at checked
  | cons top rest =>
      simp only [evaluate] at checked
      cases truth : castToBool top with
      | false => simp [truth] at checked
      | true =>
          simp only [truth, ↓reduceIte, ExecResult.success.injEq] at checked
          obtain ⟨rfl, rfl⟩ := checked
          exact ⟨top, childRun, truth⟩

/-- A truthy `c:` wrapper exposes the K child's key/signature output and the
    successful encoded signature check, for an arbitrary child fragment. -/
theorem c_inversion
    (child : CoreFragment) {stack alt outAlt : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : Eval (compile (.c child)) stack alt flags ctx (.success [top] outAlt))
    (truth : castToBool top = true) :
    ∃ sig key,
      Eval (compile child) stack alt flags ctx (.success [key, sig] outAlt) ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key = .ok true := by
  obtain ⟨middle, middleAlt, childRun, checkRun⟩ :=
    Eval.splitBalancedAppend_success (compile_balancedControlFlow child) executed
  have checked := evaluate_eq_of_eval CryptoOracle.model_refines checkRun
  cases middle with
  | nil => simp [evaluate] at checked
  | cons key rest =>
      cases rest with
      | nil => simp [evaluate] at checked
      | cons sig rest =>
          simp only [evaluate, CryptoOracle.model] at checked
          cases sigCheck : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key with
          | error error => simp [sigCheck] at checked
          | ok valid =>
              simp only [sigCheck, ExecResult.success.injEq, List.cons.injEq] at checked
              obtain ⟨⟨topEq, rfl⟩, rfl⟩ := checked
              have validTrue : valid = true := by
                rw [← topEq, P2WSHNonMalleabilitySubcase.castToBool_boolToElement] at truth
                exact truth
              exact ⟨sig, key, childRun, validTrue ▸ sigCheck⟩

/-- MINIMALIF recovers the exact selector and the selected arbitrary branch.
    These flag/version premises are already included in a P2WSH run contract. -/
theorem or_i_inversion
    (left right : CoreFragment) {stack alt out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (minimal : flags.minimalIf = true) (version : ctx.sigVersion = .witnessV0)
    (executed : Eval (compile (.or_i left right)) stack alt flags ctx (.success out outAlt)) :
    ∃ rest,
      (stack = trueElement :: rest ∧
        Eval (compile left) rest alt flags ctx (.success out outAlt)) ∨
      (stack = falseElement :: rest ∧
        Eval (compile right) rest alt flags ctx (.success out outAlt)) := by
  have checked := evaluate_eq_of_eval CryptoOracle.model_refines executed
  have split := splitConditional_balanced_ifElse (compile_balancedControlFlow left)
    (compile_balancedControlFlow right) (suffix := [])
  simp only [List.append_nil] at split
  change evaluate CryptoOracle.model
    (.op .OP_IF :: (compile left ++ [.op .OP_ELSE] ++ compile right ++ [.op .OP_ENDIF]))
    stack alt flags ctx = .success out outAlt at checked
  cases stack with
  | nil => simp [evaluate] at checked
  | cons selector rest =>
      rw [evaluate] at checked
      by_cases canonical : minimalIfSatisfied flags ctx.sigVersion selector
      · simp only [dif_pos canonical] at checked
        rw [split] at checked
        have choices : selector = falseElement ∨ selector = trueElement := by
          have h : minimalIfArg selector = true := by
            simpa [minimalIfSatisfied, version, minimal] using canonical
          simpa [minimalIfArg, stackElementEq, Bool.or_eq_true, ByteArray.ext_iff] using h
        rcases choices with rfl | rfl
        · refine ⟨rest, Or.inr ⟨rfl, ?_⟩⟩
          apply evaluate_model_iff.mpr
          simpa [ConditionalFrame.select, selectConditionalBranches, castToBool,
            falseElement] using checked
        · refine ⟨rest, Or.inl ⟨rfl, ?_⟩⟩
          apply evaluate_model_iff.mpr
          simpa [ConditionalFrame.select, selectConditionalBranches, castToBool,
            trueElement] using checked
      · simp [canonical] at checked

/-- A successful checked signature also passed its byte-encoding checks. -/
theorem encoding_of_checkSigWithEncoding_ok
    {ecdsa schnorr : StackElement → StackElement → ByteArray → Bool}
    {flags : ScriptFlags} {ctx : TxContext} {sig pubkey : StackElement} {valid : Bool}
    (checked : checkSigWithEncoding ecdsa schnorr flags ctx sig pubkey = .ok valid) :
    checkSigEncodingFor flags ctx.sigVersion sig pubkey = .ok () := by
  cases encoded : checkSigEncodingFor flags ctx.sigVersion sig pubkey with
  | error error => simp [checkSigWithEncoding, encoded] at checked
  | ok value => cases value; rfl

/-- STRICTENC separates a nonempty public key from a DER signature. -/
theorem signature_ne_pubkey_of_strict
    {flags : ScriptFlags} {ctx : TxContext} {sig pubkey : StackElement}
    (strict : flags.strictEncoding = true) (version : ctx.sigVersion = .witnessV0)
    (encoded : checkSigEncodingFor flags ctx.sigVersion sig pubkey = .ok ()) :
    sig ≠ pubkey := by
  intro same
  subst sig
  have signatureOk : checkSignatureEncoding flags pubkey = .ok () := by
    cases checked : checkSignatureEncoding flags pubkey with
    | error error =>
        simp [checkSigEncodingFor, version, checkECDSAEncoding, checked,
          bind, Except.bind] at encoded
    | ok value => cases value; rfl
  have keyOk : checkPubKeyEncoding flags pubkey = .ok () := by
    cases checked : checkPubKeyEncoding flags pubkey with
    | error error =>
        simp [checkSigEncodingFor, version, checkECDSAEncoding, signatureOk, checked,
          bind, Except.bind] at encoded
    | ok value => cases value; rfl
  have ordinary : isCompressedOrUncompressedPubKey pubkey = true := by
    cases h : isCompressedOrUncompressedPubKey pubkey <;>
      simp_all [checkPubKeyEncoding]
  have shape : (pubkey.size = 33 ∧ (pubkey[0]! = 2 ∨ pubkey[0]! = 3)) ∨
      (pubkey.size = 65 ∧ pubkey[0]! = 4) := by
    simpa [isCompressedOrUncompressedPubKey, Bool.or_eq_true, Bool.and_eq_true] using ordinary
  have nonempty : pubkey.size ≠ 0 := by rcases shape with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have notDer : isValidSignatureEncoding pubkey = false := by
    rcases shape with ⟨size, first | first⟩ | ⟨size, first⟩ <;>
      rw [getElem!_pos pubkey 0 (by omega)] at first <;>
      simp [isValidSignatureEncoding, size, first]
  simp [checkSignatureEncoding, strict, nonempty, notDer] at signatureOk

/-- The generated `c:pk_h` witness contains the selected signature and key. -/
theorem satisfyFinal_c_pk_h {env : SatEnv} {key : PubKey} {arguments : Witness}
    (generated : satisfyFinal (.c (.pk_h key)) env = some arguments) :
    ∃ sig, env.signatureFor key = some sig ∧ arguments = [sig, key.bytes] := by
  simp only [satisfyFinal, satisfactionCandidates, keyCandidates] at generated
  cases signed : env.signatureFor key with
  | none => simp [signed] at generated
  | some sig =>
      simp only [signed, CandidateResult.usable, CandidateResult.finalWitness?] at generated
      exact ⟨sig, rfl, (Option.some.inj generated).symm⟩

/-- The existing third-party contract fixes the revealed key; STRICTENC then
    ensures the accepted signature came from the signature position. -/
theorem p2wshNonMalleability_c_pk_h
    (sane : SaneFragment .p2wsh) (key : PubKey)
    (shape : sane.checked.fragment = .c (.pk_h key))
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
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  obtain ⟨sig, pubkey, otherEq, hashEq, checked⟩ := p2wshAccepted_c_pk_h sane key shape
    bytes scriptPubKey suffix env flags ctx oracles keyPath other serialized spend run accepted
  rw [shape] at generated thirdParty
  have keyMember : key ∈ CoreFragment.keys (.c (.pk_h key)) := by simp [CoreFragment.keys]
  have keyEq : pubkey = key.bytes :=
    thirdParty.2.2.2 pubkey (by simp [otherEq]) key keyMember hashEq
  subst pubkey
  have valid := verifySigFor_of_checkSigWithEncoding_true checked
  have member : sig ∈ arguments :=
    thirdParty.2.1 sig (by simp [otherEq]) key keyMember valid
  obtain ⟨_, _, _, _, modeled, _, _, context, _⟩ := run
  have strict : flags.script.strictEncoding = true := modeled.2.2.2.2
  have version : env.txCtx.sigVersion = .witnessV0 := by rw [context]; rfl
  have distinct := signature_ne_pubkey_of_strict strict version
    (encoding_of_checkSigWithEncoding_ok checked)
  obtain ⟨sig0, _, argsEq⟩ := satisfyFinal_c_pk_h generated
  simp only [argsEq, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · rw [otherEq, same, argsEq]
  · exact (distinct same).elim

/-- A positional signature frame in execution order. The relation records
    either environment lookup or successful signature verification. -/
inductive SignatureFrame (valid : StackElement → PubKey → Prop) : Stack → List PubKey → Prop
  | nil : SignatureFrame valid [] []
  | cons {sig : StackElement} {key : PubKey} {stack : Stack} {keys : List PubKey}
      (head : valid sig key) (tail : SignatureFrame valid stack keys) :
      SignatureFrame valid (sig :: stack) (key :: keys)

/-- Every item of a positional frame has a corresponding key. -/
theorem SignatureFrame.origin {valid : StackElement → PubKey → Prop}
    {stack : Stack} {keys : List PubKey} (frame : SignatureFrame valid stack keys)
    {sig : StackElement} (member : sig ∈ stack) :
    ∃ key ∈ keys, valid sig key := by
  induction frame with
  | nil => simp at member
  | @cons headSig key stack keys head tail ih =>
      rcases List.mem_cons.mp member with same | member
      · subst sig; exact ⟨key, by simp, head⟩
      · obtain ⟨source, keyMember, valid⟩ := ih member
        exact ⟨source, List.mem_cons_of_mem key keyMember, valid⟩

/-- The existing third-party restriction pins every verified signature to
    its environment lookup whenever the revealed witness is a signature frame.
    Distinct-key exclusion prevents moving another key's signature into a slot. -/
theorem signatureFrame_lookup
    {fragment : CoreFragment} {env : SatEnv} {arguments other : Witness}
    {keys : List PubKey}
    (sound : env.Sound)
    (thirdParty : ThirdPartyWitness fragment env.txCtx arguments other)
    (keyMembers : ∀ key ∈ keys, key ∈ fragment.keys)
    (generated : SignatureFrame (fun sig key => env.signatureFor key = some sig)
      arguments.reverse keys)
    {sig : StackElement} {key : PubKey}
    (member : sig ∈ other) (keyMember : key ∈ keys)
    (valid : verifySigFor checkSig checkSchnorrSig env.txCtx sig key.bytes = true) :
    env.signatureFor key = some sig := by
  have revealed := thirdParty.2.1 sig member key (keyMembers key keyMember) valid
  obtain ⟨source, sourceMember, selected⟩ := generated.origin (by simpa using revealed)
  have sourceEq : source = key := by
    apply Classical.byContradiction
    intro different
    exact thirdParty.1 sig member key (keyMembers key keyMember) source
      (keyMembers source sourceMember) (Ne.symm different) valid (sound.signatureValid selected)
  simpa [sourceEq] using selected

/-- Pointwise lookup fixes all positions of an aligned signature frame. -/
theorem SignatureFrame.unique_of_lookup
    {env : SatEnv} {keys : List PubKey} {expected observed : Stack}
    (generated : SignatureFrame (fun sig key => env.signatureFor key = some sig) expected keys)
    (verified : SignatureFrame
      (fun sig key => verifySigFor checkSig checkSchnorrSig env.txCtx sig key.bytes = true)
      observed keys)
    (lookup : ∀ sig ∈ observed, ∀ key ∈ keys,
      verifySigFor checkSig checkSchnorrSig env.txCtx sig key.bytes = true →
        env.signatureFor key = some sig) :
    observed = expected := by
  induction generated generalizing observed with
  | nil => cases verified; rfl
  | @cons sig key expected keys selected generated ih =>
      cases verified with
      | @cons other _ _ _ valid rest =>
          have same : other = sig := Option.some.inj
            ((lookup other (by simp) key (by simp) valid).symm.trans selected)
          have tailEq := ih rest (fun item member source keyMember checked =>
            lookup item (List.mem_cons_of_mem _ member) source
              (List.mem_cons_of_mem _ keyMember) checked)
          simp [same, tailEq]

/-- Witness uniqueness for any fragment whose generated and accepted witnesses
    are aligned signature frames, using exactly the existing third-party rules. -/
theorem thirdParty_signatureFrame_unique
    {fragment : CoreFragment} {env : SatEnv} {arguments other : Witness}
    {keys : List PubKey}
    (sound : env.Sound)
    (thirdParty : ThirdPartyWitness fragment env.txCtx arguments other)
    (keyMembers : ∀ key ∈ keys, key ∈ fragment.keys)
    (generated : SignatureFrame (fun sig key => env.signatureFor key = some sig)
      arguments.reverse keys)
    (verified : SignatureFrame
      (fun sig key => verifySigFor checkSig checkSchnorrSig env.txCtx sig key.bytes = true)
      other.reverse keys) :
    other = arguments := by
  have equal := generated.unique_of_lookup verified (fun sig member key keyMember valid =>
    signatureFrame_lookup sound thirdParty keyMembers generated
      (by simpa using member) keyMember valid)
  have reversed := congrArg List.reverse equal
  simpa using reversed

/-- An arbitrary sequence of verified key checks followed by a true result. -/
def signatureChain : List PubKey → CoreFragment
  | [] => .one
  | key :: keys => .and_v (.v (.c (.pk_k key))) (signatureChain keys)

theorem signatureChain_keys (keys : List PubKey) : (signatureChain keys).keys = keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simpa [signatureChain, CoreFragment.keys] using congrArg (key :: ·) ih

/-- Successful execution of a signature chain recovers every signature slot;
    no assumptions about a generated witness are used in this inversion. -/
theorem signatureChain_inversion
    (keys : List PubKey) {stack : Stack} {top : StackElement} {alt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : evaluate CryptoOracle.model (compile (signatureChain keys)) stack [] flags ctx =
      .success [top] alt) :
    SignatureFrame (fun sig key =>
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key.bytes = .ok true)
      stack keys := by
  induction keys generalizing stack with
  | nil =>
      simp only [signatureChain, compile, compileWithKeyHash, evaluate,
        ExecResult.success.injEq, List.cons.injEq] at executed
      obtain ⟨⟨_, rfl⟩, _⟩ := executed
      exact .nil
  | cons key keys ih =>
      change evaluate CryptoOracle.model
        (.pushData key.bytes :: .op .OP_CHECKSIGVERIFY :: compile (signatureChain keys))
        stack [] flags ctx = .success [top] alt at executed
      cases stack with
      | nil => simp [evaluate] at executed
      | cons sig rest =>
          simp only [evaluate] at executed
          cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig key.bytes with
          | error error => simp [CryptoOracle.model, checked] at executed
          | ok valid =>
              cases valid with
              | false => simp [CryptoOracle.model, checked] at executed
              | true =>
                  simp only [CryptoOracle.model, checked] at executed
                  exact .cons checked (ih executed)

/-- Generated chain material is a positional frame of environment signatures. -/
theorem satisfy_signatureChain
    (keys : List PubKey) {env : SatEnv} {arguments : Witness}
    (generated : satisfy (signatureChain keys) env = some arguments) :
    SignatureFrame (fun sig key => env.signatureFor key = some sig) arguments.reverse keys := by
  induction keys generalizing arguments with
  | nil =>
      simp [signatureChain, satisfy, satisfactionCandidates, CandidateResult.usable,
        CandidateResult.usableWitness?] at generated
      subst arguments
      exact .nil
  | cons key keys ih =>
      change ((keyCandidates key [] env).sat.combine
        (satisfactionCandidates (signatureChain keys) env).sat).usableWitness? =
          some arguments at generated
      obtain ⟨first, rest, firstSelected, restSelected, combined⟩ :=
        CandidateResult.combine_usableWitness_iff.mp generated
      cases selected : env.signatureFor key with
      | none => simp [keyCandidates, selected] at firstSelected
      | some sig =>
          simp only [keyCandidates, selected, CandidateResult.usable_witness?,
            Option.some.injEq] at firstSelected
          subst first
          rw [combined, Witness.combine, List.reverse_append, List.reverse_singleton]
          exact .cons selected (ih restSelected)

/-- Mapping a positional signature frame preserves its positions. -/
theorem SignatureFrame.map {first second : StackElement → PubKey → Prop}
    {stack : Stack} {keys : List PubKey}
    (frame : SignatureFrame first stack keys)
    (implication : ∀ sig key, first sig key → second sig key) :
    SignatureFrame second stack keys := by
  induction frame with
  | nil => exact .nil
  | cons head tail ih => exact .cons (implication _ _ head) ih

/-- Non-malleability for arbitrary-length sane signature chains, with the
    unchanged compilation, run, generation and third-party premises. -/
theorem p2wshNonMalleability_signatureChain
    (sane : SaneFragment .p2wsh) (keys : List PubKey)
    (shape : sane.checked.fragment = signatureChain keys)
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
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  obtain ⟨top, alt, evaluated, _⟩ := p2wshAccepted_eval sane bytes scriptPubKey suffix
    env flags ctx oracles keyPath other serialized spend run accepted
  rw [shape] at evaluated generated thirdParty
  have observed := signatureChain_inversion keys
    (evaluate_eq_of_eval CryptoOracle.model_refines evaluated)
  have supplied := satisfy_signatureChain keys (satisfyFinal_some_satisfy generated)
  exact thirdParty_signatureFrame_unique run.2.2.2.2.2.1 thirdParty
    (by intro key member; simpa [signatureChain_keys] using member) supplied
    (observed.map fun _ _ checked => verifySigFor_of_checkSigWithEncoding_true checked)

end LeanMiniscript.Extraction.P2WSHNonMalleabilityInversion
