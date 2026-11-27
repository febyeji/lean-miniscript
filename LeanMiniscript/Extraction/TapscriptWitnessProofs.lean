import LeanMiniscript.Extraction.TapscriptAcceptanceProofs

/-!
# Tapscript witness uniqueness for single-key fragments

For sane `c:pk_k` and `c:pk_h` fragments, a third-party witness accepted by
Core equals the generated final satisfaction under the existing
`CompiledNonMalleability` premises. The proofs invert accepted execution and
the generated witness, then apply the signature and key-image clauses of
`ThirdPartyWitness`.

The general `TapscriptNonMalleability` obligation remains unproved.
-/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- A singleton initial stack is a singleton wire-order witness. -/
theorem witness_eq_singleton_of_toInitialStack {other : Witness} {x : StackElement}
    (stack : other.toInitialStack = [x]) : other = [x] := by
  have rev : other.reverse = [x] := stack
  have back : other = other.reverse.reverse := (List.reverse_reverse other).symm
  rw [rev] at back
  exact back

/-- A two-element initial stack is the reversed wire-order witness. -/
theorem witness_eq_pair_of_toInitialStack {other : Witness} {x y : StackElement}
    (stack : other.toInitialStack = [x, y]) : other = [y, x] := by
  have rev : other.reverse = [x, y] := stack
  have back : other = other.reverse.reverse := (List.reverse_reverse other).symm
  rw [rev] at back
  exact back

/-- A successful checked signature is a valid model signature. -/
theorem verifySigFor_of_checkSigWithEncoding {flags : ScriptFlags} {txCtx : TxContext}
    {sig pubkey : StackElement}
    (sigOK : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig pubkey =
      .ok true) :
    verifySigFor checkSig checkSchnorrSig txCtx sig pubkey = true := by
  unfold checkSigWithEncoding at sigOK
  cases encoded : checkSigEncodingFor flags txCtx.sigVersion sig pubkey with
  | error error => simp [encoded] at sigOK
  | ok _ =>
      cases checked : checkedVerifySigFor checkSig checkSchnorrSig txCtx sig pubkey with
      | error error => simp [encoded, checked] at sigOK
      | ok valid =>
          simp only [encoded, checked] at sigOK
          cases valid with
          | true => simp [verifySigFor, checked]
          | false =>
              exfalso
              simp only [Bool.false_eq_true, ↓reduceIte] at sigOK
              repeat' split at sigOK
              all_goals simp at sigOK

/-- A well-encoded Schnorr signature has exactly 64 or 65 bytes. -/
theorem schnorr_size_of_encoding {sig : StackElement}
    (encoded : checkSchnorrSignatureEncoding sig = .ok ()) :
    sig.size = 64 ∨ sig.size = 65 := by
  by_cases h64 : sig.size = 64
  · exact Or.inl h64
  · by_cases h65 : sig.size = 65
    · exact Or.inr h65
    · exfalso
      simp [checkSchnorrSignatureEncoding, h64, h65, bne_iff_ne] at encoded

/-- A well-encoded Tapscript signature for a 32-byte key is empty or has
    exactly 64 or 65 bytes. -/
theorem tapscript_sig_size {flags : ScriptFlags} {sig pubkey : StackElement}
    (keySize : pubkey.size = 32)
    (encoded : checkSigEncodingFor flags .tapscript sig pubkey = .ok ()) :
    sig.size = 0 ∨ sig.size = 64 ∨ sig.size = 65 := by
  by_cases empty : sig.size = 0
  · exact Or.inl empty
  · right
    have nonempty : (sig.size != 0) = true := bne_iff_ne.mpr empty
    unfold checkSigEncodingFor at encoded
    rw [keySize] at encoded
    simp only [show ((32 : Nat) == 0) = false from rfl,
      show ((32 : Nat) != 32) = false from rfl, nonempty, Bool.false_eq_true,
      ↓reduceIte] at encoded
    exact schnorr_size_of_encoding encoded

/-- A valid signature is nonempty, so its size is 64 or 65. -/
theorem valid_sig_size {flags : ScriptFlags} {txCtx : TxContext}
    {sig pubkey : StackElement} (keySize : pubkey.size = 32)
    (version : txCtx.sigVersion = .tapscript)
    (encoded : checkSigEncodingFor flags txCtx.sigVersion sig pubkey = .ok ())
    (valid : verifySigFor checkSig checkSchnorrSig txCtx sig pubkey = true) :
    sig.size = 64 ∨ sig.size = 65 := by
  have notEmpty : sig.size ≠ 0 := by
    intro empty
    have checked : checkedVerifySigFor checkSig checkSchnorrSig txCtx sig pubkey =
        .ok false := by
      simp [checkedVerifySigFor, version, empty]
    simp [verifySigFor, checked] at valid
  rcases tapscript_sig_size keySize (by rw [version] at encoded; exact encoded) with
    size | size | size
  · exact absurd size notEmpty
  · exact Or.inl size
  · exact Or.inr size

/-- Invert a successful key check above an arbitrary stack suffix. -/
theorem c_pk_k_frame {flags : ScriptFlags} {txCtx : TxContext} {key : PubKey}
    {input rest alt finalAlt : Stack} {top : StackElement}
    (executed : Eval (compile (.c (.pk_k key))) input alt flags txCtx
      (.success (top :: rest) finalAlt)) (truth : castToBool top = true) :
    ∃ sig, input = sig :: rest ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig key.bytes = .ok true := by
  change Eval [.pushData key.bytes, .op .OP_CHECKSIG] input alt
    flags txCtx (.success (top :: rest) finalAlt) at executed
  cases executed with
  | pushData data rest initStack altStack flags ctx result inner =>
      cases inner with
      | checksig_success pubkey sig rest' script' altStack' flags' ctx' result'
          sigOK final =>
          cases final with
          | empty lastStack lastAlt lastFlags lastCtx =>
              exact ⟨sig, rfl, sigOK⟩
      | checksig_failure pubkey sig rest' script' altStack' flags' ctx' result'
          sigFalse final =>
          cases final with
          | empty lastStack lastAlt lastFlags lastCtx =>
              simp [castToBool, falseElement] at truth
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
          simp [Opcode.isUpgradeableNop] at upgradable

/-- Value inversion for the compiled `c:pk_k` script `[<key>, CHECKSIG]`:
every accepted witness is exactly one signature valid for the key. This is
the per-constructor inversion pattern the general uniqueness proof needs;
here the single signature role is the whole fragment. -/
theorem accepts_c_pk_k_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {key : PubKey} {other : Witness}
    (accepts : Accepts .tapscript (compile (.c (.pk_k key))) other flags txCtx) :
    ∃ sig, other = [sig] ∧
      verifySigFor checkSig checkSchnorrSig txCtx sig key.bytes = true := by
  obtain ⟨_, _, top, alt, executed, truth⟩ := accepts
  obtain ⟨sig, stack, checked⟩ := c_pk_k_frame executed truth
  exact ⟨sig, witness_eq_singleton_of_toInitialStack stack, verifySigFor_of_checkSigWithEncoding checked⟩

/-- The canonical satisfaction of `c:pk_k` is the single environment
signature for the key. -/
theorem satisfyFinal_c_pk_k {env : SatEnv} {key : PubKey} {arguments : Witness}
    (generated : satisfyFinal (.c (.pk_k key)) env = some arguments) :
    ∃ sig₀, env.signatureFor key = some sig₀ ∧ arguments = [sig₀] := by
  simp only [satisfyFinal, satisfactionCandidates, keyCandidates] at generated
  cases selected : env.signatureFor key with
  | none => simp [selected] at generated
  | some sig₀ =>
      simp only [selected] at generated
      exact ⟨sig₀, rfl, by
        simp only [CandidateResult.usable, CandidateResult.finalWitness?] at generated
        injection generated with witnessEq
        exact witnessEq.symm⟩

/-- Uniqueness for `c:pk_k`: a third-party witness accepted by the checked
semantics is the canonical satisfaction. `ThirdPartyWitness` clause 2 places
the single valid signature inside `arguments`; the canonical satisfaction is
the singleton environment signature. No hash-lock role exists, so no
disjointness premise is needed. -/
theorem unique_c_pk_k {env : SatEnv} {flags : ScriptFlags} {key : PubKey}
    {arguments other : Witness}
    (accepts : Accepts .tapscript (compile (.c (.pk_k key))) other flags env.txCtx)
    (generated : satisfyFinal (.c (.pk_k key)) env = some arguments)
    (thirdParty : ThirdPartyWitness (.c (.pk_k key)) env.txCtx arguments other) :
    other = arguments := by
  obtain ⟨sig, otherEq, verified⟩ := accepts_c_pk_k_inversion accepts
  obtain ⟨sig₀, selected, argumentsEq⟩ := satisfyFinal_c_pk_k generated
  obtain ⟨_cross, sigMem, _locks, _images⟩ := thirdParty
  have sigIn : sig ∈ arguments := sigMem sig (by rw [otherEq]; exact List.mem_singleton_self _)
    key (by simp [CoreFragment.keys]) verified
  rw [argumentsEq] at sigIn
  have sigEq : sig = sig₀ := List.mem_singleton.mp sigIn
  rw [otherEq, argumentsEq, sigEq]

/-- Invert a successful key check above an arbitrary stack suffix. -/
theorem c_pk_h_frame {flags : ScriptFlags} {txCtx : TxContext} {key : PubKey}
    {input rest alt finalAlt : Stack} {top : StackElement}
    (executed : Eval (compile (.c (.pk_h key))) input alt flags txCtx
      (.success (top :: rest) finalAlt)) (truth : castToBool top = true) :
    ∃ sig pubkey, input = pubkey :: sig :: rest ∧
      LeanMiniscript.Script.hash160 pubkey = LeanMiniscript.Script.hash160 key.bytes ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig pubkey = .ok true := by
  change Eval [.op .OP_DUP, .op .OP_HASH160,
    .pushData (LeanMiniscript.Script.hash160 key.bytes), .op .OP_EQUALVERIFY,
    .op .OP_CHECKSIG] input alt flags txCtx
    (.success (top :: rest) finalAlt) at executed
  cases executed with
  | dup x rest script' altStack' flags' ctx' result' inner =>
      cases inner with
      | op_hash160 x' rest2 script2 altStack2 flags2 ctx2 result2 inner =>
          cases inner with
          | pushData data rest3 initStack altStack flags ctx result inner =>
              cases inner with
              | equalverify_success a b rest4 script3 altStack3 flags3 ctx3
                  result imageEq inner =>
                  cases inner with
                  | checksig_success pubkey sig rest5 script5 altStack5 flags5
                      ctx5 result5 sigOK final =>
                      cases final with
                      | empty lastStack lastAlt lastFlags lastCtx =>
                          exact ⟨sig, x, rfl, imageEq.symm, sigOK⟩
                  | checksig_failure pubkey sig rest5 script5 altStack5 flags5
                      ctx5 result5 sigFalse final =>
                      cases final with
                      | empty lastStack lastAlt lastFlags lastCtx =>
                          simp [castToBool, falseElement] at truth
                  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
                      simp [Opcode.isUpgradeableNop] at upgradable
              | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
                  simp [Opcode.isUpgradeableNop] at upgradable
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
          simp [Opcode.isUpgradeableNop] at upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
      simp [Opcode.isUpgradeableNop] at upgradable

/-- Value inversion for the compiled `c:pk_h` script
`[DUP, HASH160, <hash160(key)>, EQUALVERIFY, CHECKSIG]`: every accepted
witness is a signature and a public key whose HASH160 matches the key image,
with a successful checked signature for that public key. -/
theorem accepts_c_pk_h_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {key : PubKey} {other : Witness}
    (accepts : Accepts .tapscript (compile (.c (.pk_h key))) other flags txCtx) :
    ∃ sig pubkey, other = [sig, pubkey] ∧
      LeanMiniscript.Script.hash160 pubkey =
        LeanMiniscript.Script.hash160 key.bytes ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig pubkey =
        .ok true := by
  obtain ⟨_, _, top, alt, executed, truth⟩ := accepts
  obtain ⟨sig, pubkey, stack, imageEq, checked⟩ := c_pk_h_frame executed truth
  exact ⟨sig, pubkey, witness_eq_pair_of_toInitialStack stack, imageEq, checked⟩

/-- The canonical satisfaction of `c:pk_h` is the environment signature
followed by the key bytes. -/
theorem satisfyFinal_c_pk_h {env : SatEnv} {key : PubKey} {arguments : Witness}
    (generated : satisfyFinal (.c (.pk_h key)) env = some arguments) :
    ∃ sig₀, env.signatureFor key = some sig₀ ∧ arguments = [sig₀, key.bytes] := by
  simp only [satisfyFinal, satisfactionCandidates, keyCandidates] at generated
  cases selected : env.signatureFor key with
  | none => simp [selected] at generated
  | some sig₀ =>
      simp only [selected] at generated
      exact ⟨sig₀, rfl, by
        simp only [CandidateResult.usable, CandidateResult.finalWitness?] at generated
        injection generated with witnessEq
        exact witnessEq.symm⟩

/-- Uniqueness for `c:pk_h`: `ThirdPartyWitness` clause 4 identifies the
public key from its HASH160 image, clause 2 places the valid signature inside
`arguments`, and the signature size excludes the 32-byte key bytes as a
signature alternative. No hash-lock role exists, so no disjointness premise
is needed. -/
theorem unique_c_pk_h {env : SatEnv} {flags : ScriptFlags} {key : PubKey}
    {arguments other : Witness} (keySize : key.bytes.size = 32)
    (accepts : Accepts .tapscript (compile (.c (.pk_h key))) other flags env.txCtx)
    (generated : satisfyFinal (.c (.pk_h key)) env = some arguments)
    (thirdParty : ThirdPartyWitness (.c (.pk_h key)) env.txCtx arguments other) :
    other = arguments := by
  obtain ⟨sig, pubkey, otherEq, imageEq, sigOK⟩ := accepts_c_pk_h_inversion accepts
  obtain ⟨sig₀, selected, argumentsEq⟩ := satisfyFinal_c_pk_h generated
  obtain ⟨_cross, sigMem, _locks, keyImage⟩ := thirdParty
  have pubkeyMem : pubkey ∈ other := by simp [otherEq]
  have keyMem : key ∈ CoreFragment.keys (.c (.pk_h key)) := by simp [CoreFragment.keys]
  have pubkeyEq : pubkey = key.bytes :=
    keyImage pubkey pubkeyMem key keyMem imageEq
  subst pubkeyEq
  have verified := verifySigFor_of_checkSigWithEncoding sigOK
  have sigIn : sig ∈ arguments := sigMem sig (by simp [otherEq]) key keyMem verified
  rw [argumentsEq] at sigIn
  have sigEq : sig = sig₀ := by
    rcases List.mem_cons.mp sigIn with first | deeper
    · exact first
    · have sigIsKey : sig = key.bytes := List.mem_singleton.mp deeper
      have version : env.txCtx.sigVersion = .tapscript := accepts.2.1
      have encoded : checkSigEncodingFor flags env.txCtx.sigVersion sig key.bytes =
          .ok () := by
        unfold checkSigWithEncoding at sigOK
        cases enc : checkSigEncodingFor flags env.txCtx.sigVersion sig key.bytes with
        | error error => simp [enc] at sigOK
        | ok u => cases u; rfl
      have sizes := valid_sig_size keySize version encoded verified
      rw [sigIsKey] at sizes
      rcases sizes with size | size <;> omega
  rw [otherEq, argumentsEq, sigEq]

/-- Core acceptance of a third-party witness for `c:pk_k` forces equality
with the generated final satisfaction under the original compiled-spend
premises. -/
theorem nonMalleability_c_pk_k
    (sane : SaneFragment .tapscript) (key : PubKey)
    (fragmentEq : sane.checked.fragment = .c (.pk_k key))
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray)
    (env : SatEnv) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (thirdParty : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  have accepts := tapscript_accepts_of_coreVerifyScript sane bytes scriptPubKey
    suffix env flags ctx oracles keyPath other serialized spend run accepted
  rw [fragmentEq] at accepts
  rw [fragmentEq] at generated thirdParty
  exact unique_c_pk_k accepts generated thirdParty

/-- End-to-end `c:pk_h` instance of the original obligation, with the
32-byte key size supplied by sane well-formedness. -/
theorem nonMalleability_c_pk_h
    (sane : SaneFragment .tapscript) (key : PubKey)
    (fragmentEq : sane.checked.fragment = .c (.pk_h key))
    (bytes scriptPubKey : ByteArray) (suffix : List ByteArray)
    (env : SatEnv) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments other : Witness)
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (thirdParty : ThirdPartyWitness sane.checked.fragment env.txCtx arguments other)
    (accepted : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (other ++ suffix) = .ok ()) :
    other = arguments := by
  have accepts := tapscript_accepts_of_coreVerifyScript sane bytes scriptPubKey
    suffix env flags ctx oracles keyPath other serialized spend run accepted
  rw [fragmentEq] at accepts
  rw [fragmentEq] at generated thirdParty
  have wellFormed := sane.checked.wellFormed
  rw [fragmentEq] at wellFormed
  have keySize : key.bytes.size = 32 := by
    change validResolvedPubKey .tapscript key at wellFormed
    simpa [validResolvedPubKey, PubKey.size] using wellFormed
  exact unique_c_pk_h keySize accepts generated thirdParty

end LeanMiniscript.Extraction.TapscriptWitness
