import LeanMiniscript.Extraction.P2WSHRecovery.SignatureMaterial

/-! The two lookup directions on a generated hash-and-key satisfaction. -/

namespace LeanMiniscript.Extraction.P2WSHRecovery

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- The hash guard executes before the signature check. -/
def guardedKey (lock : HashLock) (key : PubKey) : CoreFragment :=
  .and_v (.v lock.fragment) (.c (.pk_k key))

private theorem guardedKey_keys (lock : HashLock) (key : PubKey) :
    (guardedKey lock key).keys = [key] := by cases lock <;> rfl

private theorem guardedKey_locks (lock : HashLock) (key : PubKey) :
    (guardedKey lock key).hashLocks = [lock] := by cases lock <;> rfl

/-- Serialization places the signature below the hash guard's preimage on the initial stack. -/
theorem guardedKey_generated {env : SatEnv} {key : PubKey} {lock : HashLock}
    {sig preimage : StackElement} (signed : env.signatureFor key = some sig)
    (opened : env.preimageFor lock = some preimage) :
    satisfyFinal (guardedKey lock key) env = some [sig, preimage] := by
  cases lock <;>
    simp [guardedKey, satisfyFinal, HashLock.fragment, satisfactionCandidates, keyCandidates,
      hashCandidates, signed, opened] <;> rfl

/-- For one key, a published item satisfies the third-party clauses exactly when
    its HASH160 identifies the key whenever the two key hashes agree. -/
private theorem eligible_published {env : SatEnv} {lock : HashLock} {key : PubKey}
    {arguments : Witness} {item : StackElement} (mem : item ∈ arguments) :
    ThirdPartyWitness (guardedKey lock key) env.txCtx arguments [item] ↔
      (Script.hash160 item = Script.hash160 key.bytes → item = key.bytes) := by
  simp [ThirdPartyWitness, guardedKey_keys, guardedKey_locks, mem]

/-- Hash recovery compares the published signature to the hash lookup.
    Signature agreement compares the published preimage to the signature lookup. -/
theorem guardedKey_lookup_conditions {env : SatEnv} {flags : ScriptFlags}
    {lock : HashLock} {key : PubKey} {sig preimage : StackElement}
    (signed : env.signatureFor key = some sig) (opened : env.preimageFor lock = some preimage) :
    (LocalHashSlotRecovery (guardedKey lock key) env [sig, preimage] ↔
      (Script.hash160 sig = Script.hash160 key.bytes → sig = key.bytes) →
        lock.Matches sig → sig = preimage) ∧
    (PublishedPreimageSignatureAgreement (guardedKey lock key) env flags [sig, preimage] ↔
      (Script.hash160 preimage = Script.hash160 key.bytes → preimage = key.bytes) →
        checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx preimage key.bytes = .ok true →
        sig = preimage) := by
  have eligible (item : StackElement) (mem : item ∈ [sig, preimage]) :=
    @eligible_published env lock key [sig, preimage] item mem
  constructor
  · constructor
    · intro recover image matched
      have eq := recover sig (by simp) ((eligible sig (by simp)).mpr image) lock
        (by simp [guardedKey_locks]) matched
      exact Option.some.inj (eq.symm.trans opened)
    · intro consistent item member third target present matched
      have eq : target = lock := by simpa [guardedKey_locks] using present
      subst target
      rcases List.mem_cons.mp member with rfl | hp
      · rw [consistent ((eligible item (by simp)).mp third) matched]
        exact opened
      · exact List.mem_singleton.mp hp ▸ opened
  · constructor
    · intro agree image checked
      have eq := agree preimage (by simp) ((eligible preimage (by simp)).mpr image)
        ⟨lock, by simp [guardedKey_locks], opened⟩ key (by simp [guardedKey_keys]) checked
      exact Option.some.inj (signed.symm.trans eq)
    · rintro consistent item mem third ⟨target, present, lookup⟩ k hk checked
      have lockEq : target = lock := by simpa [guardedKey_locks] using present
      have keyEq : k = key := by simpa [guardedKey_keys] using hk
      subst target k
      obtain rfl := Option.some.inj (lookup.symm.trans opened)
      exact (consistent ((eligible item mem).mp third) checked) ▸ signed

/-- A matching preimage has size 32. When the selected signature has another size,
    hash recovery holds on the generated arguments. The remaining condition for
    signature recovery is the checked, eligible preimage's signature lookup. -/
theorem guardedKey_signature_obstruction {env : SatEnv} {flags : ScriptFlags}
    {lock : HashLock} {key : PubKey} {sig preimage : StackElement}
    (sound : env.Sound) (signed : env.signatureFor key = some sig)
    (opened : env.preimageFor lock = some preimage) (size : sig.size ≠ 32)
    (image : Script.hash160 preimage ≠ Script.hash160 key.bytes)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx preimage key.bytes =
      .ok true) :
    LocalHashSlotRecovery (guardedKey lock key) env [sig, preimage] ∧
      ¬ PublishedPreimageSignatureAgreement (guardedKey lock key) env flags [sig, preimage] := by
  obtain ⟨hashIff, sigIff⟩ := guardedKey_lookup_conditions (flags := flags) signed opened
  refine ⟨hashIff.mpr (fun _ matched => (size matched.1).elim), ?_⟩
  intro agrees
  have eq := sigIff.mp agrees (fun h => (image h).elim) checked
  exact size (eq ▸ (sound.preimageMatches opened).1)

/-- For two independently supplied signing environments on the same spend, Core witness
    uniqueness forces their signature lookups to agree whenever the second satisfaction
    uses eligible published material. The first satisfaction already has hash recovery. -/
theorem guardedKey_core_lookup_constraint (sane : SaneFragment .p2wsh)
    {lock : HashLock} {key : PubKey} (shape : sane.checked.fragment = guardedKey lock key)
    {bytes scriptPubKey : ByteArray} {suffix : List ByteArray} {flags : CoreVerificationFlags}
    {ctx : TxContext} {oracles : SignatureVersion → ByteArray → CryptoOracle}
    (keyPath : CoreKeyPathChecker) {env comparison : SatEnv} {arguments observed : Witness}
    {sig compared preimage : StackElement}
    (serialized : CompiledScriptBytes sane.checked.fragment bytes)
    (spend : CompiledScriptSpend .p2wsh bytes scriptPubKey suffix)
    (run : CompiledScriptRun .p2wsh comparison flags ctx oracles bytes)
    (generated : satisfyFinal sane.checked.fragment env = some arguments)
    (observedGenerated : satisfyFinal sane.checked.fragment comparison = some observed)
    (signed : env.signatureFor key = some sig) (second : comparison.signatureFor key = some compared)
    (opened : env.preimageFor lock = some preimage)
    (samePreimage : comparison.preimageFor lock = some preimage)
    (size : sig.size ≠ 32) (published : ∀ item ∈ observed, item ∈ arguments)
    (keyImage : ∀ item ∈ observed, Script.hash160 item = Script.hash160 key.bytes → item = key.bytes) :
    LocalHashSlotRecovery sane.checked.fragment env arguments ∧
      ((∀ other, ThirdPartyWitness sane.checked.fragment env.txCtx arguments other →
        coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey (other ++ suffix) =
          .ok () → other = arguments) → sig = compared) := by
  have accepted := p2wshSatisfaction sane bytes scriptPubKey suffix comparison flags ctx oracles
    keyPath observed serialized spend run observedGenerated
  rw [shape, guardedKey_generated signed opened] at generated
  rw [shape, guardedKey_generated second samePreimage] at observedGenerated
  have argsEq := Option.some.inj generated
  have observedEq := Option.some.inj observedGenerated
  rw [shape]
  have hashIff := (guardedKey_lookup_conditions (flags := flags.script) signed opened).1
  refine ⟨argsEq ▸ hashIff.mpr (fun _ matched => (size matched.1).elim), ?_⟩
  intro unique
  have eligible : ThirdPartyWitness (guardedKey lock key) env.txCtx arguments observed := by
    refine ⟨?_, fun item mem _ _ _ => published item mem,
      fun item mem _ _ _ => published item mem, ?_⟩
    · simp [guardedKey_keys]
    · simpa [guardedKey_keys] using keyImage
  exact (List.cons.inj (argsEq.trans ((unique _ eligible accepted).symm.trans observedEq.symm))).1

/-- With a non-DER preimage and a signature of length other than 32, both
    local premises hold on the generated mixed witness. -/
theorem guardedKey_separated {env : SatEnv} {flags : ScriptFlags} {lock : HashLock}
    {key : PubKey} {sig preimage : StackElement}
    (signed : env.signatureFor key = some sig) (opened : env.preimageFor lock = some preimage)
    (size : sig.size ≠ 32) (matched : lock.Matches preimage)
    (nonDER : isValidSignatureEncoding preimage = false)
    (version : env.txCtx.sigVersion = .witnessV0) (strict : flags.strictEncoding = true) :
    satisfyFinal (guardedKey lock key) env = some [sig, preimage] ∧
    LocalHashSlotRecovery (guardedKey lock key) env [sig, preimage] ∧
    LocalPreimageSignatureDisjoint (guardedKey lock key) env flags [sig, preimage] := by
  refine ⟨guardedKey_generated signed opened, (guardedKey_lookup_conditions
    (flags := flags) signed opened).1.mpr (fun _ h => (size h.1).elim), ?_⟩
  rintro item _ _ ⟨target, ht, lookup⟩ k _ checked
  obtain rfl : target = lock := by simpa [guardedKey_locks] using ht
  obtain rfl := Option.some.inj (lookup.symm.trans opened)
  have encoded := P2WSHNonMalleabilityInversion.encoding_of_checkSigWithEncoding_ok checked
  simp [version, checkSigEncodingFor, checkECDSAEncoding, checkSignatureEncoding,
    matched.1, strict, nonDER, bind, Except.bind] at encoded

/-- An explicit 32-byte opening supplies a generated witness with both local
    premises for a fragment containing a key and a hash lock. -/
theorem exists_guardedKey_separated (key : PubKey) (ctx : TxContext) (flags : ScriptFlags)
    (version : ctx.sigVersion = .witnessV0) (strict : flags.strictEncoding = true) :
    ∃ (env : SatEnv) (lock : HashLock) (sig preimage : StackElement),
      env.txCtx = ctx ∧ lock.Matches preimage ∧ env.preimageFor lock = some preimage ∧
      satisfyFinal (guardedKey lock key) env = some [sig, preimage] ∧
      LocalHashSlotRecovery (guardedKey lock key) env [sig, preimage] ∧
      LocalPreimageSignatureDisjoint (guardedKey lock key) env flags [sig, preimage] := by
  let p : StackElement := ⟨Array.replicate 32 0⟩
  let lock : HashLock := .sha256 ⟨Script.sha256 p⟩
  let sig : StackElement := ⟨#[0x30, 6, 2, 1, 1, 2, 1, 1, 1]⟩
  let env : SatEnv := ⟨fun _ => some sig, fun _ => some p, fun _ => falseElement, ctx⟩
  have matched : lock.Matches p := ⟨rfl, rfl⟩
  exact ⟨env, lock, sig, p, rfl, matched, rfl, guardedKey_separated
    (env := env) (key := key) (sig := sig) rfl rfl (by decide) matched (by decide) version strict⟩

end LeanMiniscript.Extraction.P2WSHRecovery
