import LeanMiniscript.Miniscript.SatisfactionPossibilityProofs
import LeanMiniscript.Miniscript.TypeInferenceProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.ExecutionDecomposition
import LeanMiniscript.Miniscript.TypeSoundnessProofs.SuccessShapes
import LeanMiniscript.Extraction.TapscriptThresholdRecovery
import LeanMiniscript.Extraction.TapscriptMultiAWitnessProofs

/-! Recover the signature slots of key checks and multi_a executions with a stack suffix. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

namespace LeanMiniscript.Extraction.TapscriptRecovery.MultiA

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction

export _root_.LeanMiniscript.Extraction.TapscriptWitness (verifySigFor_of_checkSigWithEncoding)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (eq_falseElement_of_checkSigWithEncoding_false)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (nonempty_of_checkSigWithEncoding_true)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (sigSlot)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (validCount)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (slots_all_of_forall)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (checkSigAddTail_slots)

private theorem compileCheckSigAddTail_balanced (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append (.append (.atom (by simp [NonConditional]))
        (.atom (by simp [NonConditional]))) ih

export _root_.LeanMiniscript.Extraction.TapscriptWitness (multiA_slots_of_trace)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (mem_zip_getElem)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (multiA_eq_of_subset_count)

end LeanMiniscript.Extraction.TapscriptRecovery.MultiA

namespace LeanMiniscript.Extraction.TapscriptRecovery.Frames

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction MultiA

theorem noLegacyMulti_tapscript (k : Nat) (keys : List PubKey) :
    ¬ (CoreFragment.multi k keys).WellFormed .tapscript := by
  intro wellFormed
  exact wellFormed.1

export _root_.LeanMiniscript.Extraction.TapscriptWitness (witness_eq_singleton_of_toInitialStack)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (witness_eq_pair_of_toInitialStack)

theorem accepts_c_pk_k_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {key : PubKey} {input rest : Stack} {top : StackElement}
    (run : Eval [.pushData key.bytes, .op .OP_CHECKSIG] input []
      flags txCtx (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ sig, input = sig :: rest ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig key.bytes =
        .ok true := by
  exact TapscriptWitness.c_pk_k_frame run truth

theorem satisfy_c_pk_k {env : SatEnv} {key : PubKey} {arguments : Witness}
    (canonical : satisfy (.c (.pk_k key)) env = some arguments) :
    ∃ sig₀, env.signatureFor key = some sig₀ ∧ arguments = [sig₀] := by
  simp only [satisfy, satisfactionCandidates, keyCandidates] at canonical
  cases selected : env.signatureFor key with
  | none => simp [selected] at canonical
  | some sig₀ =>
      simp only [selected] at canonical
      exact ⟨sig₀, rfl, by
        simp only [CandidateResult.usable, CandidateResult.usableWitness?] at canonical
        injection canonical with witnessEq
        exact witnessEq.symm⟩

theorem accepts_c_pk_h_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {key : PubKey} {input rest : Stack} {top : StackElement}
    (run : Eval [.op .OP_DUP, .op .OP_HASH160,
      .pushData (LeanMiniscript.Script.hash160 key.bytes), .op .OP_EQUALVERIFY,
      .op .OP_CHECKSIG] input [] flags txCtx
      (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ sig pubkey, input = pubkey :: sig :: rest ∧
      LeanMiniscript.Script.hash160 pubkey =
        LeanMiniscript.Script.hash160 key.bytes ∧
      checkSigWithEncoding checkSig checkSchnorrSig flags txCtx sig pubkey =
        .ok true := by
  exact TapscriptWitness.c_pk_h_frame run truth

theorem satisfy_c_pk_h {env : SatEnv} {key : PubKey} {arguments : Witness}
    (canonical : satisfy (.c (.pk_h key)) env = some arguments) :
    ∃ sig₀, env.signatureFor key = some sig₀ ∧ arguments = [sig₀, key.bytes] := by
  simp only [satisfy, satisfactionCandidates, keyCandidates] at canonical
  cases selected : env.signatureFor key with
  | none => simp [selected] at canonical
  | some sig₀ =>
      simp only [selected] at canonical
      exact ⟨sig₀, rfl, by
        simp only [CandidateResult.usable, CandidateResult.usableWitness?] at canonical
        injection canonical with witnessEq
        exact witnessEq.symm⟩

theorem accepts_sha256_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {h : Hash256} {input rest : Stack} {top : StackElement}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_SHA256,
      .pushData h.bytes, .op .OP_EQUAL] input [] flags txCtx
      (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ preimage, input = preimage :: rest ∧
      (HashLock.sha256 h).Matches preimage := by
  exact _root_.LeanMiniscript.Extraction.TapscriptWitness.hashLock_frame (lock := .sha256 h) bounded run truth

theorem accepts_hash160_inversion {flags : ScriptFlags} {txCtx : TxContext}
    {h : Hash160} {input rest : Stack} {top : StackElement}
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY, .op .OP_HASH160,
      .pushData h.bytes, .op .OP_EQUAL] input [] flags txCtx
      (.success (top :: rest) []))
    (truth : castToBool top = true) :
    ∃ preimage, input = preimage :: rest ∧
      (HashLock.hash160 h).Matches preimage := by
  exact _root_.LeanMiniscript.Extraction.TapscriptWitness.hashLock_frame (lock := .hash160 h) bounded run truth

theorem satisfy_multiA {env : SatEnv} (sound : env.Sound)
    {k : Nat} {keys : List PubKey} {arguments : Witness}
    (canonical : satisfy (.multi_a k keys) env = some arguments) :
    ∃ slots, arguments.reverse = slots ∧ slots.length = keys.length ∧
      (∀ slot ∈ List.zip slots keys,
        slot.1 = falseElement ∨ env.signatureFor slot.2 = some slot.1) ∧
      (slots.filter (· ≠ falseElement)).length = k := by
  simp only [satisfy, satisfactionCandidates, multiACandidates] at canonical
  by_cases guard : candidateThresholdValid k keys.length
  · simp only [guard, ↓reduceIte] at canonical
    obtain ⟨frames, trace⟩ :=
      CandidatePair.selectExactly_choiceTrace canonical
    exact MultiA.multiA_slots_of_trace sound trace
  · simp only [guard, ↓reduceIte] at canonical
    cases canonical

end LeanMiniscript.Extraction.TapscriptRecovery.Frames

namespace LeanMiniscript.Extraction.TapscriptRecovery.MultiA

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction

private theorem multiA_finish_frame
    {k : Nat} {firstKey : PubKey} {keys : List PubKey}
    {flags : ScriptFlags} {txCtx : TxContext} {input rest altStack : Stack}
    {sig top : StackElement} {finalAlt : Stack}
    {headCount : Nat} {rest' : Stack}
    (version : txCtx.sigVersion = .tapscript)
    (threshold : validThreshold k (keys.length + 1))
    (keyBound : keys.length + 1 ≤ MAX_PUBKEYS_PER_MULTI_A)
    (stackEq : input = sig :: rest')
    (headSlot : sigSlot flags txCtx sig firstKey)
    (headVC : (if sig = falseElement then 0 else 1) = headCount)
    (truth : castToBool top = true)
    (inner2 : Eval (compileCheckSigAddTail keys ++ [.pushNum ↑k, .op .OP_NUMEQUAL])
      (scriptNat headCount :: rest') altStack flags txCtx (.success (top :: rest) finalAlt))
    (maxBound : MAX_PUBKEYS_PER_MULTI_A < maxArithmeticScriptNatExclusive := by
      decide) :
    ∃ sigs, input = sigs ++ rest ∧ sigs.length = keys.length + 1 ∧
      (∀ slot ∈ List.zip sigs (firstKey :: keys), sigSlot flags txCtx slot.1 slot.2) ∧
      (sigs.filter (· ≠ falseElement)).length = k := by
  obtain ⟨thresholdLow, thresholdHigh⟩ := threshold
  have headBound : headCount ≤ 1 := by
    rw [← headVC]
    by_cases empty : sig = falseElement <;> simp [empty]
  obtain ⟨mid, midAlt, tailRun, finalRun⟩ :=
    LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success
      (compileCheckSigAddTail_balanced keys) inner2
  obtain ⟨tailArgs, tailRest, restEq, finalEq, lengthEq, slots⟩ :=
    checkSigAddTail_slots version (by omega) tailRun
  rw [finalEq] at finalRun
  cases finalRun with
  | pushNum n rest0 script0 altStack0 flags0 ctx0 result0 inner3 =>
      cases inner3 with
      | numequal aBytes bBytes a b rest2 script2 altStack2 flags2 ctx2 result2
          decodePair inner4 =>
          cases inner4 with
          | empty lastStack lastAlt lastFlags lastCtx =>
              have vcLe : validCount tailArgs ≤ tailArgs.length :=
                List.length_filter_le _ _
              have decodeBelow : decodeScriptNum
                  (scriptNat (headCount + validCount tailArgs)) flags.minimalData
                  maxArithmeticScriptNumBytes =
                  .ok ((headCount + validCount tailArgs : Nat) : Int) :=
                decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
              have decodeTop : decodeScriptNum (scriptNum (↑k : Int))
                  flags.minimalData maxArithmeticScriptNumBytes =
                  .ok (k : Int) :=
                decodeScriptNum_scriptNat_of_lt (by omega) flags.minimalData
              unfold decodeBinaryScriptNums at decodePair
              simp only [decodeBelow, decodeTop, bind, Except.bind, pure,
                Except.pure] at decodePair
              cases decodePair
              have eqTrue : ((k : Int) == ((headCount + validCount tailArgs : Nat) : Int)) =
                  true := by
                cases cmp : ((k : Int) == ((headCount + validCount tailArgs : Nat) : Int)) with
                | true => rfl
                | false =>
                    rw [boolToElement, cmp] at truth
                    simp [castToBool, falseElement] at truth
              have kEq : k = headCount + validCount tailArgs := by
                have eqInt : (k : Int) = (headCount + validCount tailArgs : Int) :=
                  beq_iff_eq.mp eqTrue
                omega
              refine ⟨sig :: tailArgs, ?_, ?_, ?_, ?_⟩
              · rw [stackEq, restEq]
                simp
              · simp [lengthEq]
              · intro slot member
                simp only [List.zip_cons_cons, List.mem_cons] at member
                rcases member with head | tail
                · rw [head]
                  exact headSlot
                · exact slots slot tail
              · have vcTotal : validCount (sig :: tailArgs) =
                    headCount + validCount tailArgs := by
                  rw [← headVC]
                  by_cases empty : sig = falseElement
                  · rw [empty]
                    simp only [validCount]
                    rw [List.filter_cons_of_neg (a := falseElement) (by decide)]
                    simp
                  · simp only [validCount]
                    rw [List.filter_cons_of_pos (a := sig) (by simp [empty])]
                    simp [empty, Nat.add_comm]
                show validCount (sig :: tailArgs) = k
                rw [vcTotal, ← kEq]
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
          simp [Opcode.isUpgradeableNop] at upgradable

theorem acceptsMultiAFrameInversion
    (k : Nat) (keys : List PubKey)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (flags : ScriptFlags) (txCtx : TxContext)
    {input rest altStack finalAlt : Stack} {top : StackElement}
    (version : txCtx.sigVersion = .tapscript)
    (executed : Eval (compile (.multi_a k keys)) input altStack flags txCtx
      (.success (top :: rest) finalAlt))
    (truth : castToBool top = true) :
    ∃ sigs, input = sigs ++ rest ∧ sigs.length = keys.length ∧
      (∀ slot ∈ List.zip sigs keys, sigSlot flags txCtx slot.1 slot.2) ∧
      (sigs.filter (· ≠ falseElement)).length = k := by
  have sigVersion : txCtx.sigVersion = .tapscript := version
  generalize stackEq : input = stack at executed
  cases keys with
  | nil =>
      obtain ⟨one, zero⟩ := threshold
      simp only [List.length_nil] at zero
      omega
  | cons firstKey keys =>
      have scriptEq : compile (.multi_a k (firstKey :: keys)) =
          ([.pushData firstKey.bytes, .op .OP_CHECKSIG] ++
            compileCheckSigAddTail keys) ++ [.pushNum ↑k, .op .OP_NUMEQUAL] := by
        simp [compile, compileWithKeyHash, compileCheckSigAdd]
      rw [scriptEq] at executed
      cases executed with
      | pushData data rest initStack altStack flags ctx result inner =>
          cases inner with
          | checksig_success pubkey sig rest' script' altStack' flags' ctx'
              result' sigOK inner2 =>
              have accOne : (trueElement : StackElement) = scriptNat 1 := rfl
              rw [accOne] at inner2
              rw [← stackEq]
              exact multiA_finish_frame sigVersion threshold keyCount stackEq
                (Or.inr sigOK)
                (by simp [nonempty_of_checkSigWithEncoding_true sigVersion sigOK])
                truth inner2
          | checksig_failure pubkey sig rest' script' altStack' flags' ctx'
              result' sigFalse inner2 =>
              have accZero : (falseElement : StackElement) = scriptNat 0 := rfl
              rw [accZero] at inner2
              rw [← stackEq]
              exact multiA_finish_frame sigVersion threshold keyCount stackEq
                (Or.inl (eq_falseElement_of_checkSigWithEncoding_false sigVersion
                  sigFalse))
                (by simp [eq_falseElement_of_checkSigWithEncoding_false sigVersion
                  sigFalse])
                truth inner2
          | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ =>
              simp [Opcode.isUpgradeableNop] at upgradable

end LeanMiniscript.Extraction.TapscriptRecovery.MultiA

namespace LeanMiniscript.Extraction.TapscriptRecovery.Frames

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction MultiA

theorem unique_multi_a_frame {env : SatEnv} {flags : ScriptFlags}
    {k : Nat} {keys : List PubKey} {arguments other : Witness}
    {top : StackElement} {rest : Stack}
    (sound : env.Sound)
    (noDup : keys.Nodup)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A)
    (version : env.txCtx.sigVersion = .tapscript)
    (run : Eval (compile (.multi_a k keys)) (other.toInitialStack ++ rest) []
      flags env.txCtx (.success (top :: rest) []))
    (truth : castToBool top = true)
    (generated : satisfy (.multi_a k keys) env = some arguments)
    (thirdParty : ThirdPartyWitness (.multi_a k keys) env.txCtx arguments other) :
    other = arguments := by
  obtain ⟨sigsO, inputEq, lengthO, slotsO, countO⟩ :=
    acceptsMultiAFrameInversion k keys threshold keyCount flags env.txCtx version run truth
  have stackEq : other.toInitialStack = sigsO := List.append_cancel_right inputEq
  have allO := slots_all_of_forall slotsO
  obtain ⟨slotsC, argsRevEq, lengthC, formC, countC⟩ :=
    satisfy_multiA sound generated
  obtain ⟨noCross, sigMem, _locks, _images⟩ := thirdParty
  have argsEq : arguments = slotsC.reverse := by
    have rev := congrArg List.reverse argsRevEq
    simp only [List.reverse_reverse] at rev
    exact rev
  have lengthOC : sigsO.length = slotsC.length := by omega
  have subsetPoint : ∀ i (hi : i < sigsO.length), sigsO[i] ≠ falseElement →
      slotsC[i]'(by omega) = sigsO[i] := by
    intro i hi nonempty
    have pairMem : (sigsO[i], keys[i]'(by omega)) ∈ List.zip sigsO keys :=
      mem_zip_getElem lengthO hi
    have verified : verifySigFor checkSig checkSchnorrSig env.txCtx sigsO[i]
        (keys[i]'(by omega)).bytes = true := by
      have orTrue := (List.all_eq_true.mp allO) _ pairMem
      by_cases empty : sigsO[i] = falseElement
      · exact absurd empty nonempty
      · simp only [empty, decide_false, Bool.false_or] at orTrue
        exact orTrue
    have otherMem : sigsO[i] ∈ other := by
      have initialMem : sigsO[i] ∈ other.toInitialStack := by
        rw [stackEq]
        exact List.getElem_mem _
      exact List.mem_reverse.mp initialMem
    have keyMem : keys[i]'(by omega) ∈ CoreFragment.keys (.multi_a k keys) := by
      simp only [CoreFragment.keys]
      exact List.getElem_mem _
    have inArgs : sigsO[i] ∈ arguments := sigMem _ otherMem _ keyMem verified
    rw [argsEq] at inArgs
    have inSlotsC : sigsO[i] ∈ slotsC := List.mem_reverse.mp inArgs
    obtain ⟨j, hj, sjEq⟩ := List.getElem_of_mem inSlotsC
    have pairMemJ : (slotsC[j], keys[j]'(by omega)) ∈ List.zip slotsC keys :=
      mem_zip_getElem lengthC hj
    rcases formC _ pairMemJ with emptyC | selectedC
    · exact absurd (sjEq ▸ emptyC) nonempty
    · have validJ : verifySigFor checkSig checkSchnorrSig env.txCtx slotsC[j]
          (keys[j]'(by omega)).bytes = true :=
        sound.signatureValid selectedC
      rw [sjEq] at validJ
      by_cases ijEq : i = j
      · subst ijEq
        exact sjEq
      · exfalso
        have distinct : keys[i]'(by omega) ≠ keys[j]'(by omega) := by
          intro keyEq
          exact ijEq ((List.getElem_inj noDup).mp keyEq)
        exact noCross _ otherMem _ keyMem _
          (by simp only [CoreFragment.keys]; exact List.getElem_mem _) distinct
          verified validJ
  have slotsEq : sigsO = slotsC :=
    multiA_eq_of_subset_count lengthOC subsetPoint (by rw [countO, countC])
  have otherEq : other = sigsO.reverse := by
    have stackEq' : other.reverse = sigsO := stackEq
    have back : other = other.reverse.reverse := (List.reverse_reverse other).symm
    rw [stackEq'] at back
    exact back
  rw [otherEq, slotsEq, argsEq]

end LeanMiniscript.Extraction.TapscriptRecovery.Frames

namespace LeanMiniscript.Extraction.TapscriptRecovery.Transport

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction

export _root_.LeanMiniscript.Extraction.TapscriptWitness (Items)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (PairItems)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (items_combine)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (supports_items_combine)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (supports_items_selector)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (exact_items)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (threshold_dsat_items)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (all_items)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (satisfy_material)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (material_signature_of_size)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (successful_slot_size)

export _root_.LeanMiniscript.Extraction.TapscriptWitness (and_v_decompose)

def SignatureItems (witness : Witness) : Prop :=
  Items (fun item => item = falseElement ∨ item.size = 64 ∨ item.size = 65) witness

def SignatureFrameB (fragment : CoreFragment) : Prop :=
  ∀ (env : SatEnv) (flags : ScriptFlags) (other : Witness)
    (top : StackElement) (rest : Stack),
    env.txCtx.sigVersion = .tapscript →
    (∀ key ∈ fragment.keys, key.bytes.size = 32) →
    Eval (compile fragment) (other.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) []) →
    castToBool top = true → SignatureItems other

theorem signatureFrameB_multi_a (k : Nat) (keys : List PubKey)
    (threshold : validThreshold k keys.length)
    (keyCount : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A) : SignatureFrameB (.multi_a k keys) := by
  intro env flags other top rest version keySizes run truth
  obtain ⟨sigs, inputEq, lengthEq, slots, _count⟩ :=
    MultiA.acceptsMultiAFrameInversion k keys threshold keyCount flags env.txCtx version run truth
  have initialEq : other.toInitialStack = sigs := List.append_cancel_right inputEq
  intro item hi
  have inSigs : item ∈ sigs := by
    rw [← initialEq]
    exact List.mem_reverse.mpr hi
  obtain ⟨i, hi, equal⟩ := List.getElem_of_mem inSigs
  have slot := slots _ (MultiA.mem_zip_getElem lengthEq hi)
  change sigs[i] = falseElement ∨
    checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sigs[i]
      (keys[i]'(by omega)).bytes = .ok true at slot
  rw [equal] at slot
  rcases slot with empty | checked
  · exact Or.inl empty
  · exact Or.inr (successful_slot_size version
      (keySizes _ (List.getElem_mem _)) checked)

end LeanMiniscript.Extraction.TapscriptRecovery.Transport

namespace LeanMiniscript.Extraction.TapscriptRecovery.Active

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
  LeanMiniscript.Extraction

export _root_.LeanMiniscript.Extraction.TapscriptWitness (disclosed_signature_selected)

theorem disclosed_preimage_selected {parent : CoreFragment} {env : SatEnv}
    {arguments other : Witness} {item : StackElement} {lock : HashLock}
    (recover : LocalHashSlotRecovery parent env arguments)
    (thirdParty : ThirdPartyWitness parent env.txCtx arguments other)
    (member : item ∈ other) (lockMem : lock ∈ parent.hashLocks)
    (matched : lock.Matches item) : env.preimageFor lock = some item := by
  exact hash_slot_recovery_iff.mp recover other thirdParty item member lock lockMem matched

theorem minimal_selector {flags : ScriptFlags} {ctx : TxContext} {selector : StackElement}
    (version : ctx.sigVersion = .tapscript)
    (minimal : minimalIfSatisfied flags ctx.sigVersion selector) :
    selector = falseElement ∨ selector = trueElement := by
  have eqs : selector.data = falseElement.data ∨ selector.data = trueElement.data := by
    simpa [minimalIfSatisfied, version, minimalIfArg, stackElementEq, Bool.or_eq_true] using minimal
  rcases eqs with h | h
  · exact Or.inl (congrArg ByteArray.mk h)
  · exact Or.inr (congrArg ByteArray.mk h)

theorem ifElse_active_cases {thenBranch elseBranch : Script} {selector : StackElement}
    {rest altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (thenBalanced : BalancedControlFlow thenBranch)
    (elseBalanced : BalancedControlFlow elseBranch)
    (run : Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    (selector = trueElement ∧ Eval thenBranch rest altStack flags ctx (.success out outAlt)) ∨
    (selector = falseElement ∧ Eval elseBranch rest altStack flags ctx (.success out outAlt)) := by
  have splitEq : splitConditional
      (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
      some { branches := [thenBranch, elseBranch], after := [] } := by
    simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced (suffix := [])
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case if_execute =>
      rename_i frame split minimal selected
      cases resultEq
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) = some frame at split
      rw [splitEq] at split
      cases split
      rcases minimal_selector version minimal with rfl | rfl
      · right
        exact ⟨rfl, by simpa [ConditionalFrame.select, selectConditionalBranches,
          castToBool, falseElement] using selected⟩
      · left
        exact ⟨rfl, by simpa [ConditionalFrame.select, selectConditionalBranches,
          castToBool, trueElement] using selected⟩
  case if_unbalanced =>
      rename_i selectedResult split minimal selected
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) = none at split
      rw [splitEq] at split
      contradiction
  all_goals cases resultEq

theorem and_v_malleability_children {X Y : CoreFragment} {mods : MalleabilityModifiers}
    (mal : HasMalleability .tapscript (.and_v X Y) mods)
    (nonMalleable : mods.nonMalleable = true) :
    ∃ mx my, HasMalleability .tapscript X mx ∧ HasMalleability .tapscript Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true := by
  cases mal with
  | @and_v x y mx my hx hy =>
      exact ⟨mx, my, hx, hy, (Bool.and_eq_true_iff.mp nonMalleable).1,
        (Bool.and_eq_true_iff.mp nonMalleable).2⟩

theorem or_i_malleability_children {X Y : CoreFragment} {mods : MalleabilityModifiers}
    (mal : HasMalleability .tapscript (.or_i X Y) mods)
    (nonMalleable : mods.nonMalleable = true) :
    ∃ mx my, HasMalleability .tapscript X mx ∧ HasMalleability .tapscript Y my ∧
      mx.nonMalleable = true ∧ my.nonMalleable = true ∧ (mx.s = true ∨ my.s = true) := by
  cases mal with
  | @or_i x y mx my hx hy =>
      have both := Bool.and_eq_true_iff.mp nonMalleable
      exact ⟨mx, my, hx, hy, (Bool.and_eq_true_iff.mp both.1).1,
        (Bool.and_eq_true_iff.mp both.1).2, Bool.or_eq_true_iff.mp both.2⟩

end LeanMiniscript.Extraction.TapscriptRecovery.Active
