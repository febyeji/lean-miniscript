import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Wrappers

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: multisignature candidates

Candidate composition for Tapscript `multi_a` and legacy `multi`.
-/

/-! ## Tapscript multisignature candidate composition -/

/-- One selected `multi_a` key slot. The witness block is exactly one
    signature element, and its Boolean choice agrees with the encoded signature
    check used by CHECKSIG or CHECKSIGADD. -/
structure MultiASlot (flags : ScriptFlags) (txCtx : TxContext)
    (key : PubKey) (truth : Bool) (frame : Witness)
    (signature : StackElement) : Prop where
  frame_eq : frame = [signature]
  checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
    signature key.bytes = .ok truth
  bounded : signature.size ≤ maxScriptElementSize

/-- Source-order selected key slots for `multi_a`. Serialized child frames stay
    separate until the exact-count trace supplies their combined witness. -/
inductive MultiASlots (flags : ScriptFlags) (txCtx : TxContext) :
    List PubKey → List Bool → List Witness → Stack → Prop where
  | nil : MultiASlots flags txCtx [] [] [] []
  | cons {key : PubKey} {truth : Bool} {frame : Witness}
      {signature : StackElement} {keys : List PubKey} {truths : List Bool}
      {frames : List Witness} {signatures : Stack}
      (head : MultiASlot flags txCtx key truth frame signature)
      (tail : MultiASlots flags txCtx keys truths frames signatures) :
      MultiASlots flags txCtx (key :: keys) (truth :: truths)
        (frame :: frames) (signature :: signatures)

namespace MultiASlots

/-- Append one key slot while preserving source execution order. -/
theorem snoc {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack} {key : PubKey} {truth : Bool} {frame : Witness}
    {signature : StackElement}
    (prior : MultiASlots flags txCtx keys truths frames signatures)
    (last : MultiASlot flags txCtx key truth frame signature) :
    MultiASlots flags txCtx (keys ++ [key]) (truths ++ [truth])
      (frames ++ [frame]) (signatures ++ [signature]) := by
  induction prior with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

/-- The selected one-item frames flatten to source-order runtime signatures. -/
theorem framesShape {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures) :
    (frames.map Witness.toInitialStack).flatten = signatures := by
  induction slots with
  | nil => rfl
  | cons head tail ih => simp [head.frame_eq, ih, Witness.toInitialStack]

/-- Every selected `multi_a` witness frame respects the Script element limit. -/
theorem framesBounded {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures) :
    ∀ frame ∈ frames, frame.ItemsBounded := by
  induction slots with
  | nil => simp
  | cons head tail ih =>
      intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simpa [head.frame_eq] using
          (Witness.ItemsBounded.singleton.mpr head.bounded)
      · exact ih frame member

end MultiASlots

private theorem choiceFrames_nil_inv
    {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames [] truths frames) :
    truths = [] ∧ frames = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at choices
  cases choices with
  | nil => exact ⟨rfl, rfl⟩
  | snocSat prior selected => simp at pairsEq
  | snocDsat prior selected => simp at pairsEq

private theorem choiceFrames_snoc_inv
    {pairs : List CandidatePair} {pair : CandidatePair}
    {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames (pairs ++ [pair]) truths frames) :
    ∃ priorTruths priorFrames truth frame,
      truths = priorTruths ++ [truth] ∧
      frames = priorFrames ++ [frame] ∧
      CandidatePair.ChoiceFrames pairs priorTruths priorFrames ∧
      ((truth = true ∧ pair.sat.usableWitness? = some frame) ∨
        (truth = false ∧ pair.dsat.usableWitness? = some frame)) := by
  generalize pairsEq : pairs ++ [pair] = allPairs at choices
  cases choices with
  | nil => simp at pairsEq
  | @snocSat otherPairs otherTruths otherFrames otherPair frame prior selected =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherTruths, otherFrames, true, frame, rfl, rfl, prior,
        Or.inl ⟨rfl, selected⟩⟩
  | @snocDsat otherPairs otherTruths otherFrames otherPair frame prior selected =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherTruths, otherFrames, false, frame, rfl, rfl, prior,
        Or.inr ⟨rfl, selected⟩⟩

private theorem listSnocInductionGenerated {α : Type}
    {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ (items : List α) (item : α),
      motive items → motive (items ++ [item])) :
    ∀ items, motive items := by
  intro items
  have reversed : motive items.reverse.reverse := by
    have aux : ∀ reversedItems : List α, motive reversedItems.reverse := by
      intro reversedItems
      induction reversedItems with
      | nil => simpa using nil
      | cons item reversedItems ih =>
          simpa using snoc reversedItems.reverse item ih
    exact aux items.reverse
  simpa using reversed

private theorem allKeysValid_append
    {scriptCtx : ScriptContext} {first second : List PubKey} :
    CoreFragment.allKeysValid scriptCtx (first ++ second) ↔
      CoreFragment.allKeysValid scriptCtx first ∧
        CoreFragment.allKeysValid scriptCtx second := by
  induction first with
  | nil => simp [CoreFragment.allKeysValid]
  | cons key keys ih =>
      simp [CoreFragment.allKeysValid, ih, and_assoc]

private theorem allKeysValid_of_mem
    {scriptCtx : ScriptContext} {keys : List PubKey}
    (valid : CoreFragment.allKeysValid scriptCtx keys)
    {key : PubKey} (member : key ∈ keys) :
    validResolvedPubKey scriptCtx key := by
  induction keys with
  | nil => simp at member
  | cons head tail ih =>
      simp only [CoreFragment.allKeysValid] at valid
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact valid.1
      · exact ih valid.2 member

/-- Convert exact-count source choices over `multiAKeyChoice` into checked,
    bounded source-order signature slots. -/
theorem CandidatePair.ChoiceFrames.toMultiASlots
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {env : SatEnv} {flags : ScriptFlags}
    (choices : CandidatePair.ChoiceFrames
      (keys.map (fun key => multiAKeyChoice key env)) truths frames)
    (validKeys : CoreFragment.allKeysValid .tapscript keys)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    ∃ signatures, MultiASlots flags env.txCtx keys truths frames signatures := by
  induction keys using listSnocInductionGenerated generalizing truths frames with
  | nil =>
      obtain ⟨rfl, rfl⟩ := choiceFrames_nil_inv choices
      exact ⟨[], .nil⟩
  | snoc keys key ih =>
      have shaped : CandidatePair.ChoiceFrames
          (keys.map (fun child => multiAKeyChoice child env) ++
            [multiAKeyChoice key env]) truths frames := by
        simpa using choices
      obtain ⟨priorTruths, priorFrames, truth, frame, rfl, rfl,
        priorChoices, selected⟩ := choiceFrames_snoc_inv shaped
      have validParts := allKeysValid_append.mp validKeys
      have keyValid : validResolvedPubKey .tapscript key := by
        simpa [CoreFragment.allKeysValid] using validParts.2
      obtain ⟨signatures, priorSlots⟩ :=
        ih priorChoices validParts.1
      rcases selected with satSelected | dsatSelected
      · obtain ⟨rfl, satSelected⟩ := satSelected
        cases signatureFor : env.signatureFor key with
        | none => simp [multiAKeyChoice, signatureFor] at satSelected
        | some signature =>
            have frameEq : frame = [signature] := by
              symm
              simpa [multiAKeyChoice, signatureFor] using satSelected
            refine ⟨signatures ++ [signature], priorSlots.snoc {
              frame_eq := frameEq
              checked := checkSigWithEncoding_true
                (encodings key signature signatureFor)
                (sound.signatureValid signatureFor)
              bounded := selectedSignature_size_le keyValid version modeled
                encodings signatureFor }⟩
      · obtain ⟨rfl, dsatSelected⟩ := dsatSelected
        have frameEq : frame = [falseElement] := by
          symm
          simpa [multiAKeyChoice] using dsatSelected
        refine ⟨signatures ++ [falseElement], priorSlots.snoc {
          frame_eq := frameEq
          checked := checkSigWithEncoding_empty
            (checkSigEncodingFor_empty_of_modeled keyValid version modeled)
            (sound.emptySignatureInvalid key)
          bounded := falseElement_size_le }⟩

/-- A safe canonical natural accumulator decodes for CHECKSIGADD in Tapscript. -/
theorem decodeCheckSigAddCount_scriptNat
    {count : Nat} {flags : ScriptFlags} {txCtx : TxContext}
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe count) :
    decodeCheckSigAddCount flags txCtx (scriptNat count) =
      .ok (Int.ofNat count) := by
  simp [decodeCheckSigAddCount, version, safe.decode flags.minimalData]

/-- The final canonical accumulator and threshold literal satisfy NUMEQUAL's
    two-operand decoder when the shared arithmetic guard holds. -/
theorem decodeBinaryScriptNums_scriptNat_self
    {count : Nat} {flags : ScriptFlags}
    (safe : ArithmeticScriptNatSafe count) :
    decodeBinaryScriptNums flags (scriptNat count) (scriptNat count) =
      .ok (Int.ofNat count, Int.ofNat count) := by
  simp [decodeBinaryScriptNums, safe.decode flags.minimalData]
  rfl

namespace MultiASlots

/-- Execute checked source-order slots as the CHECKSIGADD tail. Arithmetic
    safety of the final exact count is downward closed to every partial
    accumulator. -/
theorem checkSigAddTail
    {flags : ScriptFlags} {txCtx : TxContext} {count total : Nat}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    CheckSigAddTailExecution flags txCtx (Int.ofNat count) keys signatures
      (Int.ofNat total) := by
  induction slots generalizing count total with
  | nil =>
      simp at totalEq
      subst total
      exact .nil (Int.ofNat count)
  | @cons key truth frame signature keys truths frames signatures head tail ih =>
      refine CheckSigAddTailExecution.cons (truth := truth)
        (decodeCheckSigAddCount_scriptNat version
          (threshold_accumulator_safe safe totalEq)) head.checked ?_
      simpa using ih safe (threshold_accumulator_step totalEq)

/-- A nonempty exact-count slot list executes `multi_a`: the first key uses
    CHECKSIG, only the remaining source-order keys use CHECKSIGADD, and the
    final canonical accumulator equals the selected threshold. -/
theorem multiAExecution
    {flags : ScriptFlags} {txCtx : TxContext} {threshold : Nat}
    {firstKey : PubKey} {keys : List PubKey} {truths : List Bool}
    {frames : List Witness} {signatures : Stack}
    (slots : MultiASlots flags txCtx (firstKey :: keys) truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe threshold)
    (sumEq : (truths.map Bool.toNat).sum = threshold) :
    BExecution (.multi_a threshold (firstKey :: keys)) signatures trueElement
      flags txCtx := by
  cases slots with
  | @cons _ firstTruth _ firstSignature _ tailTruths _ tailSignatures
      firstSlot tail =>
      have tailEq : firstTruth.toNat +
          (tailTruths.map Bool.toNat).sum = threshold := by
        simpa using sumEq
      have tailExec := tail.checkSigAddTail version safe tailEq
      have decoded : decodeBinaryScriptNums flags (scriptNat threshold)
          (scriptNum (Int.ofNat threshold)) =
            .ok (Int.ofNat threshold, Int.ofNat threshold) := by
        simpa [scriptNat] using decodeBinaryScriptNums_scriptNat_self safe
      exact BExecution.multiATrue version firstSlot.checked tailExec decoded
        (by simp)

end MultiASlots

/-- Strong generated contract for the valid nonempty `multi_a` candidate row.
    Satisfaction comes from the exact-count table; dissatisfaction reuses the
    canonical all-empty signature row. -/
theorem generatedContract_multiA_valid
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (valid : candidateThresholdValid threshold (firstKey :: keys).length)
    (validKeys : CoreFragment.allKeysValid .tapscript (firstKey :: keys))
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (multiACandidates threshold (firstKey :: keys) env) .tapscript
        (.multi_a threshold (firstKey :: keys))
        ⟨.B, { d := true, u := true }⟩ flags env.txCtx := by
  have tapVersion : env.txCtx.sigVersion = .tapscript := by
    simpa [ModeledContextVersion] using version
  have typed : HasType .tapscript (.multi_a threshold (firstKey :: keys))
      ⟨.B, { d := true, u := true }⟩ :=
    .multi_a threshold (firstKey :: keys)
      (Nat.one_le_iff_ne_zero.mpr valid.1) valid.2.1
  have valid' : candidateThresholdValid threshold (keys.length + 1) := by
    simpa using valid
  refine ⟨typed, ?_, ?_⟩
  · rw [show (multiACandidates threshold (firstKey :: keys) env).sat =
      CandidatePair.selectExactly threshold
        ((firstKey :: keys).map (fun key => multiAKeyChoice key env)) by
        simp [multiACandidates, valid']]
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.selectExactly_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    obtain ⟨signatures, slots⟩ := choices.toMultiASlots validKeys version
      modeled sound encodings
    apply GeneratedContract.b
    · refine ⟨trace.itemsBounded slots.framesBounded, ?_, ?_, ?_⟩ <;> simp
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack, slots.framesShape]
      exact slots.multiAExecution tapVersion valid.2.2 sumEq
  · rw [show (multiACandidates threshold (firstKey :: keys) env).dsat =
      .usable (List.replicate (firstKey :: keys).length falseElement) false by
        simp [multiACandidates, valid']]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le]
      · simp
      · simp
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · rcases validKeys with ⟨firstValid, restValid⟩
      have firstChecked : checkSigWithEncoding checkSig checkSchnorrSig flags
          env.txCtx falseElement firstKey.bytes = .ok false :=
        checkSigWithEncoding_empty
          (checkSigEncodingFor_empty_of_modeled firstValid version modeled)
          (sound.emptySignatureInvalid firstKey)
      have tailChecked : ∀ key ∈ keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx
            falseElement key.bytes = .ok false := by
        intro key member
        have keyValid : validResolvedPubKey .tapscript key :=
          allKeysValid_of_mem restValid member
        exact checkSigWithEncoding_empty
          (checkSigEncodingFor_empty_of_modeled keyValid version modeled)
          (sound.emptySignatureInvalid key)
      have decoded : decodeBinaryScriptNums flags (scriptNat threshold)
          falseElement = .ok (Int.ofNat threshold, 0) := by
        have thresholdDecoded := valid.2.2.decode flags.minimalData
        have zeroDecoded : decodeScriptNum falseElement flags.minimalData
            maxArithmeticScriptNumBytes = .ok 0 := by
          simpa [boolToElement] using
            (BooleanResultFacts.canonical false ({} : CorrectnessModifiers)
              flags).decoded
        simp only [decodeBinaryScriptNums, thresholdDecoded, zeroDecoded]
        rfl
      simpa [Witness.toInitialStack, boolToElement] using
        (multiA_dissatisfaction_execution (threshold := threshold)
          (firstKey := firstKey) (keys := keys) tapVersion valid.1
          firstChecked tailChecked decoded)

/-- Well-formed `multi_a` exposes strong generated support. Well-formedness
    supplies Tapscript key/context and arity facts; the executable arithmetic
    guard is handled separately, with its invalid branch supporting no usable
    witness on either side. -/
theorem generatedContract_multiA_of_wellFormed
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi_a threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates (.multi_a threshold keys) env)
      scriptCtx (.multi_a threshold keys)
        ⟨.B, { d := true, u := true }⟩ flags env.txCtx := by
  cases scriptCtx with
  | p2wsh =>
      simp [CoreFragment.WellFormed,
        ScriptContext.permitsCheckSigAddMulti] at wellFormed
  | tapscript =>
      rcases wellFormed with ⟨permits, thresholdValid, keyCountValid, validKeys⟩
      have typed : HasType .tapscript (.multi_a threshold keys)
          ⟨.B, { d := true, u := true }⟩ :=
        .multi_a threshold keys thresholdValid.1 thresholdValid.2
      by_cases valid : candidateThresholdValid threshold keys.length
      · cases keys with
        | nil =>
            rcases thresholdValid with ⟨positive, atMost⟩
            simp at atMost
            omega
        | cons firstKey keys =>
            rw [satisfactionCandidates_multi_a]
            exact generatedContract_multiA_valid valid validKeys version modeled
              sound encodings
      · rw [satisfactionCandidates_multi_a]
        have empty : multiACandidates threshold keys env = {} := by
          simp [multiACandidates, valid]
        rw [empty]
        exact ⟨typed, CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩

/-! ## Legacy multisignature candidate composition -/

/-- Selected legacy signatures embedded in the top-first key order consumed by
    CHECKMULTISIG. `skip` retains the current signature while advancing a key;
    `take` records the source key which supplied and consumes that signature. -/
inductive OrderedMultiSignatures (env : SatEnv) :
    Stack → List PubKey → Prop where
  | nil (keys : List PubKey) : OrderedMultiSignatures env [] keys
  | skip {signature : StackElement} {signatures : Stack}
      {key : PubKey} {keys : List PubKey}
      (tail : OrderedMultiSignatures env (signature :: signatures) keys) :
      OrderedMultiSignatures env (signature :: signatures) (key :: keys)
  | take {signature : StackElement} {signatures : Stack}
      {key : PubKey} {keys : List PubKey}
      (selected : env.signatureFor key = some signature)
      (tail : OrderedMultiSignatures env signatures keys) :
      OrderedMultiSignatures env (signature :: signatures) (key :: keys)

namespace OrderedMultiSignatures

/-- An ordered signature embedding never contains more signatures than keys. -/
theorem length_le {env : SatEnv} {signatures : Stack} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env signatures keys) :
    signatures.length ≤ keys.length := by
  induction ordered with
  | nil => simp
  | skip tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega
  | take selected tail ih =>
      simp only [List.length_cons] at ih ⊢
      omega

/-- Removing the first required signature preserves an ordered embedding into
    the same key list. Keys through that signature's designated key become
    skipped keys for the next required signature. -/
theorem dropSignature {env : SatEnv} {signature : StackElement}
    {signatures : Stack} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env (signature :: signatures) keys) :
    OrderedMultiSignatures env signatures keys := by
  have tailOrdered : ∀ {source : Stack} {keyList : List PubKey},
      OrderedMultiSignatures env source keyList →
      OrderedMultiSignatures env source.tail keyList := by
    intro source keyList relation
    induction relation with
    | nil keys => exact .nil keys
    | @skip current rest key keys tail ih =>
        cases rest with
        | nil => exact .nil (key :: keys)
        | cons next rest =>
            simp only [List.tail_cons]
            exact .skip ih
    | @take current rest key keys selected tail ih =>
        cases rest with
        | nil => exact .nil (key :: keys)
        | cons next rest =>
            simp only [List.tail_cons]
            exact .skip tail
  exact tailOrdered ordered

/-- A successful check at the current key consumes the current signature while
    preserving the order of all remaining signatures. This also covers success
    at a skipped key before the signature's designated environment key. -/
theorem consumeCurrent {env : SatEnv} {signature : StackElement}
    {signatures : Stack} {key : PubKey} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env (signature :: signatures)
      (key :: keys)) :
    OrderedMultiSignatures env signatures keys := by
  cases ordered with
  | skip tail => exact tail.dropSignature
  | take selected tail => exact tail

/-- Add an unmatched key at the front of evaluator order. -/
theorem prependSkippedKey {env : SatEnv} {signatures : Stack}
    {keys : List PubKey} (key : PubKey)
    (ordered : OrderedMultiSignatures env signatures keys) :
    OrderedMultiSignatures env signatures (key :: keys) := by
  cases signatures with
  | nil => exact .nil (key :: keys)
  | cons signature signatures => exact .skip ordered

/-- The first required signature was selected for some remaining key. -/
theorem headSelected {env : SatEnv} {signature : StackElement}
    {signatures : Stack} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env (signature :: signatures) keys) :
    ∃ key, key ∈ keys ∧ env.signatureFor key = some signature := by
  have aux : ∀ {source : Stack} {keyList : List PubKey},
      OrderedMultiSignatures env source keyList →
      ∀ {head : StackElement} {tail : Stack}, source = head :: tail →
        ∃ key, key ∈ keyList ∧ env.signatureFor key = some head := by
    intro source keyList relation
    induction relation with
    | nil keys =>
        intro head tail equal
        simp at equal
    | @skip current rest key keys relation ih =>
        intro head tail equal
        obtain ⟨ownKey, member, selected⟩ := ih equal
        exact ⟨ownKey, by simp [member], selected⟩
    | @take current rest key keys selected relation ih =>
        intro head tail equal
        have currentEq : current = head := (List.cons.inj equal).1
        subst head
        exact ⟨key, by simp, selected⟩
  exact aux ordered rfl

/-- Every selected signature in an ordered embedding satisfies the Script
    element-size limit under the modeled P2WSH encoding assumptions. -/
theorem itemsBounded
    {env : SatEnv} {flags : ScriptFlags} {signatures : Stack}
    {keys : List PubKey}
    (ordered : OrderedMultiSignatures env signatures keys)
    (valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (encodings : env.EncodingSound flags) :
    Witness.ItemsBounded signatures := by
  induction ordered with
  | nil => exact Witness.ItemsBounded.nil
  | @skip signature signatures key keys tail ih =>
      exact ih (fun tailKey member => valid tailKey (by simp [member]))
  | @take signature signatures key keys selected tail ih =>
      intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact selectedSignature_size_le (valid key (by simp)) version modeled
          encodings selected
      · exact ih (fun tailKey tailMember =>
          valid tailKey (by simp [tailMember])) item member

end OrderedMultiSignatures

/-- Exact-count provenance for legacy key rows produces the top-first ordered
    signature embedding used by CHECKMULTISIG. The combined inner witness has
    exactly one element for every selected satisfaction row. -/
theorem CandidatePair.ChoiceTrace.toOrderedMultiSignatures
    {env : SatEnv} {keys : List PubKey} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : CandidatePair.ChoiceTrace
      (keys.map fun key => legacyMultiKeyChoice key env)
      count frames witness) :
    OrderedMultiSignatures env witness keys.reverse ∧
      witness.length = count := by
  induction keys using listSnocInductionGenerated generalizing count frames witness with
  | nil =>
      simp only [List.map_nil] at trace
      generalize pairsEq : ([] : List CandidatePair) = pairs at trace
      cases trace
      · exact ⟨.nil [], rfl⟩
      · simp at pairsEq
      · simp at pairsEq
  | snoc keys key ih =>
      rw [List.map_append, List.map_singleton] at trace
      generalize pairsEq :
        (keys.map fun key => legacyMultiKeyChoice key env) ++
          [legacyMultiKeyChoice key env] = pairs at trace
      cases trace with
      | nil => simp at pairsEq
      | @sat children priorCount priorFrames priorWitness child childWitness
          prior selected =>
          have pairsEq' :
              (keys.map fun key => legacyMultiKeyChoice key env).concat
                (legacyMultiKeyChoice key env) = children.concat child := by
            simpa only [List.concat_eq_append] using pairsEq
          obtain ⟨childrenEq, childEq⟩ := List.concat_inj.mp pairsEq'
          subst children
          subst child
          cases selectedSig : env.signatureFor key with
          | none => simp [legacyMultiKeyChoice, selectedSig] at selected
          | some signature =>
              have frameEq : childWitness = [signature] := by
                simpa [legacyMultiKeyChoice, selectedSig] using selected.symm
              subst childWitness
              obtain ⟨priorOrdered, priorLength⟩ := ih prior
              constructor
              · simpa [Witness.combine] using
                  (OrderedMultiSignatures.take selectedSig priorOrdered)
              · simp [Witness.combine, priorLength]
      | @dsat children priorCount priorFrames priorWitness child childWitness
          prior selected =>
          have pairsEq' :
              (keys.map fun key => legacyMultiKeyChoice key env).concat
                (legacyMultiKeyChoice key env) = children.concat child := by
            simpa only [List.concat_eq_append] using pairsEq
          obtain ⟨childrenEq, childEq⟩ := List.concat_inj.mp pairsEq'
          subst children
          subst child
          have frameEq : childWitness = [] := by
            simpa [legacyMultiKeyChoice] using selected
          subst childWitness
          obtain ⟨priorOrdered, priorLength⟩ := ih prior
          constructor
          · simpa [Witness.combine] using priorOrdered.prependSkippedKey key
          · simpa [Witness.combine] using priorLength

private theorem selectedCheckSig_witnessV0
    {env : SatEnv} {key : PubKey} {signature : StackElement}
    (version : env.txCtx.sigVersion = .witnessV0)
    (sound : env.Sound)
    (selected : env.signatureFor key = some signature) :
    checkSig signature key.bytes env.txCtx.sigHash = true := by
  have verified := sound.signatureValid selected
  simpa [verifySigFor, checkedVerifySigFor, version] using verified

/-- A failed current signature check cannot be a `take`: a selected signature
    verifies for its designated key by environment soundness. -/
theorem OrderedMultiSignatures.advanceRejected
    {env : SatEnv} {signature : StackElement} {signatures : Stack}
    {key : PubKey} {keys : List PubKey}
    (ordered : OrderedMultiSignatures env (signature :: signatures)
      (key :: keys))
    (version : env.txCtx.sigVersion = .witnessV0)
    (sound : env.Sound)
    (rejected : checkSig signature key.bytes env.txCtx.sigHash = false) :
    OrderedMultiSignatures env (signature :: signatures) keys := by
  cases ordered with
  | skip tail => exact tail
  | take selected tail =>
      have accepted := selectedCheckSig_witnessV0 version sound selected
      rw [rejected] at accepted
      contradiction

/-- Greedy CHECKMULTISIG succeeds for any ordered selected-signature
    embedding. A signature that verifies against an earlier skipped key is
    safely consumed there; the remaining signature order is preserved. -/
theorem checkMultiSigFor_true_of_ordered
    {env : SatEnv} {flags : ScriptFlags} {signatures : Stack}
    {keys : List PubKey}
    (ordered : OrderedMultiSignatures env signatures keys)
    (valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key)
    (version : env.txCtx.sigVersion = .witnessV0)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    checkMultiSigFor checkSig flags env.txCtx signatures
      (keys.map (fun key => key.bytes)) = .ok true := by
  induction keys generalizing signatures with
  | nil =>
      have emptyLength : signatures.length = 0 := by
        have bound := ordered.length_le
        simpa only [List.length_nil] using Nat.eq_zero_of_le_zero bound
      have empty : signatures = [] := List.eq_nil_of_length_eq_zero emptyLength
      subst signatures
      simp [checkMultiSigFor]
  | cons key keys ih =>
      cases signatures with
      | nil => simp [checkMultiSigFor]
      | cons signature signatures =>
          obtain ⟨ownKey, ownMember, selected⟩ := ordered.headSelected
          have encodedOwn := encodings ownKey signature selected
          have currentValid : validCompressedPubKeyBytes key.bytes := by
            simpa [validResolvedPubKey] using valid key (by simp)
          have encodedCurrent : checkSigEncodingFor flags .witnessV0
              signature key.bytes = .ok () :=
            checkSigEncodingFor_witnessV0_rekey currentValid
              (by simpa [version] using encodedOwn)
          have encodedCurrentCtx : checkSigEncodingFor flags
              env.txCtx.sigVersion signature key.bytes = .ok () := by
            simpa [version] using encodedCurrent
          have validTail : ∀ tailKey ∈ keys,
              validResolvedPubKey .p2wsh tailKey := by
            intro tailKey member
            exact valid tailKey (by simp [member])
          by_cases accepted :
              checkSig signature key.bytes env.txCtx.sigHash = true
          · have nextOrdered := ordered.consumeCurrent
            have enough := nextOrdered.length_le
            have next := ih nextOrdered validTail
            rw [List.map_cons, checkMultiSigFor, encodedCurrentCtx, accepted]
            simp only [List.length_map]
            change (if signatures.length > keys.length then .ok false
              else checkMultiSigFor checkSig flags env.txCtx signatures
                (keys.map fun key => key.bytes)) = .ok true
            rw [if_neg (by omega)]
            exact next
          · have rejected :
                checkSig signature key.bytes env.txCtx.sigHash = false := by
              cases checked : checkSig signature key.bytes env.txCtx.sigHash
              · rfl
              · exact False.elim (accepted checked)
            have nextOrdered := ordered.advanceRejected version sound rejected
            have enough := nextOrdered.length_le
            have next := ih nextOrdered validTail
            rw [List.map_cons, checkMultiSigFor, encodedCurrentCtx, rejected]
            simp only [if_neg Bool.false_ne_true, List.length_map]
            change (if (signature :: signatures).length > keys.length then
                .ok false
              else checkMultiSigFor checkSig flags env.txCtx
                (signature :: signatures)
                (keys.map fun key => key.bytes)) = .ok true
            rw [if_neg (by omega)]
            exact next

/-- The exact-count legacy candidate yields a successful greedy CHECKMULTISIG
    result in the reversed key order used by the compiled script. -/
theorem CandidatePair.legacySelected_checkMultiSigFor
    {env : SatEnv} {flags : ScriptFlags} {threshold : Nat}
    {keys : List PubKey} {inner : Witness}
    (selected : (CandidatePair.selectExactly threshold
      (keys.map fun key => legacyMultiKeyChoice key env)).usableWitness? =
        some inner)
    (valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    checkMultiSigFor checkSig flags env.txCtx inner
      ((keys.map fun key => key.bytes).reverse) = .ok true := by
  obtain ⟨frames, trace⟩ :=
    CandidatePair.selectExactly_choiceTrace selected
  have ordered := trace.toOrderedMultiSignatures.1
  have reversedValid : ∀ key ∈ keys.reverse,
      validResolvedPubKey .p2wsh key := by
    intro key member
    exact valid key (by simpa using member)
  have checked := checkMultiSigFor_true_of_ordered ordered reversedValid
    version sound encodings
  simpa using checked

private theorem exceptOkSeqGenerated {ε α : Type} (next : Except ε α) :
    (do Except.ok (); next) = next := by
  rfl

/-- Empty signatures are rejected at every P2WSH key. CHECKMULTISIG eventually
    returns false either recursively or as soon as too few keys remain. -/
theorem checkMultiSigFor_all_empty_false_topFirst
    {env : SatEnv} {flags : ScriptFlags} {threshold : Nat}
    {keys : List PubKey}
    (positive : 0 < threshold) (atMost : threshold ≤ keys.length)
    (valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (sound : env.Sound) :
    checkMultiSigFor checkSig flags env.txCtx
      (List.replicate threshold falseElement)
      (keys.map fun key => key.bytes) = .ok false := by
  induction keys generalizing threshold with
  | nil => simp only [List.length_nil] at atMost; omega
  | cons key keys ih =>
      cases threshold with
      | zero => simp at positive
      | succ threshold =>
          have currentValid : validResolvedPubKey .p2wsh key :=
            valid key (by simp)
          have validTail : ∀ tailKey ∈ keys,
              validResolvedPubKey .p2wsh tailKey := by
            intro tailKey member
            exact valid tailKey (by simp [member])
          have encoded := checkSigEncodingFor_empty_of_modeled
            currentValid version modeled
          have versionEq : env.txCtx.sigVersion = .witnessV0 := version
          have rejected :
              checkSig falseElement key.bytes env.txCtx.sigHash = false := by
            have invalid := sound.emptySignatureInvalid key
            simpa [verifySigFor, checkedVerifySigFor, versionEq] using invalid
          rw [List.replicate_succ, List.map_cons, checkMultiSigFor,
            encoded, rejected]
          simp only [if_neg Bool.false_ne_true, List.length_map]
          rw [exceptOkSeqGenerated]
          simp only [List.length_cons, List.length_replicate]
          by_cases tooMany : threshold + 1 > keys.length
          · rw [if_pos tooMany]
            rfl
          · have tailBound : threshold + 1 ≤ keys.length := by omega
            have next := ih (by omega) tailBound validTail
            rw [if_neg tooMany]
            simpa only [List.replicate_succ] using next

/-- Canonical empty signatures produce false in the reversed key order used by
    compiled legacy `multi`. -/
theorem checkMultiSigFor_all_empty_false
    {env : SatEnv} {flags : ScriptFlags} {threshold : Nat}
    {keys : List PubKey}
    (positive : 0 < threshold) (atMost : threshold ≤ keys.length)
    (valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (sound : env.Sound) :
    checkMultiSigFor checkSig flags env.txCtx
      (List.replicate threshold falseElement)
      ((keys.map fun key => key.bytes).reverse) = .ok false := by
  have reversedValid : ∀ key ∈ keys.reverse,
      validResolvedPubKey .p2wsh key := by
    intro key member
    exact valid key (by simpa using member)
  have checked := checkMultiSigFor_all_empty_false_topFirst
    (env := env) (flags := flags) (keys := keys.reverse)
    positive (by simpa using atMost) reversedValid version modeled sound
  simpa using checked

private theorem replicateFalse_snocGenerated (count : Nat) :
    List.replicate count falseElement ++ [falseElement] =
      List.replicate (count + 1) falseElement := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (falseElement :: ·) ih

/-- Strong generated contract for a structurally valid legacy `multi` pair.
    Satisfaction follows the exact-count signature subsequence; dissatisfaction
    uses the canonical historical dummy and all-empty signature vector. -/
theorem generatedContract_multi_valid
    {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (thresholdValid : validThreshold threshold keys.length)
    (keyBound : validLegacyMultiKeyCount keys.length)
    (validKeys : CoreFragment.allKeysValid .p2wsh keys)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (legacyMultiCandidates threshold keys env) .p2wsh
        (.multi threshold keys)
        ⟨.B, { n := true, d := true, u := true }⟩ flags env.txCtx := by
  simp only [validThreshold] at thresholdValid
  simp only [validLegacyMultiKeyCount] at keyBound
  obtain ⟨positive, atMost⟩ := thresholdValid
  have keyBoundMax : keys.length ≤ maxPubKeysPerMultiSig := by
    simpa [maxPubKeysPerMultiSig] using keyBound
  have typed : HasType .p2wsh (.multi threshold keys)
      ⟨.B, { n := true, d := true, u := true }⟩ :=
    .multi threshold keys positive atMost
  have guard : ¬ (threshold = 0 ∨ keys.length < threshold ∨
      maxPubKeysPerMultiSig < keys.length) := by
    simp only [not_or]
    constructor
    · omega
    constructor
    · omega
    · exact Nat.not_lt_of_ge keyBoundMax
  have valid : ∀ key ∈ keys, validResolvedPubKey .p2wsh key :=
    fun key member => allKeysValid_of_mem validKeys member
  have reversedValid : ∀ key ∈ keys.reverse,
      validResolvedPubKey .p2wsh key := by
    intro key member
    exact valid key (by simpa using member)
  refine ⟨typed, ?_, ?_⟩
  · rw [show (legacyMultiCandidates threshold keys env).sat =
      finalizeLegacyMulti (CandidatePair.selectExactly threshold
        (keys.map fun key => legacyMultiKeyChoice key env)) by
        simp [legacyMultiCandidates, guard]]
    intro witness selected
    rw [CandidateResult.finalizeLegacyMulti_usableWitness_iff] at selected
    obtain ⟨inner, innerSelected, rfl⟩ := selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.selectExactly_choiceTrace innerSelected
    obtain ⟨ordered, signatureCount⟩ :=
      trace.toOrderedMultiSignatures
    have innerBounded := ordered.itemsBounded reversedValid version modeled
      encodings
    have finalBounded :
        Witness.ItemsBounded (falseElement :: inner.reverse) := by
      intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact falseElement_size_le
      · exact innerBounded item (by simpa using member)
    apply GeneratedContract.b
    · refine ⟨finalBounded, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro enabled expectedTrue
        cases inner with
        | nil =>
            simp only [List.length_nil] at signatureCount
            omega
        | cons signature signatures =>
            obtain ⟨key, member, signatureSelected⟩ := ordered.headSelected
            exact ⟨signature, signatures ++ [falseElement], by
              simp [Witness.toInitialStack],
              selectedSignature_size_ne_zero sound signatureSelected⟩
    · exact BooleanResultFacts.canonical true _ flags
    · have checked := CandidatePair.legacySelected_checkMultiSigFor
        innerSelected valid version sound encodings
      have versionEq : env.txCtx.sigVersion = .witnessV0 := version
      have versionNe : env.txCtx.sigVersion ≠ .tapscript := by
        rw [versionEq]
        decide
      have executed := BExecution.multi versionNe
        keyBoundMax atMost signatureCount checked (Or.inl rfl)
      simpa [Witness.toInitialStack, boolToElement] using executed
  · rw [show (legacyMultiCandidates threshold keys env).dsat =
      .usable (List.replicate (threshold + 1) falseElement) false by
        simp [legacyMultiCandidates, guard]]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le]
      · simp
      · simp
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · have versionEq : env.txCtx.sigVersion = .witnessV0 := version
      have versionNe : env.txCtx.sigVersion ≠ .tapscript := by
        rw [versionEq]
        decide
      have checked := checkMultiSigFor_all_empty_false positive
        atMost valid version modeled sound
      have executed := multi_dissatisfaction_execution versionNe
        keyBoundMax atMost checked
      simpa [Witness.toInitialStack, List.reverse_replicate,
        replicateFalse_snocGenerated, boolToElement] using executed

/-- Every well-formed legacy `multi` exposes strong generated support. Its
    P2WSH context restriction supplies witness-v0 execution; well-formedness
    supplies the threshold, key-count, and key-validity premises. -/
theorem generatedContract_multi_of_wellFormed
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates (.multi threshold keys) env)
      scriptCtx (.multi threshold keys)
        ⟨.B, { n := true, d := true, u := true }⟩ flags env.txCtx := by
  cases scriptCtx with
  | tapscript =>
      simp [CoreFragment.WellFormed,
        ScriptContext.permitsLegacyMulti] at wellFormed
  | p2wsh =>
      rcases wellFormed with
        ⟨permits, thresholdValid, keyBound, validKeys⟩
      rw [satisfactionCandidates_multi]
      exact generatedContract_multi_valid thresholdValid keyBound validKeys
        version modeled sound encodings

end LeanMiniscript.Miniscript
