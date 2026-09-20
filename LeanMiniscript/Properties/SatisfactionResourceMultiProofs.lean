import LeanMiniscript.Properties.SatisfactionResourceAtomicProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-! # Resource proofs for multisignature atoms -/

private theorem replicateFalse_rotate (count : Nat) :
    List.replicate count falseElement ++ [falseElement] =
      falseElement :: List.replicate count falseElement := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (falseElement :: ·) ih

private def checkSigTrace : StackTraceBound := ⟨1, 1⟩
private def checkSigAddTrace : StackTraceBound := ⟨2, 2⟩
private def multiAFirstTrace : StackTraceBound :=
  StackTraceBound.push.sequential checkSigTrace
private def multiATailStepTrace : StackTraceBound :=
  StackTraceBound.push.sequential checkSigAddTrace

private def multiATailTrace : List PubKey → StackTraceBound
  | [] => StackTraceBound.empty
  | _ :: keys => multiATailStepTrace.sequential (multiATailTrace keys)

private theorem checkSigFrame
    {key signature : StackElement} {truth : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok truth) :
    ExecutesResourceFrame [.op .OP_CHECKSIG] [key, signature]
      [boolToElement truth] flags ctx checkSigTrace 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases truth with
    | false =>
        simpa [boolToElement] using
          (Eval.checksig_failure key signature rest [] altStack flags ctx _
            checked Eval.done)
    | true =>
        simpa [boolToElement] using
          (Eval.checksig_success key signature rest [] altStack flags ctx _
            checked Eval.done)
  · simp [checkSigTrace]
  · simp [checkSigTrace]
  · simp [checkSigTrace]
  · simp [executedMultiSigKeyCharge]

private theorem checkSigAddFrame
    {key signature : StackElement} {count : Int} {truth : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeCheckSigAddCount flags ctx (scriptNum count) = .ok count)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok truth) :
    ExecutesResourceFrame [.op .OP_CHECKSIGADD]
      [key, scriptNum count, signature]
      [scriptNum (count + Int.ofNat truth.toNat)] flags ctx
      checkSigAddTrace 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    cases truth with
    | false =>
        simpa using
          (Eval.checksigadd_failure key (scriptNum count) signature count rest
            [] altStack flags ctx _ decoded checked Eval.done)
    | true =>
        simpa using
          (Eval.checksigadd_success key (scriptNum count) signature count rest
            [] altStack flags ctx _ decoded checked Eval.done)
  · simp [checkSigAddTrace]
  · simp [checkSigAddTrace]
  · simp [checkSigAddTrace]
  · simp [executedMultiSigKeyCharge]

theorem CheckSigAddTailExecution.resourceFrame
    {flags : ScriptFlags} {ctx : TxContext} {count total : Int}
    {keys : List PubKey} {signatures : Stack}
    (executed : CheckSigAddTailExecution flags ctx count keys signatures total) :
    ExecutesResourceFrame (compileCheckSigAddTail keys)
      (scriptNum count :: signatures) [scriptNum total] flags ctx
      (multiATailTrace keys) 0 := by
  induction executed with
  | nil count =>
      simpa [compileCheckSigAddTail, multiATailTrace] using
        ExecutesResourceFrame.empty [scriptNum count] flags ctx
  | @cons count total key keys signature signatures truth decoded checked tail ih =>
      have pushed := (ExecutesResourceFrame.pushData key.bytes flags
        ctx).withSuffix
        (suffix := [scriptNum count, signature])
      have added := checkSigAddFrame decoded checked
      have segment := (pushed.append added).withSuffix (suffix := signatures)
      simpa [compileCheckSigAddTail, multiATailTrace, multiATailStepTrace,
        List.append_assoc] using segment.append ih

private theorem multiATailTrace_shape (keys : List PubKey) :
    multiATailTrace keys =
      if keys = [] then StackTraceBound.empty else
        { netDiff := Int.ofNat keys.length
          exec := Int.ofNat (keys.length + 1) } := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [multiATailTrace, ih, List.cons_ne_nil, ↓reduceIte]
      cases keys with
      | nil => rfl
      | cons next rest =>
          simp [multiATailStepTrace, checkSigAddTrace,
            StackTraceBound.push, checkSigAddTrace, checkSigAddTrace,
            StackTraceBound.sequential]
          omega

private theorem multiAChildrenFrame
    {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total) :
    ExecutesResourceFrame (compileCheckSigAdd (firstKey :: keys))
      (firstSignature :: signatures) [scriptNum total] flags ctx
      (multiAFirstTrace.sequential (multiATailTrace keys)) 0 := by
  have pushed := (ExecutesResourceFrame.pushData firstKey.bytes flags
    ctx).withSuffix
    (suffix := [firstSignature])
  have checkedFrame := checkSigFrame checked
  have firstFrame := (pushed.append checkedFrame).withSuffix
    (suffix := signatures)
  have tailFrame :=
    _root_.LeanMiniscript.Properties.CheckSigAddTailExecution.resourceFrame tail
  cases firstTruth <;>
    simpa [compileCheckSigAdd, multiAFirstTrace, boolToElement,
      scriptNum_zero, scriptNum_one, List.append_assoc] using
      firstFrame.append tailFrame

private theorem numEqualFrame
    {first second : StackElement} {a b : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeBinaryScriptNums flags first second = .ok (a, b)) :
    ExecutesResourceFrame [.op .OP_NUMEQUAL] [first, second]
      [boolToElement (a == b)] flags ctx StackTraceBound.binary 0 := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    exact Eval.numequal first second a b rest [] altStack flags ctx _ decoded
      Eval.done
  · simp [StackTraceBound.binary]
  · simp [StackTraceBound.binary]
  · simp [StackTraceBound.binary]
  · simp [executedMultiSigKeyCharge]

private theorem multiAResourceFrame
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total)) :
    ExecutesResourceFrame (compile (.multi_a threshold (firstKey :: keys)))
      (firstSignature :: signatures)
      [boolToElement (Int.ofNat threshold == total)] flags ctx
      { netDiff := Int.ofNat (firstKey :: keys).length - 1
        exec := Int.ofNat (firstKey :: keys).length } 0 := by
  have children := multiAChildrenFrame checked tail
  have pushed := (ExecutesResourceFrame.pushNum threshold flags ctx).withSuffix
    (suffix := [scriptNum total])
  have compared := numEqualFrame (flags := flags) (ctx := ctx) decoded
  have complete := children.append (pushed.append compared)
  have traceEq :
      (multiAFirstTrace.sequential (multiATailTrace keys)).sequential
          (StackTraceBound.push.sequential StackTraceBound.binary) =
        { netDiff := Int.ofNat (firstKey :: keys).length - 1
          exec := Int.ofNat (firstKey :: keys).length } := by
    rw [multiATailTrace_shape]
    cases keys with
    | nil => rfl
    | cons key keys =>
        simp [multiAFirstTrace, checkSigTrace, StackTraceBound.push,
          StackTraceBound.binary, StackTraceBound.sequential]
        omega
  rw [← traceEq]
  simpa [compile, compileWithKeyHash] using complete

namespace MultiASlots

/-- Checked source-order slots produce the advertised `multi_a` resource
    trace and no legacy multisignature charge. -/
theorem resourceFrame
    {flags : ScriptFlags} {txCtx : TxContext} {threshold : Nat}
    {firstKey : PubKey} {keys : List PubKey} {truths : List Bool}
    {frames : List Witness} {signatures : Stack}
    (slots : MultiASlots flags txCtx (firstKey :: keys) truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe threshold)
    (sumEq : (truths.map Bool.toNat).sum = threshold) :
    ExecutesResourceFrame (compile (.multi_a threshold (firstKey :: keys)))
      signatures [trueElement] flags txCtx
      { netDiff := Int.ofNat (firstKey :: keys).length - 1
        exec := Int.ofNat (firstKey :: keys).length } 0 := by
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
      have bounded := multiAResourceFrame firstSlot.checked tailExec decoded
      simpa [boolToElement] using bounded

end MultiASlots

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

/-- Resource-aware support for a valid nonempty Tapscript `multi_a`. -/
theorem generatedResources_multiA_valid
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (valid : candidateThresholdValid threshold (firstKey :: keys).length)
    (validKeys : CoreFragment.allKeysValid .tapscript (firstKey :: keys))
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
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
    apply GeneratedResourceContract.b
    · refine ⟨trace.itemsBounded slots.framesBounded, ?_, ?_, ?_⟩ <;> simp
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack, slots.framesShape]
      exact slots.multiAExecution tapVersion valid.2.2 sumEq
    · rw [trace.toInitialStack, slots.framesShape]
      exact _root_.LeanMiniscript.Properties.MultiASlots.resourceFrame slots
        tapVersion valid.2.2 sumEq
    · rfl
    · rfl
  · rw [show (multiACandidates threshold (firstKey :: keys) env).dsat =
      .usable (List.replicate (firstKey :: keys).length falseElement) false by
        simp [multiACandidates, valid']]
    apply CandidateResult.supports_usable
    rcases validKeys with ⟨firstValid, restValid⟩
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
    have tailExec := CheckSigAddTailExecution.allFalse keys tapVersion
      tailChecked
    apply GeneratedResourceContract.b
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le]
      · simp
      · simp
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · simpa [Witness.toInitialStack, boolToElement] using
        (multiA_dissatisfaction_execution (threshold := threshold)
          (firstKey := firstKey) (keys := keys) tapVersion valid.1
          firstChecked tailChecked decoded)
    · have bounded := multiAResourceFrame (threshold := threshold)
          firstChecked tailExec decoded
      simpa [Witness.toInitialStack, List.replicate_succ, boolToElement,
        valid.1, replicateFalse_rotate] using bounded
    · simp [selectedStackSummary, stackPathBounds]
    · rfl

/-- Every well-formed `multi_a` exposes resource-aware generated support. -/
theorem generatedResources_multiA
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi_a threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
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
            exact generatedResources_multiA_valid valid validKeys version modeled
              sound encodings
      · rw [satisfactionCandidates_multi_a]
        have empty : multiACandidates threshold keys env = {} := by
          simp [multiACandidates, valid]
        rw [empty]
        exact ⟨typed, CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩

private def keyPushTrace : List PubKey → StackTraceBound
  | [] => StackTraceBound.empty
  | _ :: keys => StackTraceBound.push.sequential (keyPushTrace keys)

private theorem keyPushTrace_shape (keys : List PubKey) :
    keyPushTrace keys =
      { netDiff := -(Int.ofNat keys.length), exec := 0 } := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp [keyPushTrace, ih, StackTraceBound.push,
        StackTraceBound.sequential]
      omega

private theorem compileKeyPushesFrame (keys : List PubKey)
    (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesResourceFrame (compileKeyPushes keys) []
      ((keys.map (fun key => key.bytes)).reverse) flags ctx
      (keyPushTrace keys) 0 := by
  induction keys with
  | nil =>
      simpa [compileKeyPushes, keyPushTrace] using
        ExecutesResourceFrame.empty [] flags ctx
  | cons key keys ih =>
      have tail := ih.withSuffix (suffix := [key.bytes])
      simpa [compileKeyPushes, keyPushTrace, List.append_assoc] using
        (ExecutesResourceFrame.pushData key.bytes flags ctx).append tail

private def multiCheckTrace (threshold keyCount : Nat) : StackTraceBound :=
  { netDiff := Int.ofNat (threshold + keyCount + 2)
    exec := Int.ofNat (threshold + keyCount + 2) }

private theorem checkMultiSigFrame
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {result : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok result)
    (allowed : result = true ∨ nullFailSatisfied flags signatures) :
    ExecutesResourceFrame [.op .OP_CHECKMULTISIG]
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ [falseElement])
      [boolToElement result] flags ctx
      (multiCheckTrace threshold keys.length) keys.length := by
  apply ExecutesResourceFrame.single
  · intro rest altStack
    let operands : CheckMultiSigOperands := {
      pubkeys := (keys.map (fun key => key.bytes)).reverse
      signatures := signatures
      dummy := some falseElement
      rest := rest }
    have decoded : decodeCheckMultiSigOperandsFor flags ctx
        (scriptNat keys.length ::
          (keys.map (fun key => key.bytes)).reverse ++
          scriptNat threshold :: signatures ++ falseElement :: rest) =
        .ok operands :=
      decodeCheckMultiSigOperandsFor_multi version keyBound thresholdBound
        signatureCount
    have dummyOk : checkMultiSigDummy flags (some falseElement) = .ok () := by
      simp [checkMultiSigDummy, nullDummySatisfied, stackElementEq,
        falseElement]
    cases result with
    | false =>
        have nullFail : nullFailSatisfied flags signatures := by
          rcases allowed with impossible | satisfied
          · simp at impossible
          · exact satisfied
        simpa [operands, boolToElement, List.append_assoc] using
          (Eval.checkmultisig_failure
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx _ decoded checked nullFail dummyOk
            Eval.done)
    | true =>
        simpa [operands, boolToElement, List.append_assoc] using
          (Eval.checkmultisig_success
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx _ decoded checked dummyOk Eval.done)
  · simp [multiCheckTrace, signatureCount]
    omega
  · simp [multiCheckTrace, signatureCount]
    omega
  · simp [multiCheckTrace]
    omega
  · intro rest
    have decoded := decodeCheckMultiSigOperandsFor_multi
      (flags := flags) (ctx := ctx) (rest := rest) version keyBound
      thresholdBound signatureCount
    simp only [executedMultiSigKeyCharge]
    rw [show
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
          scriptNat threshold :: signatures ++ [falseElement] ++ rest) =
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
          scriptNat threshold :: signatures ++ falseElement :: rest) by
        simp [List.append_assoc]]
    rw [decoded]
    simp

private theorem multiResourceFrame
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {result : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok result)
    (allowed : result = true ∨ nullFailSatisfied flags signatures) :
    ExecutesResourceFrame (compile (.multi threshold keys))
      (signatures ++ [falseElement]) [boolToElement result] flags ctx
      { netDiff := Int.ofNat threshold
        exec := Int.ofNat (threshold + keys.length + 2) } keys.length := by
  have thresholdPush :=
    (ExecutesResourceFrame.pushNum threshold flags ctx).withSuffix
    (suffix := signatures ++ [falseElement])
  have keyPushes := (compileKeyPushesFrame keys flags ctx).withSuffix
    (suffix := scriptNat threshold :: signatures ++ [falseElement])
  have countPush : ExecutesResourceFrame [.pushNum keys.length]
      ((keys.map (fun key => key.bytes)).reverse ++
        (scriptNat threshold :: signatures ++ [falseElement]))
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        (scriptNat threshold :: signatures ++ [falseElement]))
      flags ctx StackTraceBound.push 0 := by
    simpa [List.append_assoc, scriptNat] using
      (ExecutesResourceFrame.pushNum keys.length flags ctx).withSuffix
        (suffix := (keys.map (fun key => key.bytes)).reverse ++
          (scriptNat threshold :: signatures ++ [falseElement]))
  have checkedFrame := checkMultiSigFrame version keyBound thresholdBound
    signatureCount checked allowed
  have checkedFrame' : ExecutesResourceFrame [.op .OP_CHECKMULTISIG]
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        (scriptNat threshold :: signatures ++ [falseElement]))
      [boolToElement result] flags ctx
      (multiCheckTrace threshold keys.length) keys.length := by
    simpa [List.append_assoc] using checkedFrame
  have complete := ((thresholdPush.append keyPushes).append countPush).append
    checkedFrame'
  have traceEq :
      (((StackTraceBound.push.sequential (keyPushTrace keys)).sequential
        StackTraceBound.push).sequential
        (multiCheckTrace threshold keys.length)) =
      { netDiff := Int.ofNat threshold
        exec := Int.ofNat (threshold + keys.length + 2) } := by
    rw [keyPushTrace_shape]
    simp [StackTraceBound.push, StackTraceBound.sequential, multiCheckTrace]
    omega
  rw [← traceEq]
  simpa [compile, compileWithKeyHash, List.append_assoc] using complete

/-- Resource-aware support for a structurally valid legacy `multi`. -/
theorem generatedResources_multi_valid
    {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (thresholdValid : validThreshold threshold keys.length)
    (keyBound : validLegacyMultiKeyCount keys.length)
    (validKeys : CoreFragment.allKeysValid .p2wsh keys)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
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
    exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBoundMax⟩
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
    have checked := CandidatePair.legacySelected_checkMultiSigFor
      innerSelected valid version sound encodings
    have versionEq : env.txCtx.sigVersion = .witnessV0 := version
    have versionNe : env.txCtx.sigVersion ≠ .tapscript := by
      rw [versionEq]
      decide
    have executed := BExecution.multi versionNe keyBoundMax atMost
      signatureCount checked (Or.inl rfl)
    have bounded := multiResourceFrame versionNe keyBoundMax atMost
      signatureCount checked (Or.inl rfl)
    apply GeneratedResourceContract.b
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
    · simpa [Witness.toInitialStack, boolToElement] using executed
    · simpa [Witness.toInitialStack, boolToElement] using bounded
    · rfl
    · rfl
  · rw [show (legacyMultiCandidates threshold keys env).dsat =
      .usable (List.replicate (threshold + 1) falseElement) false by
        simp [legacyMultiCandidates, guard]]
    apply CandidateResult.supports_usable
    have versionEq : env.txCtx.sigVersion = .witnessV0 := version
    have versionNe : env.txCtx.sigVersion ≠ .tapscript := by
      rw [versionEq]
      decide
    have checked := checkMultiSigFor_all_empty_false positive atMost valid
      version modeled sound
    have nullFail : nullFailSatisfied flags
        (List.replicate threshold falseElement) := by
      right
      intro signature member
      have equal : signature = falseElement :=
        List.eq_of_mem_replicate member
      subst signature
      rfl
    have executed := multi_dissatisfaction_execution versionNe keyBoundMax
      atMost checked
    have bounded := multiResourceFrame versionNe keyBoundMax atMost (by simp)
      checked (Or.inr nullFail)
    apply GeneratedResourceContract.b
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le]
      · simp
      · simp
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · simpa [Witness.toInitialStack, List.reverse_replicate,
        List.replicate_succ, replicateFalse_rotate, boolToElement] using executed
    · simpa [Witness.toInitialStack, List.reverse_replicate,
        List.replicate_succ, replicateFalse_rotate, boolToElement] using bounded
    · rfl
    · rfl

/-- Every well-formed legacy `multi` exposes resource-aware support. -/
theorem generatedResources_multi
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedResources
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
      exact generatedResources_multi_valid thresholdValid keyBound validKeys
        version modeled sound encodings

end LeanMiniscript.Properties
