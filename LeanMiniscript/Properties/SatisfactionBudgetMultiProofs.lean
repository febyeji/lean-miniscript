import LeanMiniscript.Properties.SatisfactionBudgetGuardProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

def signatureBudget (signatures : Stack) : Nat :=
  (signatures.map signatureValidationWeight).sum

@[simp] theorem signatureBudget_nil : signatureBudget [] = 0 := rfl
@[simp] theorem signatureBudget_cons (signature : StackElement) (rest : Stack) :
    signatureBudget (signature :: rest) = signatureValidationWeight signature + signatureBudget rest := rfl
@[simp] theorem signatureBudget_empty (count : Nat) :
    signatureBudget (List.replicate count falseElement) = 0 := by
  simp [signatureBudget, show signatureValidationWeight falseElement = 0 from rfl]

namespace ExecutesBudgetFrame

theorem pushData (value : StackElement) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.pushData value] [] [value] flags ctx 0 :=
  of_resource_zero (ExecutesResourceFrame.pushData value flags ctx)

theorem pushNum (value : Int) (flags : ScriptFlags) (ctx : TxContext) :
    ExecutesBudgetFrame [.pushNum value] [] [scriptNum value] flags ctx 0 :=
  of_resource_zero (ExecutesResourceFrame.pushNum value flags ctx)

end ExecutesBudgetFrame

private theorem checkSigFrame
    {key signature : StackElement} {truth : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok truth) :
    ExecutesBudgetFrame [.op .OP_CHECKSIG] [key, signature]
      [boolToElement truth] flags ctx (signatureValidationWeight signature) := by
  apply ExecutesBudgetFrame.single
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
  · intro rest
    simp only [List.cons_append, List.nil_append, executedSignatureWeight]
    split <;> simp

private theorem checkSigAddFrame
    {key signature : StackElement} {count : Int} {truth : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeCheckSigAddCount flags ctx (scriptNum count) = .ok count)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok truth) :
    ExecutesBudgetFrame [.op .OP_CHECKSIGADD]
      [key, scriptNum count, signature]
      [scriptNum (count + Int.ofNat truth.toNat)] flags ctx
      (signatureValidationWeight signature) := by
  apply ExecutesBudgetFrame.single
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
  · intro rest
    simp only [List.cons_append, List.nil_append, executedSignatureWeight]
    split <;> simp

theorem CheckSigAddTailExecution.budgetFrame
    {flags : ScriptFlags} {ctx : TxContext} {count total : Int}
    {keys : List PubKey} {signatures : Stack}
    (executed : CheckSigAddTailExecution flags ctx count keys signatures total) :
    ExecutesBudgetFrame (compileCheckSigAddTail keys)
      (scriptNum count :: signatures) [scriptNum total] flags ctx
      (signatureBudget signatures) := by
  induction executed with
  | nil count =>
      simpa [compileCheckSigAddTail, signatureBudget] using
        ExecutesBudgetFrame.empty [scriptNum count] flags ctx
  | @cons count total key keys signature signatures truth decoded checked tail ih =>
      have pushed := (ExecutesBudgetFrame.pushData key.bytes flags
        ctx).withSuffix
        (suffix := [scriptNum count, signature])
      have added := checkSigAddFrame decoded checked
      have segment := (pushed.append added).withSuffix (suffix := signatures)
      simpa [compileCheckSigAddTail, signatureBudget,
        List.append_assoc] using segment.append ih

private theorem multiAChildrenFrame
    {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total) :
    ExecutesBudgetFrame (compileCheckSigAdd (firstKey :: keys))
      (firstSignature :: signatures) [scriptNum total] flags ctx
      (signatureBudget (firstSignature :: signatures)) := by
  have pushed := (ExecutesBudgetFrame.pushData firstKey.bytes flags
    ctx).withSuffix
    (suffix := [firstSignature])
  have checkedFrame := checkSigFrame checked
  have firstFrame := (pushed.append checkedFrame).withSuffix
    (suffix := signatures)
  have tailFrame :=
    _root_.LeanMiniscript.Properties.CheckSigAddTailExecution.budgetFrame tail
  cases firstTruth <;>
    simpa [compileCheckSigAdd, signatureBudget, boolToElement,
      scriptNum_zero, scriptNum_one, List.append_assoc] using
      firstFrame.append tailFrame

private theorem numEqualFrame
    {first second : StackElement} {a b : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeBinaryScriptNums flags first second = .ok (a, b)) :
    ExecutesBudgetFrame [.op .OP_NUMEQUAL] [first, second]
      [boolToElement (a == b)] flags ctx 0 :=
  .of_zero fun rest altStack =>
    Eval.numequal first second a b rest [] altStack flags ctx _ decoded
      Eval.done

private theorem multiABudgetFrame
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
    ExecutesBudgetFrame (compile (.multi_a threshold (firstKey :: keys)))
      (firstSignature :: signatures)
      [boolToElement (Int.ofNat threshold == total)] flags ctx
      (signatureBudget (firstSignature :: signatures)) := by
  have children := multiAChildrenFrame checked tail
  have pushed := (ExecutesBudgetFrame.pushNum threshold flags ctx).withSuffix
    (suffix := [scriptNum total])
  have compared := numEqualFrame (flags := flags) (ctx := ctx) decoded
  have complete := children.append (pushed.append compared)
  simpa [compile, compileWithKeyHash] using complete

namespace MultiASlots

theorem budgetFrame
    {flags : ScriptFlags} {txCtx : TxContext} {threshold : Nat}
    {firstKey : PubKey} {keys : List PubKey} {truths : List Bool}
    {frames : List Witness} {signatures : Stack}
    (slots : MultiASlots flags txCtx (firstKey :: keys) truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe threshold)
    (sumEq : (truths.map Bool.toNat).sum = threshold) :
    ExecutesBudgetFrame (compile (.multi_a threshold (firstKey :: keys)))
      signatures [trueElement] flags txCtx
      (signatureBudget signatures) := by
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
      have bounded := multiABudgetFrame firstSlot.checked tailExec decoded
      simpa [boolToElement] using bounded

theorem signatureBudget_le_payload
    {flags : ScriptFlags} {txCtx : TxContext} {keys : List PubKey}
    {truths : List Bool} {frames : List Witness} {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures)
    (valid : CoreFragment.allKeysValid .tapscript keys)
    (version : txCtx.sigVersion = .tapscript) :
    signatureBudget signatures ≤ witnessPayload signatures := by
  induction slots with
  | nil => simp [witnessPayload]
  | @cons key truth frame signature keys truths frames signatures head tail ih =>
      have encoded : checkSigEncodingFor flags txCtx.sigVersion signature key.bytes = .ok () := by
        cases encoding : checkSigEncodingFor flags txCtx.sigVersion signature key.bytes with
        | ok value => cases value; rfl
        | error error =>
            have checked := head.checked
            simp [checkSigWithEncoding, encoding] at checked
      rw [version] at encoded
      have bound := signatureValidationWeight_le_size_of_encoding valid.1 encoded
      have tailBound := ih valid.2
      simp only [signatureBudget_cons, witnessPayload, List.map_cons, List.sum_cons] at *
      omega

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

theorem generatedBudgets_multiA_valid
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (valid : candidateThresholdValid threshold (firstKey :: keys).length)
    (validKeys : CoreFragment.allKeysValid .tapscript (firstKey :: keys))
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedBudgets
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
    apply GeneratedBudgetContract.b
    · refine ⟨trace.itemsBounded slots.framesBounded, ?_, ?_, ?_⟩ <;> simp
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack, slots.framesShape]
      exact slots.multiAExecution tapVersion valid.2.2 sumEq
    · rw [trace.toInitialStack, slots.framesShape]
      exact _root_.LeanMiniscript.Properties.MultiASlots.budgetFrame slots
        tapVersion valid.2.2 sumEq
    · have bound := MultiASlots.signatureBudget_le_payload slots validKeys tapVersion
      have shape := congrArg (fun items : Stack => witnessPayload items)
        (trace.toInitialStack.trans slots.framesShape)
      simp only [witnessPayload, Witness.toInitialStack, List.map_reverse, List.sum_reverse] at shape
      simpa [witnessPayload, shape] using bound
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
    apply GeneratedBudgetContract.b
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
    · have bounded := multiABudgetFrame (threshold := threshold)
          firstChecked tailExec decoded
      simpa [Witness.toInitialStack, List.replicate_succ, boolToElement,
        valid.1, List.replicate_rotate (a := falseElement),
        show signatureValidationWeight falseElement = 0 from rfl] using bounded
    · exact Nat.zero_le _

theorem generatedBudgets_multiA
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi_a threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedBudgets
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
            exact generatedBudgets_multiA_valid valid validKeys version modeled
              sound encodings
      · rw [satisfactionCandidates_multi_a]
        have empty : multiACandidates threshold keys env = {} := by
          simp [multiACandidates, valid]
        rw [empty]
        exact ⟨typed, CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩

end LeanMiniscript.Properties
