import LeanMiniscript.Miniscript.SatisfactionProofs.Execution

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Legacy multisignature execution -/

/-- Legacy multisignature count literals up to the consensus public-key limit
    decode to their corresponding nonnegative integers under either
    minimal-data setting. -/
theorem decodeScriptNum_scriptNat_multi_count
    (count : Nat) (flags : ScriptFlags)
    (bounded : count ≤ maxPubKeysPerMultiSig) :
    decodeScriptNum (scriptNat count) flags.minimalData
      maxArithmeticScriptNumBytes = .ok (Int.ofNat count) := by
  have bounded' : count ≤ 20 := by
    simpa [maxPubKeysPerMultiSig] using bounded
  have options : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨
      count = 4 ∨ count = 5 ∨ count = 6 ∨ count = 7 ∨ count = 8 ∨
      count = 9 ∨ count = 10 ∨ count = 11 ∨ count = 12 ∨ count = 13 ∨
      count = 14 ∨ count = 15 ∨ count = 16 ∨ count = 17 ∨
      count = 18 ∨ count = 19 ∨ count = 20 := by
    omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases flags.minimalData <;> rfl

/-- Pushing the source-order key list leaves the decoder's top-first reversed
    public-key frame while preserving every surrounding stack suffix. -/
theorem compileKeyPushes_execution (keys : List PubKey) (flags : ScriptFlags)
    (ctx : TxContext) :
    ExecutesStackFrame (compileKeyPushes keys) []
      ((keys.map (fun key => key.bytes)).reverse) flags ctx := by
  induction keys with
  | nil =>
      intro rest altStack
      exact Eval.done
  | cons key keys ih =>
      intro rest altStack
      apply Eval.pushData
      simpa [List.map_append, List.append_assoc] using
        ih (key.bytes :: rest) altStack

private theorem exceptOkBind {ε α β} (value : α)
    (next : α → Except ε β) :
    (do let result ← Except.ok value; next result) = next value := by
  rfl

/-- Decode the exact canonical stack frame produced by the legacy `multi`
    compiler and its selected top-first signature arguments. -/
theorem decodeCheckMultiSigOperandsFor_multi
    {threshold : Nat} {keys : List PubKey} {signatures rest : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold) :
    decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest) =
      .ok {
        pubkeys := (keys.map (fun key => key.bytes)).reverse
        signatures := signatures
        dummy := some falseElement
        rest := rest } := by
  have decodeKeys := decodeScriptNum_scriptNat_multi_count keys.length flags
    keyBound
  have decodeThreshold := decodeScriptNum_scriptNat_multi_count threshold flags
    (Nat.le_trans thresholdBound keyBound)
  unfold decodeCheckMultiSigOperandsFor
  simp only [if_neg version]
  simp [decodeCheckMultiSigOperands]
  rw [exceptOkBind]
  rw [decodeKeys]
  rw [exceptOkBind]
  simp only [Int.ofNat_eq_natCast] at *
  simp [maxPubKeysPerMultiSig] at keyBound
  have keyNonnegative : ¬ ((keys.length : Int) < 0) := by omega
  have keyWithinLimit : ¬ ((20 : Int) < (keys.length : Int)) := by omega
  have thresholdNonnegative : ¬ ((threshold : Int) < 0) := by omega
  have thresholdWithinKeys : ¬ (keys.length < threshold) := by omega
  have enoughSignatures :
      ¬ ((threshold : Int) + (rest.length + 1) < threshold) := by omega
  simp [decodeThreshold, exceptOkBind, maxPubKeysPerMultiSig, signatureCount,
    keyNonnegative, keyWithinLimit, thresholdNonnegative, thresholdWithinKeys,
    enoughSignatures]

/-- A legacy `multi` consumes the selected signatures followed by the
    canonical historical dummy. Signature and public-key lists are both in
    the top-first order used by the evaluator. Failed checks require NULLFAIL;
    the canonical dummy discharges NULLDUMMY internally. -/
theorem BExecution.multi
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {result : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok result)
    (allowed : result = true ∨ nullFailSatisfied flags signatures) :
    BExecution (.multi threshold keys) (signatures ++ [falseElement])
      (boolToElement result) flags ctx := by
  intro rest altStack
  let operands : CheckMultiSigOperands := {
    pubkeys := (keys.map (fun key => key.bytes)).reverse
    signatures := signatures
    dummy := some falseElement
    rest := rest }
  have decoded : decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest) =
      .ok operands := by
    exact decodeCheckMultiSigOperandsFor_multi version keyBound thresholdBound
      signatureCount
  have dummyOk : checkMultiSigDummy flags (some falseElement) = .ok () := by
    simp [checkMultiSigDummy, nullDummySatisfied, stackElementEq, falseElement]
  have checked' : checkMultiSigFor checkSig flags ctx operands.signatures
      operands.pubkeys = .ok result := checked
  have checkExec : Eval [.op .OP_CHECKMULTISIG]
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: signatures ++ falseElement :: rest)
      altStack flags ctx
      (.success (boolToElement result :: rest) altStack) := by
    cases result with
    | false =>
        have nullFail : nullFailSatisfied flags signatures := by
          rcases allowed with impossible | satisfied
          · simp at impossible
          · exact satisfied
        simpa [operands, boolToElement] using
          (Eval.checkmultisig_failure
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx
            (.success (falseElement :: rest) altStack)
            decoded checked' nullFail dummyOk Eval.done)
    | true =>
        simpa [operands, boolToElement] using
          (Eval.checkmultisig_success
            (scriptNat keys.length ::
              (keys.map (fun key => key.bytes)).reverse ++
              scriptNat threshold :: signatures ++ falseElement :: rest)
            operands [] altStack flags ctx
            (.success (trueElement :: rest) altStack)
            decoded checked' dummyOk Eval.done)
  have keyExec := compileKeyPushes_execution keys flags ctx
    (scriptNat threshold :: signatures ++ falseElement :: rest) altStack
  have tailExec : Eval
      (compileKeyPushes keys ++ [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      (scriptNat threshold :: signatures ++ falseElement :: rest)
      altStack flags ctx
      (.success (boolToElement result :: rest) altStack) := by
    have pushedCount : Eval [.pushNum keys.length, .op .OP_CHECKMULTISIG]
        ((keys.map (fun key => key.bytes)).reverse ++
          (scriptNat threshold :: signatures ++ falseElement :: rest))
        altStack flags ctx
        (.success (boolToElement result :: rest) altStack) := by
      simpa [List.append_assoc] using
        (Eval.pushNum keys.length [.op .OP_CHECKMULTISIG]
          ((keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: signatures ++ falseElement :: rest)
          altStack flags ctx _ checkExec)
    exact Eval.append keyExec pushedCount
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    List.append_assoc] using
    (Eval.pushNum threshold
      (compileKeyPushes keys ++ [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      (signatures ++ falseElement :: rest) altStack flags ctx _ tailExec)

/-- The false branch of legacy `multi` exposes the NULLFAIL premise directly. -/
theorem BExecution.multiFalse
    {threshold : Nat} {keys : List PubKey} {signatures : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (signatureCount : signatures.length = threshold)
    (checked : checkMultiSigFor checkSig flags ctx signatures
      ((keys.map (fun key => key.bytes)).reverse) = .ok false)
    (nullFail : nullFailSatisfied flags signatures) :
    BExecution (.multi threshold keys) (signatures ++ [falseElement])
      falseElement flags ctx := by
  simpa [boolToElement] using BExecution.multi version keyBound thresholdBound
    signatureCount checked (Or.inr nullFail)

/-- The canonical legacy `multi` dissatisfaction uses only empty signatures,
    so its failed check always satisfies NULLFAIL. -/
theorem multi_dissatisfaction_execution
    {threshold : Nat} {keys : List PubKey}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion ≠ .tapscript)
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (checked : checkMultiSigFor checkSig flags ctx
      (List.replicate threshold falseElement)
      ((keys.map (fun key => key.bytes)).reverse) = .ok false) :
    BExecution (.multi threshold keys)
      (List.replicate threshold falseElement ++ [falseElement])
      falseElement flags ctx := by
  have nullFail : nullFailSatisfied flags
      (List.replicate threshold falseElement) := by
    right
    intro signature member
    have equal : signature = falseElement := List.eq_of_mem_replicate member
    subst signature
    rfl
  exact BExecution.multiFalse version keyBound thresholdBound
    (by simp) checked nullFail

/-! ## Tapscript multisignature execution -/

/-- Exact execution evidence for the CHECKSIGADD tail of `multi_a`. Keys and
    signatures are both in source execution order. Every step retains the
    Tapscript count decoder and version-aware signature-check result as
    explicit premises, while the accumulator is an `Int`. -/
inductive CheckSigAddTailExecution (flags : ScriptFlags) (ctx : TxContext) :
    Int → List PubKey → Stack → Int → Prop where
  | nil (count : Int) :
      CheckSigAddTailExecution flags ctx count [] [] count
  | cons {count total : Int} {key : PubKey} {keys : List PubKey}
      {signature : StackElement} {signatures : Stack} {truth : Bool}
      (decoded : decodeCheckSigAddCount flags ctx (scriptNum count) = .ok count)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        signature key.bytes = .ok truth)
      (tail : CheckSigAddTailExecution flags ctx
        (count + Int.ofNat truth.toNat) keys signatures total) :
      CheckSigAddTailExecution flags ctx count (key :: keys)
        (signature :: signatures) total

/-- A CHECKSIGADD tail consumes source-order signatures below its accumulator
    and leaves the exact final canonical Script-number while preserving both
    surrounding stacks. -/
theorem CheckSigAddTailExecution.executes
    {flags : ScriptFlags} {ctx : TxContext} {count total : Int}
    {keys : List PubKey} {signatures : Stack}
    (executed : CheckSigAddTailExecution flags ctx count keys signatures total) :
    ExecutesStackFrame (compileCheckSigAddTail keys)
      (scriptNum count :: signatures) [scriptNum total] flags ctx := by
  induction executed with
  | nil count =>
      intro rest altStack
      exact Eval.done
  | @cons count total key keys signature signatures truth decoded checked tail ih =>
      intro rest altStack
      apply Eval.pushData
      cases truth with
      | false =>
          apply Eval.checksigadd_failure (count := count)
          · exact decoded
          · exact checked
          · simpa using ih rest altStack
      | true =>
          apply Eval.checksigadd_success (count := count)
          · exact decoded
          · exact checked
          · simpa using ih rest altStack

/-- The nonempty CHECKSIG/CHECKSIGADD compiler consumes one source-order
    signature per source-order key and exposes the tail's exact accumulator. -/
theorem compileCheckSigAdd_execution
    {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total) :
    ExecutesStackFrame (compileCheckSigAdd (firstKey :: keys))
      (firstSignature :: signatures) [scriptNum total] flags ctx := by
  intro rest altStack
  apply Eval.pushData
  cases firstTruth with
  | false =>
      apply Eval.checksig_failure
      · exact checked
      · simpa [compileCheckSigAddTail, List.append_assoc, scriptNum_zero] using
          tail.executes rest altStack
  | true =>
      apply Eval.checksig_success
      · exact checked
      · simpa [compileCheckSigAddTail, List.append_assoc, scriptNum_one] using
          tail.executes rest altStack

/-- A nonempty `multi_a` executes only under the explicit Tapscript boundary,
    computes the CHECKSIG/CHECKSIGADD accumulator, then compares it numerically
    with the threshold. Both accumulator and final NUMEQUAL decodes remain
    explicit rather than being inferred from well-formedness. -/
theorem BExecution.multiA
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (_version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total)) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures)
      (boolToElement (Int.ofNat threshold == total)) flags ctx := by
  have children := compileCheckSigAdd_execution checked tail
  have comparison : ExecutesStackFrame [.pushNum threshold, .op .OP_NUMEQUAL]
      [scriptNum total] [boolToElement (Int.ofNat threshold == total)]
      flags ctx := by
    intro rest altStack
    exact Eval.pushNum threshold [.op .OP_NUMEQUAL] (scriptNum total :: rest)
      altStack flags ctx _
      (Eval.numequal (scriptNat threshold) (scriptNum total)
        (Int.ofNat threshold) total rest [] altStack flags ctx _ decoded Eval.done)
  have complete := ExecutesStackFrame.append children comparison
  simpa [BExecution, compile, compileWithKeyHash] using complete

/-- Expose the requested Boolean result of the final NUMEQUAL comparison. -/
theorem BExecution.multiAOutcome
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth expected : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = expected) :
    BExecutionOutcome (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) expected flags ctx := by
  refine ⟨boolToElement (Int.ofNat threshold == total),
    BExecution.multiA version checked tail decoded, ?_⟩
  exact (castToBool_boolToElement _).trans comparison

/-- A final equality result gives the exact canonical true B result. -/
theorem BExecution.multiATrue
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = true) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) trueElement flags ctx := by
  have executed := BExecution.multiA version checked tail decoded
  rw [comparison] at executed
  exact executed

/-- A failed final numeric equality gives the exact canonical false B result. -/
theorem BExecution.multiAFalse
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {firstSignature : StackElement} {signatures : Stack}
    {firstTruth : Bool} {total : Int}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      firstSignature firstKey.bytes = .ok firstTruth)
    (tail : CheckSigAddTailExecution flags ctx
      (Int.ofNat firstTruth.toNat) keys signatures total)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      (scriptNum total) = .ok (Int.ofNat threshold, total))
    (comparison : (Int.ofNat threshold == total) = false) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (firstSignature :: signatures) falseElement flags ctx := by
  have executed := BExecution.multiA version checked tail decoded
  rw [comparison] at executed
  exact executed

/-- Empty signatures keep a CHECKSIGADD tail accumulator at zero. The exact
    empty-signature encoding result stays explicit for every key. -/
theorem CheckSigAddTailExecution.allFalse
    {flags : ScriptFlags} {ctx : TxContext} (keys : List PubKey)
    (version : ctx.sigVersion = .tapscript)
    (checked : ∀ key ∈ keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        falseElement key.bytes = .ok false) :
    CheckSigAddTailExecution flags ctx 0 keys
      (List.replicate keys.length falseElement) 0 := by
  induction keys with
  | nil => exact .nil 0
  | cons key keys ih =>
      rw [List.length_cons, List.replicate_succ]
      apply CheckSigAddTailExecution.cons (truth := false)
      · simp only [decodeCheckSigAddCount, version, ne_eq,
          not_true_eq_false, ↓reduceIte, scriptNum_zero]
        cases flags.minimalData <;> rfl
      · exact checked key (by simp)
      · simpa using ih (fun child member => checked child (by simp [member]))

/-- The canonical all-empty `multi_a` dissatisfaction stays at accumulator
    zero and returns false for every positive threshold. -/
theorem multiA_dissatisfaction_execution
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {flags : ScriptFlags} {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript)
    (positive : threshold ≠ 0)
    (firstChecked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      falseElement firstKey.bytes = .ok false)
    (tailChecked : ∀ key ∈ keys,
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx
        falseElement key.bytes = .ok false)
    (decoded : decodeBinaryScriptNums flags (scriptNat threshold)
      falseElement = .ok (Int.ofNat threshold, 0)) :
    BExecution (.multi_a threshold (firstKey :: keys))
      (List.replicate (firstKey :: keys).length falseElement)
      falseElement flags ctx := by
  have tail := CheckSigAddTailExecution.allFalse keys version tailChecked
  have executed := BExecution.multiA (threshold := threshold) version
    firstChecked tail decoded
  simpa [List.replicate_succ, boolToElement, positive] using executed

end LeanMiniscript.Miniscript
