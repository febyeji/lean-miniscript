import LeanMiniscript.Script.RuntimeCompletenessProofs
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Miniscript.WitnessBudgetProofs

namespace LeanMiniscript.Script.RuntimeCompletenessExamples

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty, sigVersion := .tapscript }
private def oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)
private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩
private def run (script : Script) (stack : Stack) (weight : Nat) : WeightedResult :=
  evaluateWithRuntimeLimits oracle script stack [] {} ctx weight

-- All three signature opcodes debit the same 50 units. The final CHECKSIGADD
-- reaches the exact budget boundary after the preceding two checks succeed.
private def signatures : Script :=
  [.pushData (bytes 64), .pushData (bytes 32), .op .OP_CHECKSIGVERIFY,
   .pushData (bytes 64), .pushData (bytes 32), .op .OP_CHECKSIG, .op .OP_DROP,
   .pushData (bytes 64), .pushNum 0, .pushData (bytes 32), .op .OP_CHECKSIGADD]

example : staticValidationWeight signatures = 150 ∧
    run signatures [] (staticValidationWeight signatures) = .success [trueElement] [] 0 ∧
    run signatures [] 149 = .failure .tapscriptValidationWeight := by native_decide

-- The source bound deliberately includes empty signatures, which debit zero.
example : staticValidationWeight [.op .OP_CHECKSIG] = 50 ∧
    run [.op .OP_CHECKSIG] [bytes 32, ByteArray.empty] 0 =
      .success [falseElement] [] 0 := by native_decide

-- An outer inactive branch contains nested IF/NOTIF and repeated ELSEs.
-- Restoring it preserves the selected result and the entire unused budget.
private def nested : Script :=
  [.op .OP_IF, .op .OP_IF, .op .OP_CHECKSIG,
   .op .OP_ELSE, .op .OP_CHECKSIGVERIFY, .op .OP_ELSE, .op .OP_NOTIF,
   .op .OP_CHECKSIGADD, .op .OP_ENDIF, .op .OP_ENDIF,
   .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF]

example : staticValidationWeight nested = 150 ∧
    run nested [falseElement] (staticValidationWeight nested) =
      .success [trueElement] [] 150 := by native_decide

-- A selected nested NOTIF executes while its ELSE signature is skipped.
private def selectedNested : Script :=
  [.op .OP_IF, .pushNum 0, .op .OP_NOTIF, .pushNum 1,
   .op .OP_ELSE, .op .OP_CHECKSIG, .op .OP_ENDIF, .op .OP_ENDIF]

example : run selectedNested [trueElement] (staticValidationWeight selectedNested) =
    .success [trueElement] [] 50 := by native_decide

-- Projected execution alone omits this 521-byte push; source completion
-- additionally needs the push bound on the inactive branch.
private def skippedPush (size : Nat) : Script :=
  [.op .OP_IF, .pushData (bytes size), .op .OP_ENDIF, .pushNum 1]

example : (match evaluate oracle (skippedPush 521) [falseElement] [] {} ctx with
      | .success stack alt => stack == [trueElement] && alt.isEmpty
      | .failure _ => false) = true ∧
    run (skippedPush 521) [falseElement] 0 = .failure .pushSize ∧
    run (skippedPush 520) [falseElement] 0 = .success [trueElement] [] 0 := by native_decide

-- Sufficient weight preserves ordinary operand errors. CHECKSIGADD's count
-- decoding still precedes the debit and cryptographic verification.
example : run [.op .OP_CHECKSIGADD] [bytes 32, bytes 5, bytes 64] 50 =
    .failure .scriptNumOverflow := by native_decide

-- The active-path theorem accepts zero weight for the inactive nested checks.
private theorem nestedResources :
    EvalResources nested [falseElement] [] {} ctx [trueElement] []
      { peakStackItems := 1, executedMultiSigKeys := 0, signatureWeight := 0 } := by
  let frame : ConditionalFrame :=
    { branches := [
        [.op .OP_IF, .op .OP_CHECKSIG, .op .OP_ELSE, .op .OP_CHECKSIGVERIFY,
         .op .OP_ELSE, .op .OP_NOTIF, .op .OP_CHECKSIGADD, .op .OP_ENDIF,
         .op .OP_ENDIF], [.pushNum 1]], after := [] }
  have selected : EvalResources [.pushNum 1] [] [] {} ctx [trueElement] []
      { peakStackItems := 1, executedMultiSigKeys := 0, signatureWeight := 0 } := by
    simpa [ExecutionResources.prepend, ExecutionResources.initial,
      executedMultiSigKeyCharge, executedSignatureWeight] using
      EvalResources.step (Eval.pushNum 1 [] [] [] {} ctx _ Eval.done)
        (EvalResources.empty [trueElement] [] {} ctx)
  have observed := EvalResources.if_execute (frame := frame)
    (show splitConditional nested.tail = some frame by rfl)
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg)
    (show EvalResources (frame.select (castToBool falseElement)) [] [] {} ctx
      [trueElement] [] _ from selected)
  simpa [nested, ExecutionResources.prepend] using observed

example (modelOracle : CryptoOracle) (agreement : modelOracle.RefinesModel) :
    evaluateWithRuntimeLimits modelOracle nested [falseElement] [] {} ctx 0 =
      .success [trueElement] [] 0 := by
  obtain ⟨remaining, completed, spent⟩ := nestedResources.runtime_complete_exact agreement
    (by simp [nested, ScriptElement.pushSize, maxScriptElementSize]; decide) (by decide) 0 (by decide)
  have zero : remaining = 0 := by simpa using spent
  simpa [zero] using completed

-- One checked signature exhausts exactly 50 units in the proved resource path.
example (modelOracle : CryptoOracle) (agreement : modelOracle.RefinesModel)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig {} ctx
      (bytes 64) (bytes 32) = .ok true) :
    evaluateWithRuntimeLimits modelOracle [.op .OP_CHECKSIG]
      [bytes 32, bytes 64] [] {} ctx 50 = .success [trueElement] [] 0 := by
  have head : Eval [.op .OP_CHECKSIG] [bytes 32, bytes 64] [] {} ctx
      (.success [trueElement] []) :=
    .checksig_success _ _ [] [] [] {} ctx _ checked Eval.done
  have observed : EvalResources [.op .OP_CHECKSIG] [bytes 32, bytes 64] [] {} ctx
      [trueElement] []
      { peakStackItems := 2, executedMultiSigKeys := 0, signatureWeight := 50 } := by
    simpa [ExecutionResources.prepend, ExecutionResources.initial, executedMultiSigKeyCharge,
      executedSignatureWeight, signatureValidationWeight, validationWeightPerSigop,
      ctx, bytes, ByteArray.size] using
      EvalResources.step head (EvalResources.empty [trueElement] [] {} ctx)
  obtain ⟨remaining, completed, spent⟩ := observed.runtime_complete_exact agreement
    (by simp [ScriptElement.pushSize, maxScriptElementSize]) (by decide) 50 (by decide)
  have zero : remaining = 0 := by simpa using spent
  simpa [zero] using completed

-- multi_a visits all three keys, but its empty middle signature costs nothing.
private def twoOfThree : Script :=
  LeanMiniscript.Miniscript.compile (.multi_a 2
    [⟨bytes 32⟩, ⟨bytes 32⟩, ⟨bytes 32⟩])

example : staticValidationWeight twoOfThree = 150 ∧
    run twoOfThree [bytes 64, falseElement, bytes 64] 100 =
      .success [trueElement] [] 0 ∧
    run twoOfThree [bytes 64, falseElement, bytes 64] 99 =
      .failure .tapscriptValidationWeight := by native_decide

-- CompactSize overhead is included when signature payloads fund a full witness.
example : initialValidationWeight [bytes 64, falseElement, bytes 64, bytes 104, bytes 33] = 321 := by
  native_decide

example : 100 ≤ initialValidationWeight [bytes 64, falseElement, bytes 64, bytes 104, bytes 33] := by
  apply LeanMiniscript.Miniscript.Witness.signatureWeight_le_initialValidationWeight
    (arguments := [bytes 64, falseElement, bytes 64])
  · exact List.sublist_append_left _ _
  · decide

-- The satisfier chooses the short branch. The serialized witness budget is
-- smaller than the source-wide bound because twenty signature checks are skipped.
private def branchFragment : LeanMiniscript.Miniscript.CoreFragment :=
  .or_i (.c (.pk_k ⟨bytes 32⟩)) (.multi_a 1 (List.replicate 20 ⟨bytes 32⟩))

private def signingEnv : LeanMiniscript.Miniscript.SatEnv :=
  { signatureFor := fun _ => some (bytes 64)
    preimageFor := fun _ => none
    nonPreimageFor := fun _ => bytes 32
    txCtx := ctx }

private def generatedBranchCompletes : Bool :=
  match LeanMiniscript.Miniscript.satisfyFinal branchFragment signingEnv,
      serializeScript (LeanMiniscript.Miniscript.compile branchFragment) with
  | some arguments, .ok scriptBytes =>
      let weight := initialValidationWeight (arguments ++ [scriptBytes, bytes 33])
      arguments == [bytes 64, trueElement] &&
        weight < staticValidationWeight (LeanMiniscript.Miniscript.compile branchFragment) &&
        (run (LeanMiniscript.Miniscript.compile branchFragment) arguments.toInitialStack weight ==
          .success [trueElement] [] (weight - 50))
  | _, _ => false

example : generatedBranchCompletes = true := by native_decide

-- A generated threshold witness has two signatures and one empty dissatisfaction.
-- Its a: wrappers preserve the partial count without spending extra weight.
private def thresholdFragment : LeanMiniscript.Miniscript.CoreFragment :=
  .thresh 2 [.c (.pk_k ⟨bytes 32⟩), .a (.c (.pk_k ⟨bytes 32⟩)),
    .a (.c (.pk_k ⟨bytes 32⟩))]

example : (match LeanMiniscript.Miniscript.satisfyFinal thresholdFragment signingEnv with
  | some arguments =>
      run (LeanMiniscript.Miniscript.compile thresholdFragment) arguments.toInitialStack 100 ==
        .success [trueElement] [] 0 &&
      run (LeanMiniscript.Miniscript.compile thresholdFragment) arguments.toInitialStack 99 ==
        .failure .tapscriptValidationWeight
  | none => false) = true := by native_decide

end LeanMiniscript.Script.RuntimeCompletenessExamples
