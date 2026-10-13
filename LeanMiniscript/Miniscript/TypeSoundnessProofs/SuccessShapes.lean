import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.ExecutionDecomposition

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type soundness: successful opcode-sequence shapes

Inversion lemmas describing the stack shape after a successful run of each
compiled opcode sequence used by the base-type proof.

Some helper lemmas here were `private` in the former single-file
`TypeSoundnessProofs` module. They are visible only so that sibling
submodules can use them; treat them as internal proof helpers, not stable API.
-/

/-- A successful run cannot share its input state with a failing run. -/
private theorem Eval.success_failure_absurd
    {script : Script} {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
    (run : Eval script stack altStack flags ctx (.success out outAlt))
    (failed : Eval script stack altStack flags ctx (.failure error)) :
    False := by
  cases Eval.result_unique run failed

/-- A successful run has the one-result shape of a canonical run on the same
    input that leaves one element above `rest` and preserves the alternate
    stack. -/
private theorem Eval.oneResult_of_canonical
    {script : Script} {stack altStack rest finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : StackElement}
    (run : Eval script stack altStack flags ctx (.success finalStack finalAlt))
    (canonical : Eval script stack altStack flags ctx
      (.success (result :: rest) altStack)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases Eval.result_unique run canonical
  exact ⟨rfl, result, rfl⟩

/-- A successful standalone CHECKSIG consumes its key/signature pair, leaves
    one boolean result, and preserves the alternate stack. -/
theorem Eval.checkSigSingle_success_shape
    {key signature : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIG] (key :: signature :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key with
  | error error =>
      exact (Eval.success_failure_absurd run
        (Eval.checksig_encoding_failure key signature rest [] altStack flags
          ctx error checked)).elim
  | ok valid =>
      cases valid with
      | false =>
          exact Eval.oneResult_of_canonical run
            (Eval.checksigFalse checked Eval.done)
      | true =>
          exact Eval.oneResult_of_canonical run
            (Eval.checksigTrue checked Eval.done)

/-- A successful standalone 0NOTEQUAL leaves one normalized boolean and
    preserves the alternate stack. -/
theorem Eval.zeroNotEqualSingle_success_shape
    {operand : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_0NOTEQUAL] (operand :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes with
  | error error =>
      exact (Eval.success_failure_absurd run
        (Eval.unary_scriptnum_failure operand rest [] altStack flags ctx error
          decoded)).elim
  | ok value =>
      exact Eval.oneResult_of_canonical run
        (Eval.zeroNotEqual operand value rest altStack [] flags ctx _ decoded
          Eval.done)

/-- Successful standalone VERIFY consumes its true operand and preserves the
    alternate stack. -/
theorem Eval.verifySingle_success_shape
    {operand : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_VERIFY] (operand :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalStack = rest ∧ finalAlt = altStack := by
  cases truth : castToBool operand with
  | false =>
      exact (Eval.success_failure_absurd run (Eval.verifyFalse truth)).elim
  | true =>
      cases Eval.result_unique run (Eval.verifyTrue truth Eval.done)
      exact ⟨rfl, rfl⟩

/-- Successful standalone BOOLAND execution leaves one boolean and preserves
    the alternate stack. -/
theorem Eval.boolAndSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] (first :: second :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      exact (Eval.success_failure_absurd run
        (Eval.binaryScriptNumFailure (opcode := .OP_BOOLAND) rfl decoded)).elim
  | ok values =>
      exact Eval.oneResult_of_canonical run
        (Eval.booland first second values.1 values.2 rest [] altStack flags
          ctx _ decoded Eval.done)

/-- Successful standalone BOOLOR execution leaves one boolean and preserves
    the alternate stack. -/
theorem Eval.boolOrSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLOR] (first :: second :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      exact (Eval.success_failure_absurd run
        (Eval.binaryScriptNumFailure (opcode := .OP_BOOLOR) rfl decoded)).elim
  | ok values =>
      exact Eval.oneResult_of_canonical run
        (Eval.boolor first second values.1 values.2 rest [] altStack flags
          ctx _ decoded Eval.done)

/-- Successful standalone ADD execution leaves one accumulator and preserves
    the alternate stack. -/
theorem Eval.addSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_ADD] (first :: second :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      exact (Eval.success_failure_absurd run
        (Eval.binaryScriptNumFailure (opcode := .OP_ADD) rfl decoded)).elim
  | ok values =>
      exact Eval.oneResult_of_canonical run
        (Eval.add first second values.1 values.2 rest [] altStack flags ctx
          _ decoded Eval.done)

/-- Pushing a threshold and comparing it with an accumulator leaves one
    boolean result. -/
theorem Eval.pushNumEqual_success_shape
    {threshold : Nat} {accumulator : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum threshold, .op .OP_EQUAL]
      (accumulator :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  by_cases equal : scriptNum threshold = accumulator
  · exact Eval.oneResult_of_canonical run (Eval.pushNum _ _ _ _ _ _ _
      (Eval.equal_true _ _ _ [] _ _ _ _ equal Eval.done))
  · exact Eval.oneResult_of_canonical run (Eval.pushNum _ _ _ _ _ _ _
      (Eval.equal_false _ _ _ [] _ _ _ _ equal Eval.done))

/-- Successful standalone CHECKSIGADD leaves one updated accumulator. -/
private theorem Eval.checkSigAddSingle_success_shape
    {pubkey count signature : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIGADD]
      (pubkey :: count :: signature :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  generalize resultEq : ExecResult.success finalStack finalAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case checksigadd_success =>
      rename_i countValue decoded checked next
      cases resultEq
      have equal := Eval.result_unique next
        (Eval.done (stack := scriptNum (countValue + 1) :: rest)
          (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩
  case checksigadd_failure =>
      rename_i countValue decoded checked next
      cases resultEq
      have equal := Eval.result_unique next
        (Eval.done (stack := scriptNum countValue :: rest)
          (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩
  all_goals cases resultEq

/-- Pushing a threshold and applying NUMEQUAL leaves one boolean result. -/
theorem Eval.pushNumNumEqual_success_shape
    {threshold : Nat} {accumulator : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum threshold, .op .OP_NUMEQUAL]
      (accumulator :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  have pushed : Eval [.pushNum threshold] (accumulator :: rest) altStack
      flags ctx (.success (scriptNum threshold :: accumulator :: rest)
        altStack) := by
    apply Eval.pushNum
    exact Eval.done
  obtain ⟨middle, middleAlt, pushRun, compareRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) run
  have pushEq := Eval.result_unique pushRun pushed
  cases pushEq
  cases decoded : decodeBinaryScriptNums flags (scriptNum threshold)
      accumulator with
  | error error =>
      exact (Eval.success_failure_absurd compareRun
        (Eval.binaryScriptNumFailure (opcode := .OP_NUMEQUAL) rfl decoded)).elim
  | ok values =>
      exact Eval.oneResult_of_canonical compareRun
        (Eval.numequal _ _ values.1 values.2 rest [] altStack flags ctx _
          decoded Eval.done)

/-- Expand a successful EQUALVERIFY back into EQUAL followed by VERIFY. -/
private theorem Eval.unfuseEqualVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_EQUALVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_EQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case equalverify_success =>
      rename_i first second rest equal next
      cases resultEq
      exact Eval.equal_true first second rest [.op .OP_VERIFY] altStack flags ctx
        _ equal (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful CHECKSIGVERIFY back into CHECKSIG followed by VERIFY. -/
private theorem Eval.unfuseCheckSigVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIGVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case checksigverify_success =>
      rename_i pubkey signature rest checked next
      cases resultEq
      exact Eval.checksigTrue checked (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful CHECKMULTISIGVERIFY back into CHECKMULTISIG followed
    by VERIFY. -/
private theorem Eval.unfuseCheckMultiSigVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKMULTISIGVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_CHECKMULTISIG, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case checkmultisigverify_success =>
      rename_i operands dummy checked decoded next
      cases resultEq
      exact Eval.checkmultisig_success stack operands [.op .OP_VERIFY]
        altStack flags ctx _ decoded checked dummy (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful NUMEQUALVERIFY back into NUMEQUAL followed by VERIFY. -/
private theorem Eval.unfuseNumEqualVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_NUMEQUALVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_NUMEQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case numequalverify_success =>
      rename_i first second firstValue secondValue rest equal decoded next
      cases resultEq
      apply Eval.numequal first second firstValue secondValue rest
        [.op .OP_VERIFY] altStack flags ctx _ decoded
      have comparison : (firstValue == secondValue) = true := by
        simp [equal]
      rw [comparison]
      exact Eval.verifyTrue rfl next
  all_goals cases resultEq

/-- Successful optimized VERIFY compilation can be expanded to the original
    balanced script followed by an explicit VERIFY. -/
theorem Eval.compileVerify_success_inverse
    {script : Script} {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow script)
    (run : Eval (compileVerify script) stack altStack flags ctx
      (.success out outAlt)) :
    Eval (script ++ [.op .OP_VERIFY]) stack altStack flags ctx
      (.success out outAlt) := by
  induction balanced generalizing stack altStack out outAlt with
  | nil => simpa using run
  | @atom element nonConditional =>
      cases element with
      | pushData data =>
          simpa [compileVerify, verifyReplacement?] using run
      | pushNum number =>
          simpa [compileVerify, verifyReplacement?] using run
      | op opcode =>
          cases opcode <;>
            simp [compileVerify, verifyReplacement?] at run ⊢
          all_goals first
            | exact Eval.unfuseEqualVerify_success run
            | exact Eval.unfuseCheckSigVerify_success run
            | exact Eval.unfuseCheckMultiSigVerify_success run
            | exact Eval.unfuseNumEqualVerify_success run
            | exact run
  | @append left right leftBalanced rightBalanced leftIH rightIH =>
      rcases List.eq_nil_or_concat right with rfl | ⟨initScript, last, rfl⟩
      · have expanded := leftIH (by simpa using run)
        simpa using expanded
      · simp only [List.concat_eq_append] at run rightBalanced rightIH ⊢
        have normalized : Eval
            (left ++ compileVerify (initScript ++ [last])) stack altStack
            flags ctx (.success out outAlt) := by
          rw [compileVerify_append_singleton]
          rw [← List.append_assoc] at run
          rw [compileVerify_append_singleton] at run
          cases replacementEq : verifyReplacement? last <;>
            simp [replacementEq, List.append_assoc] at run ⊢
          all_goals exact run
        obtain ⟨middle, middleAlt, leftRun, rightRun⟩ :=
          Eval.splitBalancedAppend_success leftBalanced normalized
        have expandedRight := rightIH rightRun
        simpa [List.append_assoc] using Eval.append leftRun expandedRight
  | @ifThen body bodyBalanced bodyIH =>
      change Eval
        ((([.op .OP_IF] ++ body) ++ [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifThen body bodyBalanced bodyIH =>
      change Eval
        ((([.op .OP_NOTIF] ++ body) ++ [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        ((([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
          [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        ((([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
          [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run

/-- CHECKSIGADD helper compilation contains no control-flow delimiters. -/
private theorem compileCheckSigAddTail_balancedControlFlow
    (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append
        (.append (.atom (by simp [NonConditional]))
          (.atom (by simp [NonConditional]))) ih

/-- Nonempty CHECKSIGADD compilation is balanced. -/
theorem compileCheckSigAdd_balancedControlFlow
    (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAdd keys) := by
  cases keys with
  | nil => exact .atom (by simp [NonConditional])
  | cons key keys =>
      exact .append
        (.append (.atom (by simp [NonConditional]))
          (.atom (by simp [NonConditional])))
        (compileCheckSigAddTail_balancedControlFlow keys)

/-- A successful CHECKSIGADD tail consumes a prefix of signatures below its
    incoming accumulator and leaves one accumulator. -/
private theorem Eval.compileCheckSigAddTail_success_shape
    (keys : List PubKey) {accumulator : StackElement}
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compileCheckSigAddTail keys) (accumulator :: stack)
      altStack flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  induction keys generalizing accumulator stack altStack finalStack finalAlt with
  | nil =>
      have equal := Eval.result_unique run
        (Eval.done (stack := accumulator :: stack) (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨[], stack, accumulator, rfl, rfl⟩⟩
  | cons key keys ih =>
      have combined : Eval
          ([.pushData key] ++
            ([.op .OP_CHECKSIGADD] ++ compileCheckSigAddTail keys))
          (accumulator :: stack) altStack flags ctx
          (.success finalStack finalAlt) := by
        simpa [compileCheckSigAddTail, List.append_assoc] using run
      obtain ⟨afterPush, afterPushAlt, pushRun, tailRun⟩ :=
        Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) combined
      obtain ⟨afterCheck, afterCheckAlt, checkRun, restRun⟩ :=
        Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) tailRun
      have canonicalPush : Eval [.pushData key] (accumulator :: stack)
          altStack flags ctx
          (.success (key :: accumulator :: stack) altStack) :=
        Eval.pushDataNext Eval.done
      have pushEq := Eval.result_unique pushRun canonicalPush
      cases pushEq
      cases stack with
      | nil =>
          cases checkRun <;>
            simp_all [Opcode.isUpgradeableNop]
      | cons signature rest =>
          obtain ⟨checkAlt, nextAccumulator, checkEq⟩ :=
            Eval.checkSigAddSingle_success_shape checkRun
          subst afterCheckAlt
          rw [checkEq] at restRun
          obtain ⟨tailAlt, tailArgs, finalRest, result, tailInput,
              finalEq⟩ := ih restRun
          rw [tailInput, finalEq]
          exact ⟨tailAlt,
            ⟨signature :: tailArgs, finalRest, result, by simp, rfl⟩⟩

/-- A successful nonempty CHECKSIGADD multisig body consumes a prefix of
    signatures and leaves one accumulator. -/
theorem Eval.compileCheckSigAdd_success_shape
    (firstKey : PubKey) (keys : List PubKey)
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compileCheckSigAdd (firstKey :: keys)) stack altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  have combined : Eval
      ([.pushData firstKey] ++
        ([.op .OP_CHECKSIG] ++ compileCheckSigAddTail keys))
      stack altStack flags ctx (.success finalStack finalAlt) := by
    simpa [compileCheckSigAdd, List.append_assoc] using run
  obtain ⟨afterPush, afterPushAlt, pushRun, tailRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) combined
  obtain ⟨afterCheck, afterCheckAlt, checkRun, restRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) tailRun
  have canonicalPush : Eval [.pushData firstKey] stack altStack flags ctx
      (.success (firstKey :: stack) altStack) := Eval.pushDataNext Eval.done
  have pushEq := Eval.result_unique pushRun canonicalPush
  cases pushEq
  cases stack with
  | nil =>
      have failed := Eval.fixedArityStackUnderflow_result
        (opcode := .OP_CHECKSIG) (required := 2) (arity := rfl)
        (underflow := by simp) checkRun
      contradiction
  | cons signature rest =>
      obtain ⟨checkAlt, accumulator, checkEq⟩ :=
        Eval.checkSigSingle_success_shape checkRun
      subst afterCheckAlt
      rw [checkEq] at restRun
      obtain ⟨tailAlt, tailArgs, finalRest, result, tailInput, finalEq⟩ :=
        Eval.compileCheckSigAddTail_success_shape keys restRun
      rw [tailInput, finalEq]
      exact ⟨tailAlt,
        ⟨signature :: tailArgs, finalRest, result, by simp, rfl⟩⟩

/-- A successful legacy multisignature decode over the compiler's canonical
    key/count prefix consumes exactly the threshold signatures and one dummy. -/
private theorem decodeCheckMultiSigOperandsFor_compiled_shape
    {threshold : Nat} {keys : List PubKey} {stack : Stack}
    {operands : CheckMultiSigOperands}
    {flags : ScriptFlags} {ctx : TxContext}
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (decoded : decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack) = .ok operands)
    (dummyOk : checkMultiSigDummy flags operands.dummy = .ok ()) :
    ∃ signatures dummy rest,
      stack = signatures ++ dummy :: rest ∧
      signatures.length = threshold ∧ operands.rest = rest := by
  have decodeKeys := decodeScriptNum_scriptNat_multi_count keys.length flags
    keyBound
  have decodeThreshold := decodeScriptNum_scriptNat_multi_count threshold flags
    (Nat.le_trans thresholdBound keyBound)
  unfold decodeCheckMultiSigOperandsFor at decoded
  split at decoded
  · contradiction
  · simp only [decodeCheckMultiSigOperands, bind, Except.bind] at decoded
    simp at decoded
    rw [decodeKeys] at decoded
    have keyNonnegative : ¬ ((keys.length : Int) < 0) := by omega
    have keyWithinLimit :
        ¬ ((maxPubKeysPerMultiSig : Int) < (keys.length : Int)) := by
      omega
    simp [keyNonnegative, keyWithinLimit] at decoded
    rw [decodeThreshold] at decoded
    have thresholdNonnegative : ¬ ((threshold : Int) < 0) := by omega
    have thresholdWithinKeys : ¬ ((keys.length : Int) < threshold) := by omega
    simp [thresholdNonnegative, thresholdWithinKeys] at decoded
    split at decoded
    · contradiction
    · split at decoded
      · cases decoded
        simp [checkMultiSigDummy] at dummyOk
      · rename_i dummy rest afterDrop
        cases decoded
        refine ⟨stack.take threshold, dummy, rest, ?_, ?_, rfl⟩
        · have parts := List.take_append_drop threshold stack
          rw [afterDrop] at parts
          exact parts.symm
        · simp [List.length_take]
          omega

/-- The compiler's legacy key-push prefix contains no control-flow
    delimiters. -/
private theorem compileKeyPushes_balancedControlFlow (keys : List PubKey) :
    BalancedControlFlow (compileKeyPushes keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append (.atom (by simp [NonConditional])) ih

/-- Successful legacy multisignature compilation consumes an input prefix and
    replaces it with one boolean result. -/
theorem Eval.legacyMulti_success_shape
    {threshold : Nat} {keys : List PubKey}
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (run : Eval
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      stack altStack flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  have combined : Eval
      (([.pushNum threshold] ++ compileKeyPushes keys ++
          [.pushNum keys.length]) ++ [.op .OP_CHECKMULTISIG])
      stack altStack flags ctx (.success finalStack finalAlt) := by
    simpa [List.append_assoc] using run
  have prefixBalanced : BalancedControlFlow
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length]) :=
    .append
      (.append (.atom (by simp [NonConditional]))
        (compileKeyPushes_balancedControlFlow keys))
      (.atom (by simp [NonConditional]))
  obtain ⟨middle, middleAlt, prefixRun, checkRun⟩ :=
    Eval.splitBalancedAppend_success prefixBalanced combined
  have thresholdRun : Eval [.pushNum threshold] stack altStack flags ctx
      (.success (scriptNat threshold :: stack) altStack) := by
    exact Eval.pushNum threshold [] stack altStack flags ctx _ Eval.done
  have keysRun := compileKeyPushes_execution keys flags ctx
    (scriptNat threshold :: stack) altStack
  have countRun : Eval [.pushNum keys.length]
      ((keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack)
      altStack flags ctx
      (.success
        (scriptNat keys.length ::
          (keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: stack)
        altStack) := by
    exact Eval.pushNum keys.length [] _ altStack flags ctx _ Eval.done
  have canonicalPrefix : Eval
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length]) stack altStack flags ctx
      (.success
        (scriptNat keys.length ::
          (keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: stack)
        altStack) := by
    exact Eval.append (Eval.append thresholdRun keysRun) countRun
  have prefixEq := Eval.result_unique prefixRun canonicalPrefix
  cases prefixEq
  let opcodeStack : Stack :=
    scriptNat keys.length ::
      (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack
  cases decodedEq : decodeCheckMultiSigOperandsFor flags ctx opcodeStack with
  | error error =>
      have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack altStack flags ctx
          (.failure error) :=
        Eval.checkmultisig_operand_failure opcodeStack [] altStack flags ctx
          error decodedEq
      exact (Eval.success_failure_absurd checkRun failed).elim
  | ok operands =>
      cases checkedEq : checkMultiSigFor checkSig flags ctx
          operands.signatures operands.pubkeys with
      | error error =>
          have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack altStack
              flags ctx (.failure error) :=
            Eval.checkmultisig_encoding_failure opcodeStack operands []
              altStack flags ctx error decodedEq checkedEq
          exact (Eval.success_failure_absurd checkRun failed).elim
      | ok checked =>
          cases checked with
          | false =>
              by_cases nullFail : nullFailSatisfied flags operands.signatures
              · cases dummyEq : checkMultiSigDummy flags operands.dummy with
                | error error =>
                    have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                        altStack flags ctx (.failure error) :=
                      Eval.checkmultisig_dummy_failure opcodeStack operands []
                        altStack flags ctx false error decodedEq checkedEq
                        (Or.inr nullFail) dummyEq
                    exact (Eval.success_failure_absurd checkRun failed).elim
                | ok successValue =>
                    cases successValue
                    have canonical : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                        altStack flags ctx
                        (.success (falseElement :: operands.rest) altStack) :=
                      Eval.checkmultisig_failure opcodeStack operands []
                        altStack flags ctx _ decodedEq checkedEq nullFail dummyEq
                        Eval.done
                    have equal := Eval.result_unique checkRun canonical
                    cases equal
                    obtain ⟨signatures, dummy, rest, inputEq,
                        signatureCount, restEq⟩ :=
                      decodeCheckMultiSigOperandsFor_compiled_shape keyBound
                        thresholdBound decodedEq dummyEq
                    rw [restEq]
                    refine ⟨rfl, signatures ++ [dummy], rest, falseElement,
                      ?_, rfl⟩
                    simpa [List.append_assoc] using inputEq
              · have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                    altStack flags ctx (.failure .sigNullFail) :=
                  Eval.checkmultisig_nullfail_failure opcodeStack operands []
                    altStack flags ctx decodedEq checkedEq nullFail
                exact (Eval.success_failure_absurd checkRun failed).elim
          | true =>
              cases dummyEq : checkMultiSigDummy flags operands.dummy with
              | error error =>
                  have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                      altStack flags ctx (.failure error) :=
                    Eval.checkmultisig_dummy_failure opcodeStack operands []
                      altStack flags ctx true error decodedEq checkedEq
                      (Or.inl rfl) dummyEq
                  exact (Eval.success_failure_absurd checkRun failed).elim
              | ok successValue =>
                  cases successValue
                  have canonical : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                      altStack flags ctx
                      (.success (trueElement :: operands.rest) altStack) :=
                    Eval.checkmultisig_success opcodeStack operands [] altStack
                      flags ctx _ decodedEq checkedEq dummyEq Eval.done
                  have equal := Eval.result_unique checkRun canonical
                  cases equal
                  obtain ⟨signatures, dummy, rest, inputEq,
                      signatureCount, restEq⟩ :=
                    decodeCheckMultiSigOperandsFor_compiled_shape keyBound
                      thresholdBound decodedEq dummyEq
                  rw [restEq]
                  refine ⟨rfl, signatures ++ [dummy], rest, trueElement,
                    ?_, rfl⟩
                  simpa [List.append_assoc] using inputEq

end LeanMiniscript.Miniscript
