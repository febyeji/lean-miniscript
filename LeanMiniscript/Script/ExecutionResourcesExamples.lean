import LeanMiniscript.Script.ExecutionResources

namespace LeanMiniscript.Script

/-! # Successful execution resource observation fixtures -/

private def resourceFlags : ScriptFlags := { strictEncoding := false }

private def noNullFailFlags : ScriptFlags where
  strictEncoding := false
  nullFail := false

private def resourceContext : TxContext where
  version := 2
  locktime := 0
  sequence := 0
  sigHash := ⟨#[]⟩

private def resourceKeyA : StackElement := ⟨#[0x02]⟩
private def resourceKeyB : StackElement := ⟨#[0x03]⟩
private def resourceSignature : StackElement := ⟨#[0x30]⟩

private def oneOfTwoStack : Stack :=
  [scriptNum 2, resourceKeyB, resourceKeyA, scriptNum 1,
    resourceSignature, falseElement]

private def oneOfTwoOperands : CheckMultiSigOperands where
  pubkeys := [resourceKeyB, resourceKeyA]
  signatures := [resourceSignature]
  dummy := some falseElement
  rest := []

/-- A stack-growing opcode records both the input and larger output state. -/
example (x : StackElement) :
    EvalResources [.op .OP_DUP] [x] [] resourceFlags resourceContext
      [x, x] [] { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have head : Eval [.op .OP_DUP] [x] [] resourceFlags resourceContext
      (.success [x, x] []) :=
    .dup x [] [] [] resourceFlags resourceContext _
      (.empty [x, x] [] resourceFlags resourceContext)
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    executedMultiSigKeyCharge] using
    EvalResources.step head
      (EvalResources.empty [x, x] [] resourceFlags resourceContext)

private def skippedMultiSigTail : Script :=
  [.op .OP_DUP, .op .OP_ELSE, .op .OP_CHECKMULTISIG, .op .OP_ENDIF]

private def skippedMultiSigFrame : ConditionalFrame where
  branches := [[.op .OP_DUP], [.op .OP_CHECKMULTISIG]]
  after := []

/-- Only the selected branch contributes: the inactive multisignature opcode
    has no dynamic key charge. -/
example (x : StackElement) :
    EvalResources (.op .OP_IF :: skippedMultiSigTail)
      [trueElement, x] [] resourceFlags resourceContext [x, x] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have selectedHead : Eval [.op .OP_DUP] [x] [] resourceFlags resourceContext
      (.success [x, x] []) :=
    .dup x [] [] [] resourceFlags resourceContext _
      (.empty [x, x] [] resourceFlags resourceContext)
  have selected : EvalResources [.op .OP_DUP] [x] [] resourceFlags
      resourceContext [x, x] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
    simpa [ExecutionResources.prepend, ExecutionResources.initial,
      executedMultiSigKeyCharge] using
      EvalResources.step selectedHead
        (EvalResources.empty [x, x] [] resourceFlags resourceContext)
  have selected' : EvalResources
      (skippedMultiSigFrame.select (castToBool trueElement)) [x] []
      resourceFlags resourceContext [x, x] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
    change EvalResources [.op .OP_DUP] [x] [] resourceFlags resourceContext
      [x, x] [] { peakStackItems := 2, executedMultiSigKeys := 0 }
    exact selected
  have observed := EvalResources.if_execute (frame := skippedMultiSigFrame)
    (show splitConditional skippedMultiSigTail = some skippedMultiSigFrame by rfl)
    (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) selected'
  simpa [ExecutionResources.prepend] using observed

/-- A successful legacy multisignature check charges its two decoded keys. -/
example
    (verified : checkMultiSigFor checkSig resourceFlags resourceContext
      [resourceSignature] [resourceKeyB, resourceKeyA] = .ok true) :
    EvalResources [.op .OP_CHECKMULTISIG] oneOfTwoStack [] resourceFlags
      resourceContext [trueElement] []
      { peakStackItems := 6, executedMultiSigKeys := 2 } := by
  have head : Eval [.op .OP_CHECKMULTISIG] oneOfTwoStack [] resourceFlags
      resourceContext (.success [trueElement] []) := by
    apply Eval.checkmultisig_success (operands := oneOfTwoOperands)
    · rfl
    · exact verified
    · simp [checkMultiSigDummy, nullDummySatisfied, resourceFlags,
        oneOfTwoOperands, stackElementEq, falseElement]
    · exact .empty [trueElement] [] resourceFlags resourceContext
  have decoded : decodeCheckMultiSigOperandsFor resourceFlags resourceContext
      oneOfTwoStack = .ok oneOfTwoOperands := by rfl
  have charged := executedMultiSigKeyCharge_checkmultisig decoded
  have observed := EvalResources.step head
    (EvalResources.empty [trueElement] [] resourceFlags resourceContext)
  rw [charged] at observed
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    oneOfTwoStack, oneOfTwoOperands] using observed

/-- A false CHECKMULTISIG result still continues and charges the decoded keys. -/
example
    (rejected : checkMultiSigFor checkSig noNullFailFlags resourceContext
      [resourceSignature] [resourceKeyB, resourceKeyA] = .ok false) :
    EvalResources [.op .OP_CHECKMULTISIG] oneOfTwoStack [] noNullFailFlags
      resourceContext [falseElement] []
      { peakStackItems := 6, executedMultiSigKeys := 2 } := by
  have head : Eval [.op .OP_CHECKMULTISIG] oneOfTwoStack [] noNullFailFlags
      resourceContext (.success [falseElement] []) := by
    apply Eval.checkmultisig_failure (operands := oneOfTwoOperands)
    · rfl
    · exact rejected
    · simp [nullFailSatisfied, noNullFailFlags]
    · simp [checkMultiSigDummy, nullDummySatisfied, noNullFailFlags,
        oneOfTwoOperands, stackElementEq, falseElement]
    · exact .empty [falseElement] [] noNullFailFlags resourceContext
  have decoded : decodeCheckMultiSigOperandsFor noNullFailFlags resourceContext
      oneOfTwoStack = .ok oneOfTwoOperands := by rfl
  have charged := executedMultiSigKeyCharge_checkmultisig decoded
  have observed := EvalResources.step head
    (EvalResources.empty [falseElement] [] noNullFailFlags resourceContext)
  rw [charged] at observed
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    oneOfTwoStack, oneOfTwoOperands] using observed

/-- The VERIFY form consumes the true result while retaining the same key
    charge. -/
example
    (verified : checkMultiSigFor checkSig resourceFlags resourceContext
      [resourceSignature] [resourceKeyB, resourceKeyA] = .ok true) :
    EvalResources [.op .OP_CHECKMULTISIGVERIFY] oneOfTwoStack [] resourceFlags
      resourceContext [] []
      { peakStackItems := 6, executedMultiSigKeys := 2 } := by
  have head : Eval [.op .OP_CHECKMULTISIGVERIFY] oneOfTwoStack [] resourceFlags
      resourceContext (.success [] []) := by
    apply Eval.checkmultisigverify_success (operands := oneOfTwoOperands)
    · rfl
    · exact verified
    · simp [checkMultiSigDummy, nullDummySatisfied, resourceFlags,
        oneOfTwoOperands, stackElementEq, falseElement]
    · exact .empty [] [] resourceFlags resourceContext
  have decoded : decodeCheckMultiSigOperandsFor resourceFlags resourceContext
      oneOfTwoStack = .ok oneOfTwoOperands := by rfl
  have charged := executedMultiSigKeyCharge_checkmultisigverify decoded
  have observed := EvalResources.step head
    (EvalResources.empty [] [] resourceFlags resourceContext)
  rw [charged] at observed
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    oneOfTwoStack, oneOfTwoOperands] using observed

/-- CHECKSIG followed by VERIFY and CHECKSIGVERIFY have the same stack peak
    and dynamic multisignature charge on success. -/
example (pubkey signature : StackElement)
    (verified : checkSigWithEncoding checkSig checkSchnorrSig resourceFlags
      resourceContext signature pubkey = .ok true) :
    EvalResources [.op .OP_CHECKSIG, .op .OP_VERIFY]
        [pubkey, signature] [] resourceFlags resourceContext [] []
        { peakStackItems := 2, executedMultiSigKeys := 0 } ∧
      EvalResources [.op .OP_CHECKSIGVERIFY]
        [pubkey, signature] [] resourceFlags resourceContext [] []
        { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have checkHead : Eval [.op .OP_CHECKSIG] [pubkey, signature] []
      resourceFlags resourceContext (.success [trueElement] []) :=
    .checksig_success pubkey signature [] [] [] resourceFlags resourceContext _
      verified (.empty [trueElement] [] resourceFlags resourceContext)
  have verifyHead : Eval [.op .OP_VERIFY] [trueElement] [] resourceFlags
      resourceContext (.success [] []) :=
    .verify_success trueElement [] [] [] resourceFlags resourceContext _ rfl
      (.empty [] [] resourceFlags resourceContext)
  have fusedHead : Eval [.op .OP_CHECKSIGVERIFY] [pubkey, signature] []
      resourceFlags resourceContext (.success [] []) :=
    .checksigverify_success pubkey signature [] [] [] resourceFlags
      resourceContext _ verified (.empty [] [] resourceFlags resourceContext)
  constructor
  · simpa [ExecutionResources.prepend, ExecutionResources.initial,
      executedMultiSigKeyCharge] using
      EvalResources.step checkHead
        (EvalResources.step verifyHead
          (EvalResources.empty [] [] resourceFlags resourceContext))
  · simpa [ExecutionResources.prepend, ExecutionResources.initial,
      executedMultiSigKeyCharge] using
      EvalResources.step fusedHead
        (EvalResources.empty [] [] resourceFlags resourceContext)

end LeanMiniscript.Script
