import LeanMiniscript.Miniscript.CompileVerifyResourceProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! # Terminal VERIFY resource-preservation fixtures -/

private def resourceFlags : ScriptFlags := { strictEncoding := false }

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

private theorem equalThenVerifyObserved (value : StackElement) :
    EvalResources [.op .OP_EQUAL, .op .OP_VERIFY]
      [value, value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have equalHead : Eval [.op .OP_EQUAL] [value, value] []
      resourceFlags resourceContext (.success [trueElement] []) :=
    .equal_true value value [] [] [] resourceFlags resourceContext _ rfl
      (.empty [trueElement] [] resourceFlags resourceContext)
  have verifyHead : Eval [.op .OP_VERIFY] [trueElement] []
      resourceFlags resourceContext (.success [] []) :=
    .verify_success trueElement [] [] [] resourceFlags resourceContext _ rfl
      (.empty [] [] resourceFlags resourceContext)
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    executedMultiSigKeyCharge] using
    EvalResources.step equalHead
      (EvalResources.step verifyHead
        (EvalResources.empty [] [] resourceFlags resourceContext))

private theorem dupEqualThenVerifyObserved (value : StackElement) :
    EvalResources ([.op .OP_DUP, .op .OP_EQUAL] ++ [.op .OP_VERIFY])
      [value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have dupHead : Eval [.op .OP_DUP] [value] [] resourceFlags resourceContext
      (.success [value, value] []) :=
    .dup value [] [] [] resourceFlags resourceContext _
      (.empty [value, value] [] resourceFlags resourceContext)
  have equalHead : Eval [.op .OP_EQUAL] [value, value] []
      resourceFlags resourceContext (.success [trueElement] []) :=
    .equal_true value value [] [] [] resourceFlags resourceContext _ rfl
      (.empty [trueElement] [] resourceFlags resourceContext)
  have verifyHead : Eval [.op .OP_VERIFY] [trueElement] []
      resourceFlags resourceContext (.success [] []) :=
    .verify_success trueElement [] [] [] resourceFlags resourceContext _ rfl
      (.empty [] [] resourceFlags resourceContext)
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    executedMultiSigKeyCharge] using
    EvalResources.step dupHead
      (EvalResources.step equalHead
        (EvalResources.step verifyHead
          (EvalResources.empty [] [] resourceFlags resourceContext)))

private theorem checkMultiSigThenVerifyObserved
    (verified : checkMultiSigFor checkSig resourceFlags resourceContext
      [resourceSignature] [resourceKeyB, resourceKeyA] = .ok true) :
    EvalResources [.op .OP_CHECKMULTISIG, .op .OP_VERIFY]
      oneOfTwoStack [] resourceFlags resourceContext [] []
      { peakStackItems := 6, executedMultiSigKeys := 2 } := by
  have multiSigHead : Eval [.op .OP_CHECKMULTISIG] oneOfTwoStack []
      resourceFlags resourceContext (.success [trueElement] []) := by
    apply Eval.checkmultisig_success (operands := oneOfTwoOperands)
    · rfl
    · exact verified
    · simp [checkMultiSigDummy, nullDummySatisfied, resourceFlags,
        oneOfTwoOperands, stackElementEq, falseElement]
    · exact .empty [trueElement] [] resourceFlags resourceContext
  have verifyHead : Eval [.op .OP_VERIFY] [trueElement] []
      resourceFlags resourceContext (.success [] []) :=
    .verify_success trueElement [] [] [] resourceFlags resourceContext _ rfl
      (.empty [] [] resourceFlags resourceContext)
  have decoded : decodeCheckMultiSigOperandsFor resourceFlags resourceContext
      oneOfTwoStack = .ok oneOfTwoOperands := by
    rfl
  have charged := executedMultiSigKeyCharge_checkmultisig decoded
  have observed := EvalResources.step multiSigHead
    (EvalResources.step verifyHead
      (EvalResources.empty [] [] resourceFlags resourceContext))
  rw [charged] at observed
  simpa [ExecutionResources.prepend, ExecutionResources.initial,
    executedMultiSigKeyCharge, oneOfTwoStack, oneOfTwoOperands] using observed

private def selectedIfScript : Script :=
  [.op .OP_IF, .op .OP_DUP, .op .OP_ENDIF, .op .OP_EQUAL]

private def selectedIfTail : Script :=
  [.op .OP_DUP, .op .OP_ENDIF, .op .OP_EQUAL, .op .OP_VERIFY]

private def selectedIfFrame : ConditionalFrame where
  branches := [[.op .OP_DUP]]
  after := [.op .OP_EQUAL, .op .OP_VERIFY]

private theorem selectedIfThenVerifyObserved (value : StackElement) :
    EvalResources (selectedIfScript ++ [.op .OP_VERIFY])
      [trueElement, value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have selected : EvalResources
      (selectedIfFrame.select (castToBool trueElement)) [value] []
      resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
    change EvalResources [.op .OP_DUP, .op .OP_EQUAL, .op .OP_VERIFY]
      [value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 }
    simpa using dupEqualThenVerifyObserved value
  have observed := EvalResources.if_execute (frame := selectedIfFrame)
    (show splitConditional selectedIfTail = some selectedIfFrame by rfl)
    (minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg) selected
  simpa [selectedIfScript, selectedIfTail, ExecutionResources.prepend] using observed

/-- The removed Boolean state does not lower the observed peak because the
two-item input state already dominates it. -/
example (value : StackElement) :
    EvalResources [.op .OP_EQUALVERIFY]
      [value, value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } :=
  EvalResources.fuseEqualVerify (equalThenVerifyObserved value)

/-- Signature fusion preserves whichever exact resource observation was
recorded for the successful unfused execution. -/
example {stack out : Stack} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_CHECKSIG, .op .OP_VERIFY]
      stack [] resourceFlags resourceContext out [] resources) :
    EvalResources [.op .OP_CHECKSIGVERIFY]
      stack [] resourceFlags resourceContext out [] resources :=
  EvalResources.fuseCheckSigVerify run

/-- Multisignature fusion preserves both the stack peak and decoded public-key
charge. -/
example {stack out : Stack} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_CHECKMULTISIG, .op .OP_VERIFY]
      stack [] resourceFlags resourceContext out [] resources) :
    EvalResources [.op .OP_CHECKMULTISIGVERIFY]
      stack [] resourceFlags resourceContext out [] resources :=
  EvalResources.fuseCheckMultiSigVerify run

/-- A successful two-key CHECKMULTISIG fusion retains its concrete six-item
peak and decoded two-key charge. -/
example
    (verified : checkMultiSigFor checkSig resourceFlags resourceContext
      [resourceSignature] [resourceKeyB, resourceKeyA] = .ok true) :
    EvalResources [.op .OP_CHECKMULTISIGVERIFY]
      oneOfTwoStack [] resourceFlags resourceContext [] []
      { peakStackItems := 6, executedMultiSigKeys := 2 } :=
  EvalResources.fuseCheckMultiSigVerify
    (checkMultiSigThenVerifyObserved verified)

/-- Numeric equality fusion preserves the exact successful observation. -/
example {stack out : Stack} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_NUMEQUAL, .op .OP_VERIFY]
      stack [] resourceFlags resourceContext out [] resources) :
    EvalResources [.op .OP_NUMEQUALVERIFY]
      stack [] resourceFlags resourceContext out [] resources :=
  EvalResources.fuseNumEqualVerify run

/-- The balanced-script theorem selects the specialized terminal opcode while
retaining the concrete observation. -/
example (value : StackElement) :
    EvalResources (compileVerify [.op .OP_EQUAL])
      [value, value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  exact EvalResources.compileVerify_success
    (.atom (by trivial)) (equalThenVerifyObserved value)

/-- Fusion under a balanced prefix keeps the prefix peak and exercises the
resource-preserving suffix replacement used by the general theorem. -/
example (value : StackElement) :
    EvalResources (compileVerify [.op .OP_DUP, .op .OP_EQUAL])
      [value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  exact EvalResources.compileVerify_success
    (.append (.atom (by trivial)) (.atom (by trivial)))
    (dupEqualThenVerifyObserved value)

/-- A selected IF branch can grow the stack before the trailing equality is
fused; the balanced-prefix transformation retains the exact peak and charge. -/
example (value : StackElement) :
    EvalResources (compileVerify selectedIfScript)
      [trueElement, value] [] resourceFlags resourceContext [] []
      { peakStackItems := 2, executedMultiSigKeys := 0 } := by
  have balanced : BalancedControlFlow selectedIfScript := by
    simpa [selectedIfScript] using
      BalancedControlFlow.append
        (BalancedControlFlow.ifThen
          (BalancedControlFlow.atom (element := .op .OP_DUP) (by trivial)))
        (BalancedControlFlow.atom (element := .op .OP_EQUAL) (by trivial))
  exact EvalResources.compileVerify_success balanced
    (selectedIfThenVerifyObserved value)

end LeanMiniscript.Miniscript
