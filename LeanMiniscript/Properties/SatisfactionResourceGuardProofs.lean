import LeanMiniscript.Properties.SatisfactionResourceProofs

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Resource-aware nonempty guard wrapper
-/

namespace GeneratedResourceContract

/-- Resource-aware satisfying execution of the `j` nonempty guard. -/
theorem j
    {fragment : CoreFragment} {witness : Witness}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedResourceContract fragment witness true flags txCtx
      ⟨.B, mods⟩) (nonzero : mods.n = true) :
    GeneratedResourceContract (.j fragment) witness true flags txCtx
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ := by
  cases contract with
  | @b _ result value trace dynamic input facts executed resources stackSelected
      opSelected =>
    obtain ⟨top, rest, shape, topNonempty⟩ := input.nonzeroTop nonzero rfl
    have topBound := input.bounded.runtimeTop shape
    have decoded := decodeScriptNum_scriptNat_of_le_maxScriptElementSize
      topBound flags.minimalData
    have childResources : ExecutesResourceFrame (compile fragment)
        (top :: rest) [result] flags txCtx trace dynamic := by
      simpa [shape] using resources
    have sized := (ExecutesResourceFrame.size top flags txCtx).withSuffix
      (suffix := rest)
    have normalized := (ExecutesResourceFrame.zeroNotEqual (scriptNat top.size)
      (Int.ofNat top.size) flags txCtx decoded).withSuffix
        (suffix := top :: rest)
    have prefixFrame := sized.append normalized
    let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
    have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
        some frame := by
      simpa [frame] using splitConditional_balanced_ifThen
        (compile_balancedControlFlow fragment) (suffix := [])
    have sizeNonzero : Int.ofNat top.size ≠ 0 :=
      Int.ofNat_ne_zero.mpr topNonempty
    have nonzeroBool : (Int.ofNat top.size != 0) = true :=
      bne_iff_ne.mpr sizeNonzero
    have selectorEq : boolToElement (Int.ofNat top.size != 0) = trueElement := by
      rw [nonzeroBool]
      rfl
    have selected : ExecutesResourceFrame
        (frame.select (castToBool
          (boolToElement (Int.ofNat top.size != 0))))
        (top :: rest) [result] flags txCtx trace dynamic := by
      rw [selectorEq]
      simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
        childResources
    have selectorMinimal : minimalIfSatisfied flags txCtx.sigVersion
        (boolToElement (Int.ofNat top.size != 0)) := by
      rw [selectorEq]
      exact minimalIfSatisfied_of_arg _ _ trueElement_minimalIfArg
    have conditional := ExecutesResourceFrame.ifSelected split
      selectorMinimal selected
    have concrete := prefixFrame.append conditional
    let prefixTrace := (StackTraceBound.size
      |>.sequential StackTraceBound.zeroNotEqual
      |>.sequential StackTraceBound.branch)
    have raw : ExecutesResourceFrame (compile (.j fragment)) (top :: rest)
        [result] flags txCtx
        ((StackTraceBound.size.sequential StackTraceBound.zeroNotEqual).sequential
          (StackTraceBound.branch.sequential trace)) dynamic := by
      simpa [compile, compileWithKeyHash, frame, List.append_assoc] using concrete
    have bounded : ExecutesResourceFrame (compile (.j fragment)) (top :: rest)
        [result] flags txCtx (prefixTrace.sequential trace) dynamic := by
      apply raw.mono
      · simp [prefixTrace, StackTraceBound.sequential]
        omega
      · simp [prefixTrace, StackTraceBound.sequential]
        omega
      · exact Nat.le_refl _
    have childExec := executed
    rw [shape] at childExec
    apply GeneratedResourceContract.b
    · refine ⟨input.bounded, ?_, ?_, ?_⟩
      · simp
      · intro enabled
        exact input.oneArg enabled
      · intro _ _
        exact ⟨top, rest, shape, topNonempty⟩
    · exact facts.monoUnit (by simp)
    · simpa [shape] using childExec.j topNonempty decoded
    · simpa [shape] using bounded
    · simpa [selectedStackSummary, stackPathBounds, prefixTrace,
        StackTraceSet.sequential] using congrArg
          (fun summary => StackTraceSet.sequential (some prefixTrace) summary)
          stackSelected
    · simpa [selectedOpSummary, opPathBounds] using opSelected

/-- Resource-aware canonical dissatisfaction of the `j` guard. -/
theorem j_false
    {mods : CorrectnessModifiers} (fragment : CoreFragment)
    (flags : ScriptFlags) (txCtx : TxContext) :
    GeneratedResourceContract (.j fragment) [falseElement] false flags txCtx
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ := by
  have decoded : decodeScriptNum (scriptNat falseElement.size)
      flags.minimalData maxArithmeticScriptNumBytes = .ok 0 := by
    have sizeZero : falseElement.size = 0 := by rfl
    simpa [sizeZero, scriptNat, scriptNum_zero] using
      (decodeScriptNum_scriptNat_of_lt
        (n := 0) (by change 0 < 2147483648; omega) flags.minimalData)
  have sized := ExecutesResourceFrame.size falseElement flags txCtx
  have normalized := (ExecutesResourceFrame.zeroNotEqual
    (scriptNat falseElement.size) 0 flags txCtx decoded).withSuffix
      (suffix := [falseElement])
  have prefixFrame := sized.append normalized
  let frame : ConditionalFrame := { branches := [compile fragment], after := [] }
  have split : splitConditional (compile fragment ++ [.op .OP_ENDIF]) =
      some frame := by
    simpa [frame] using splitConditional_balanced_ifThen
      (compile_balancedControlFlow fragment) (suffix := [])
  have skipped : ExecutesResourceFrame
      (frame.select (castToBool falseElement)) [falseElement] [falseElement]
      flags txCtx StackTraceBound.empty 0 := by
    simpa [frame, ConditionalFrame.select, selectConditionalBranches] using
      ExecutesResourceFrame.empty [falseElement] flags txCtx
  have conditional := ExecutesResourceFrame.ifSelected split
    (minimalIfSatisfied_of_arg _ _ falseElement_minimalIfArg) skipped
  have concrete := prefixFrame.append conditional
  let prefixTrace := (StackTraceBound.size
    |>.sequential StackTraceBound.zeroNotEqual
    |>.sequential StackTraceBound.branch)
  have raw : ExecutesResourceFrame (compile (.j fragment)) [falseElement]
      [falseElement] flags txCtx
      ((StackTraceBound.size.sequential StackTraceBound.zeroNotEqual).sequential
        (StackTraceBound.branch.sequential StackTraceBound.empty)) 0 := by
    simpa [compile, compileWithKeyHash, frame, List.append_assoc] using concrete
  have resources : ExecutesResourceFrame (compile (.j fragment)) [falseElement]
      [falseElement] flags txCtx prefixTrace 0 := by
    apply raw.mono
    · simp [prefixTrace, StackTraceBound.sequential, StackTraceBound.empty,
        StackTraceBound.size, StackTraceBound.zeroNotEqual,
        StackTraceBound.branch]
    · simp [prefixTrace, StackTraceBound.sequential, StackTraceBound.empty,
        StackTraceBound.size, StackTraceBound.zeroNotEqual,
        StackTraceBound.branch]
      omega
    · exact Nat.le_refl _
  apply GeneratedResourceContract.b
  · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
      ?_, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨falseElement, rfl⟩
    · simp
  · exact BooleanResultFacts.canonical false _ flags
  · simpa [boolToElement, Witness.toInitialStack] using
      j_dissatisfaction_execution fragment flags txCtx
  · simpa [Witness.toInitialStack, boolToElement] using resources
  · simp [selectedStackSummary, stackPathBounds, prefixTrace]
  · simp [selectedOpSummary, opPathBounds]

end GeneratedResourceContract

namespace CandidatePair.SupportsGeneratedResources

/-- Candidate-wide resource support for the `j` nonempty guard. -/
theorem j
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.B, mods⟩ flags txCtx) (nonzero : mods.n = true) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := pair.sat
         dsat := (CandidateResult.usable [falseElement] false).select
           (pair.dsat.requireNonemptyRuntimeTop.markNonCanonical) } : CandidatePair)
      scriptCtx (.j fragment)
      ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩ flags txCtx := by
  refine ⟨.j_wrap supported.typed nonzero, ?_, ?_⟩
  · intro witness selected
    exact (supported.sat witness selected).j nonzero
  · intro witness selected
    have witnessShape := CandidateResult.usable_false_select_witness selected
    subst witness
    exact GeneratedResourceContract.j_false (mods := mods) fragment flags txCtx

end CandidatePair.SupportsGeneratedResources

end LeanMiniscript.Properties
