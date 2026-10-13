import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Bridges
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Contracts

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: wrapper contracts

The K-to-B `c:` lift and the compositional contracts for the `c`, `v`, `a`,
`s`, `n`, `d`, and `j` wrappers.
-/

/-! ## K-to-B wrapper lift -/

namespace CandidatePair.SupportsGenerated

/-- Wrapper `c` consumes the checked pending signature carried by a generated
    K execution. The candidate pair itself is unchanged by `c`, so metadata
    and selection provenance remain exact. -/
theorem c
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGenerated scriptCtx fragment ⟨.K, mods⟩
      flags txCtx) :
    pair.SupportsGenerated scriptCtx (.c fragment)
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx := by
  refine ⟨.c_wrap supported.typed, ?_, ?_⟩
  · intro witness selected
    cases supported.sat witness selected with
    | k ownArgs key signature stackShape keyExec checked =>
        apply GeneratedExecution.b
        refine ⟨boolToElement true, ?_, castToBool_boolToElement true⟩
        simpa [stackShape] using keyExec.c checked
  · intro witness selected
    cases supported.dsat witness selected with
    | k ownArgs key signature stackShape keyExec checked =>
        apply GeneratedExecution.b
        refine ⟨boolToElement false, ?_, castToBool_boolToElement false⟩
        simpa [stackShape] using keyExec.c checked

end CandidatePair.SupportsGenerated

/-! ## Compositional wrapper contracts -/

namespace GeneratedContract

theorem c
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.K, mods⟩) :
    GeneratedContract (.c fragment) witness expected flags txCtx
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      apply GeneratedContract.b
      · exact input.mono (by simp) (by simp) (by simp)
      · exact BooleanResultFacts.canonical expected _ flags
      · simpa [stackShape] using executed.c checked

theorem verify
    {fragment : CoreFragment} {witness : Witness}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract fragment witness true flags txCtx
      ⟨.B, mods⟩) :
    GeneratedContract (.v fragment) witness true flags txCtx
      ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .v (input.mono (by simp) (by simp) (by simp)) rfl
        (executed.v facts.truth)

theorem a
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) :
    GeneratedContract (.a fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .w (input.mono (by simp) (by simp) (by simp)) .savedFirst
        (facts.monoUnit (by simp)) executed.a

theorem s
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) (oneArg : mods.o = true) :
    GeneratedContract (.s fragment) witness expected flags txCtx
      ⟨.W, { d := mods.d, u := mods.u }⟩ := by
  cases contract with
  | b input facts executed =>
      obtain ⟨argument, shape⟩ := input.oneArg oneArg
      apply GeneratedContract.w
        (input := input.mono (by simp) (by simp) (by simp))
        (order := .resultFirst)
        (facts := facts.monoUnit (by simp))
      have childExec := executed
      rw [shape] at childExec
      simpa [shape] using childExec.s

theorem n
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract fragment witness expected flags txCtx
      ⟨.B, mods⟩) :
    GeneratedContract (.n fragment) witness expected flags txCtx
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩ := by
  cases contract with
  | b input facts executed =>
      apply GeneratedContract.b
      · exact input.mono (by simp) (by simp) (by simp)
      · exact BooleanResultFacts.canonical expected _ flags
      · simpa [facts.nonzero] using executed.n facts.decoded

end GeneratedContract

namespace CandidatePair.SupportsGeneratedContract

/-- Strong K-to-B wrapper composition. -/
theorem c
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.K, mods⟩ flags txCtx) :
    pair.SupportsGeneratedContract scriptCtx (.c fragment)
      ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.c_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).c,
    fun witness selected => (supported.dsat witness selected).c⟩

/-- Generated `v` keeps only satisfying child candidates. -/
theorem v
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.B, mods⟩ flags txCtx) :
    ({ sat := pair.sat } : CandidatePair).SupportsGeneratedContract scriptCtx
      (.v fragment) ⟨.V, { z := mods.z, o := mods.o, n := mods.n }⟩
      flags txCtx :=
  ⟨.v_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).verify,
    CandidateResult.supports_impossible _⟩

/-- Generated `a` preserves candidates and records saved-first W order. -/
theorem a
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.B, mods⟩ flags txCtx) :
    pair.SupportsGeneratedContract scriptCtx (.a fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.a_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).a,
    fun witness selected => (supported.dsat witness selected).a⟩

/-- Generated `s` uses the child's typed singleton-input invariant and records
    result-first W order. -/
theorem s
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.B, mods⟩ flags txCtx) (oneArg : mods.o = true) :
    pair.SupportsGeneratedContract scriptCtx (.s fragment)
      ⟨.W, { d := mods.d, u := mods.u }⟩ flags txCtx :=
  ⟨.s_wrap supported.typed oneArg,
    fun witness selected => (supported.sat witness selected).s oneArg,
    fun witness selected => (supported.dsat witness selected).s oneArg⟩

/-- Generated `n` preserves candidates while normalizing each exact decoded
    child result to a canonical boolean. -/
theorem n
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.B, mods⟩ flags txCtx) :
    pair.SupportsGeneratedContract scriptCtx (.n fragment)
      ⟨.B, { z := mods.z, o := mods.o, n := mods.n, d := mods.d, u := true }⟩
      flags txCtx :=
  ⟨.n_wrap supported.typed,
    fun witness selected => (supported.sat witness selected).n,
    fun witness selected => (supported.dsat witness selected).n⟩

/-- Generated `d` adds the canonical true selector to child satisfactions and
    supplies the canonical false singleton directly for dissatisfaction. -/
theorem d
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.V, mods⟩ flags txCtx) (zeroArg : mods.z = true) :
    CandidatePair.SupportsGeneratedContract
      ({ sat := pair.sat.withSelector trueElement
         dsat := .usable [falseElement] false } : CandidatePair)
      scriptCtx (.d fragment)
        ⟨.B, { o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩
      flags txCtx := by
  refine ⟨.d_wrap supported.typed zeroArg, ?_, ?_⟩
  · intro witness selected
    rw [CandidateResult.withSelector_usableWitness_iff] at selected
    obtain ⟨inner, innerSelected, rfl⟩ := selected
    cases supported.sat inner innerSelected with
    | v input expectedTrue executed =>
        have childExec := executed
        have childShape := input.zeroArgs zeroArg
        rw [childShape] at childExec
        apply GeneratedContract.b
        · refine ⟨input.bounded.withSelector trueElement_size_le,
            ?_, ?_, ?_⟩
          · simp
          · intro _
            exact ⟨trueElement, by simp [childShape]⟩
          · intro _ _
            exact ⟨trueElement, [], by simp [childShape], by decide⟩
        · exact BooleanResultFacts.canonical true _ flags
        · simpa [childShape, boolToElement] using childExec.d
  · apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
        ?_, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨falseElement, rfl⟩
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · simpa [boolToElement, Witness.toInitialStack] using
        d_dissatisfaction_execution fragment flags txCtx

/-- Generated `j` uses the child's `n` invariant and witness-item bound to
    justify the size guard. Its selected dissatisfaction is always the
    canonical false singleton, independent of the non-canonical child row. -/
theorem j
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment
      ⟨.B, mods⟩ flags txCtx) (nonzero : mods.n = true) :
    CandidatePair.SupportsGeneratedContract
      ({ sat := pair.sat
         dsat := (CandidateResult.usable [falseElement] false).select
           (pair.dsat.requireNonemptyRuntimeTop.markNonCanonical) } : CandidatePair)
      scriptCtx (.j fragment)
        ⟨.B, { o := mods.o, n := true, d := true, u := mods.u }⟩
        flags txCtx := by
  refine ⟨.j_wrap supported.typed nonzero, ?_, ?_⟩
  · intro witness selected
    cases supported.sat witness selected with
    | b input facts executed =>
        obtain ⟨top, rest, shape, topNonempty⟩ :=
          input.nonzeroTop nonzero rfl
        have topBound := input.bounded.runtimeTop shape
        have decoded := decodeScriptNum_scriptNat_of_le_maxScriptElementSize
          topBound flags.minimalData
        have childExec := executed
        rw [shape] at childExec
        apply GeneratedContract.b
        · refine ⟨input.bounded, ?_, ?_, ?_⟩
          · simp
          · intro enabled
            exact input.oneArg enabled
          · intro _ _
            exact ⟨top, rest, shape, topNonempty⟩
        · exact facts.monoUnit (by simp)
        · simpa [shape] using childExec.j topNonempty decoded
  · intro witness selected
    have witnessShape := CandidateResult.usable_false_select_witness selected
    subst witness
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
        ?_, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨falseElement, rfl⟩
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · simpa [boolToElement, Witness.toInitialStack] using
        j_dissatisfaction_execution fragment flags txCtx

end CandidatePair.SupportsGeneratedContract

end LeanMiniscript.Miniscript
