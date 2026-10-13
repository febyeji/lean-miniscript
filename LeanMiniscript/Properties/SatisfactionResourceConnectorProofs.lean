import LeanMiniscript.Properties.SatisfactionResourceProofs
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs.Frames
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs.Connectives
import LeanMiniscript.Properties.SatisfactionResourceConnectorProofs.Conditionals

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-! # Resource-aware connector composition

The resource frames and `GeneratedResourceContract` connector lemmas live in
the `SatisfactionResourceConnectorProofs/` submodules; this module composes
them into candidate-level resource support.
-/

namespace CandidatePair.SupportsGeneratedResources

private theorem orILeftSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedResourceContract first witness expected flags txCtx
        ⟨base, firstMods⟩)
    (branch : branchBase base) :
    (result.withSelector trueElement).Supports fun witness =>
      GeneratedResourceContract (.or_i first second) witness expected flags
        txCtx ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector trueElement) witness selected
  exact contract.orI_left branch

private theorem orIRightSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedResourceContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (branch : branchBase base) :
    (result.withSelector falseElement).Supports fun witness =>
      GeneratedResourceContract (.or_i first second) witness expected flags
        txCtx ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector falseElement) witness selected
  exact contract.orI_right branch

private theorem andorTrueSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedResourceContract first witness true flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedResourceContract second witness expected flags txCtx
        ⟨base, secondMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedResourceContract (.andor first second third) witness expected
        flags txCtx ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  exact firstContract.andorTrue firstUnit branchContract branch

private theorem andorFalseSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedResourceContract first witness false flags txCtx
        ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedResourceContract third witness expected flags txCtx
        ⟨base, thirdMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedResourceContract (.andor first second third) witness expected
        flags txCtx ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  exact firstContract.andorFalse firstUnit branchContract branch

/-- Resource-aware generated support for `and_b`. -/
theorem and_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.combine secondPair.sat
         dsat := ((firstPair.dsat.combine secondPair.dsat).select
           ((firstPair.dsat.combine secondPair.sat).markOvercomplete)).select
           ((firstPair.sat.combine secondPair.dsat).markOvercomplete) } :
        CandidatePair) scriptCtx (.and_b first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true }⟩ flags txCtx := by
  refine ⟨.and_b firstSupported.typed secondSupported.typed, ?_, ?_⟩
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    exact firstContract.andB_same secondContract
  · have canonical : (firstPair.dsat.combine secondPair.dsat).Supports
        (fun witness => GeneratedResourceContract (.and_b first second)
          witness false flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            n := firstMods.n || (firstMods.z && secondMods.n)
            d := firstMods.d && secondMods.d
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.dsat) witness selected
      exact firstContract.andB_same secondContract
    exact (canonical.select
      (CandidateResult.supports_markOvercomplete _ _)).select
      (CandidateResult.supports_markOvercomplete _ _)

/-- Resource-aware generated support for `or_b`. -/
theorem or_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.W, secondMods⟩ flags txCtx)
    (secondD : secondMods.d = true) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := ((firstPair.sat.combine secondPair.dsat).select
           (firstPair.dsat.combine secondPair.sat)).select
           ((firstPair.sat.combine secondPair.sat).markOvercomplete)
         dsat := firstPair.dsat.combine secondPair.dsat } : CandidatePair)
      scriptCtx (.or_b first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        d := true
        u := true }⟩ flags txCtx := by
  refine ⟨.or_b firstSupported.typed firstD secondSupported.typed secondD,
    ?_, ?_⟩
  · have left : (firstPair.sat.combine secondPair.dsat).Supports
        (fun witness => GeneratedResourceContract (.or_b first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.sat.combine secondSupported.dsat) witness selected
      simpa using firstContract.orB_path secondContract (by simp)
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedResourceContract (.or_b first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      simpa using firstContract.orB_path secondContract (by simp)
    exact (left.select right).select
      (CandidateResult.supports_markOvercomplete _ _)
  · intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    simpa using firstContract.orB_path secondContract (by simp)

/-- Resource-aware generated support for both satisfaction paths of `or_c`. -/
theorem or_c
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.V, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat) } : CandidatePair)
      scriptCtx (.or_c first second)
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z }⟩ flags txCtx := by
  refine ⟨.or_c firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, CandidateResult.supports_impossible _⟩
  change (firstPair.sat.select
    (firstPair.dsat.combine secondPair.sat)).Supports _
  have left : firstPair.sat.Supports
      (fun witness => GeneratedResourceContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) :=
    firstSupported.sat.mono fun _ contract => contract.orC_left firstUnit
  have right : (firstPair.dsat.combine secondPair.sat).Supports
      (fun witness => GeneratedResourceContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) := by
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.sat) witness selected
    exact firstContract.orC_right firstUnit secondContract
  exact left.select right

/-- Resource-aware generated support for every usable path of `or_d`. -/
theorem or_d
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨.B, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat)
         dsat := firstPair.dsat.combine secondPair.dsat } : CandidatePair)
      scriptCtx (.or_d first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u }⟩ flags txCtx := by
  refine ⟨.or_d firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, ?_⟩
  · change (firstPair.sat.select
      (firstPair.dsat.combine secondPair.sat)).Supports _
    have left : firstPair.sat.Supports
        (fun witness => GeneratedResourceContract (.or_d first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) :=
      firstSupported.sat.mono fun _ contract => contract.orD_left firstUnit
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedResourceContract (.or_d first second)
          witness true flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl, firstContract,
        secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      exact firstContract.orD_right firstUnit secondContract
    exact left.select right
  · change (firstPair.dsat.combine secondPair.dsat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl, firstContract,
      secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    exact firstContract.orD_right firstUnit secondContract

/-- Resource-aware generated support for both tagged branches of `or_i`. -/
theorem or_i
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨base, firstMods⟩ flags txCtx)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := (firstPair.sat.withSelector trueElement).select
           (secondPair.sat.withSelector falseElement)
         dsat := (firstPair.dsat.withSelector trueElement).select
           (secondPair.dsat.withSelector falseElement) } : CandidatePair)
      scriptCtx (.or_i first second)
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u }⟩ flags txCtx := by
  refine ⟨.or_i firstSupported.typed secondSupported.typed branch rfl, ?_, ?_⟩
  · change ((firstPair.sat.withSelector trueElement).select
      (secondPair.sat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.sat branch).select
      (orIRightSupport secondSupported.sat branch)
  · change ((firstPair.dsat.withSelector trueElement).select
      (secondPair.dsat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.dsat branch).select
      (orIRightSupport secondSupported.dsat branch)

/-- Resource-aware generated support for every usable `andor` path. -/
theorem andor
    {firstPair secondPair thirdPair : CandidatePair}
    {scriptCtx : ScriptContext} {first second third : CoreFragment}
    {base : BaseType} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : CandidatePair.SupportsGeneratedResources firstPair
      scriptCtx first ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (secondSupported : CandidatePair.SupportsGeneratedResources secondPair
      scriptCtx second ⟨base, secondMods⟩ flags txCtx)
    (thirdSupported : CandidatePair.SupportsGeneratedResources thirdPair
      scriptCtx third ⟨base, thirdMods⟩ flags txCtx)
    (branch : branchBase base) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := (firstPair.sat.combine secondPair.sat).select
           (firstPair.dsat.combine thirdPair.sat)
         dsat := (firstPair.dsat.combine thirdPair.dsat).select
           ((firstPair.sat.combine secondPair.dsat).markNonCanonical) } :
        CandidatePair)
      scriptCtx (.andor first second third)
      ⟨base, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u }⟩ flags txCtx := by
  refine ⟨.andor firstSupported.typed firstD firstUnit secondSupported.typed
    thirdSupported.typed branch rfl, ?_, ?_⟩
  · change ((firstPair.sat.combine secondPair.sat).select
      (firstPair.dsat.combine thirdPair.sat)).Supports _
    exact (andorTrueSupport firstSupported.sat secondSupported.sat
      firstUnit branch).select
      (andorFalseSupport firstSupported.dsat thirdSupported.sat
        firstUnit branch)
  · change ((firstPair.dsat.combine thirdPair.dsat).select
      ((firstPair.sat.combine secondPair.dsat).markNonCanonical)).Supports _
    have canonical := andorFalseSupport (second := second)
      (secondMods := secondMods) firstSupported.dsat thirdSupported.dsat
      firstUnit branch
    have noncanonical := CandidateResult.Supports.markNonCanonical
      (andorTrueSupport (third := third) (thirdMods := thirdMods)
        firstSupported.sat secondSupported.dsat firstUnit branch)
    exact canonical.select noncanonical

/-- Resource-aware generated support for the `d` wrapper. -/
theorem d
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {mods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : CandidatePair.SupportsGeneratedResources pair scriptCtx
      fragment ⟨.V, mods⟩ flags txCtx) (zeroArg : mods.z = true) :
    CandidatePair.SupportsGeneratedResources
      ({ sat := pair.sat.withSelector trueElement
         dsat := .usable [falseElement] false } : CandidatePair)
      scriptCtx (.d fragment)
      ⟨.B, { o := true, n := true, d := true, u := scriptCtx.dWrapperUnit }⟩
      flags txCtx := by
  refine ⟨.d_wrap supported.typed zeroArg, ?_, ?_⟩
  · intro witness selected
    rw [CandidateResult.withSelector_usableWitness_iff] at selected
    obtain ⟨inner, innerSelected, rfl⟩ := selected
    exact (supported.sat inner innerSelected).d scriptCtx zeroArg
  · apply CandidateResult.supports_usable
    exact GeneratedResourceContract.d_false fragment scriptCtx flags txCtx

end CandidatePair.SupportsGeneratedResources

end LeanMiniscript.Properties
