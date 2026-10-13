import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Atomic
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Connectives

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: candidate composition for combinators

Candidate-pair support for the binary connectives, `andor`, and `thresh`.
-/

namespace CandidatePair.SupportsGeneratedContract

/-- Generated candidate support for `and_v`, including the usable
    non-canonical dissatisfaction row. -/
theorem and_v
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods : CorrectnessModifiers}
    {secondType : MiniType} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.V, firstMods⟩ flags txCtx)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      secondType flags txCtx)
    (branch : branchBase secondType.base) :
    ({ sat := firstPair.sat.combine secondPair.sat
       dsat := (firstPair.sat.combine secondPair.dsat).markNonCanonical } :
      CandidatePair).SupportsGeneratedContract scriptCtx (.and_v first second)
      ⟨secondType.base, {
        z := firstMods.z && secondType.mods.z
        o := (firstMods.z && secondType.mods.o) ||
          (firstMods.o && secondType.mods.z)
        n := firstMods.n || (firstMods.z && secondType.mods.n)
        u := secondType.mods.u
      }⟩ flags txCtx := by
  refine ⟨.and_v firstSupported.typed secondSupported.typed branch, ?_, ?_⟩
  · change (firstPair.sat.combine secondPair.sat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    cases secondType with
    | mk base mods =>
        cases base with
        | B => exact firstContract.andV_b secondContract
        | K => exact firstContract.andV_k secondContract
        | V => exact firstContract.andV_v secondContract
        | W => simp [branchBase] at branch
  · change (firstPair.sat.combine secondPair.dsat).markNonCanonical.Supports _
    intro witness selected
    have combined := CandidateResult.markNonCanonical_usableWitness_iff.mp selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.dsat) witness combined
    cases secondType with
    | mk base mods =>
        cases base with
        | B => exact firstContract.andV_b secondContract
        | K => exact firstContract.andV_k secondContract
        | V => exact firstContract.andV_v secondContract
        | W => simp [branchBase] at branch

/-- Generated candidate support for `and_b`. Only the all-false
    dissatisfaction is usable; both mixed rows are overcomplete. -/
theorem and_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨.W, secondMods⟩ flags txCtx) :
    ({ sat := firstPair.sat.combine secondPair.sat
       dsat := ((firstPair.dsat.combine secondPair.dsat).select
         ((firstPair.dsat.combine secondPair.sat).markOvercomplete)).select
         ((firstPair.sat.combine secondPair.dsat).markOvercomplete) } :
      CandidatePair).SupportsGeneratedContract scriptCtx (.and_b first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true
      }⟩ flags txCtx := by
  refine ⟨.and_b firstSupported.typed secondSupported.typed, ?_, ?_⟩
  · change (firstPair.sat.combine secondPair.sat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.sat.combine secondSupported.sat) witness selected
    exact firstContract.andB secondContract (by decide)
  · change (((firstPair.dsat.combine secondPair.dsat).select
      ((firstPair.dsat.combine secondPair.sat).markOvercomplete)).select
      ((firstPair.sat.combine secondPair.dsat).markOvercomplete)).Supports _
    have canonical : (firstPair.dsat.combine secondPair.dsat).Supports
        (fun witness => GeneratedContract (.and_b first second) witness false
          flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            n := firstMods.n || (firstMods.z && secondMods.n)
            d := firstMods.d && secondMods.d
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl,
        firstContract, secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.dsat) witness selected
      exact firstContract.andB secondContract (by decide)
    exact (canonical.select
      (CandidateResult.supports_markOvercomplete _ _)).select
      (CandidateResult.supports_markOvercomplete _ _)

/-- Generated candidate support for `or_b`, including both usable mixed
    satisfaction paths and the all-false canonical dissatisfaction. -/
theorem or_b
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨.W, secondMods⟩ flags txCtx) (secondD : secondMods.d = true) :
    CandidatePair.SupportsGeneratedContract
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
        u := true
      }⟩ flags txCtx := by
  refine ⟨.or_b firstSupported.typed firstD secondSupported.typed secondD,
    ?_, ?_⟩
  · change (((firstPair.sat.combine secondPair.dsat).select
      (firstPair.dsat.combine secondPair.sat)).select
      ((firstPair.sat.combine secondPair.sat).markOvercomplete)).Supports _
    have left : (firstPair.sat.combine secondPair.dsat).Supports
        (fun witness => GeneratedContract (.or_b first second) witness true
          flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl,
        firstContract, secondContract⟩ :=
        (firstSupported.sat.combine secondSupported.dsat) witness selected
      exact firstContract.orB secondContract (by decide)
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedContract (.or_b first second) witness true
          flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := (firstMods.z && secondMods.o) ||
              (firstMods.o && secondMods.z)
            d := true
            u := true }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl,
        firstContract, secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      exact firstContract.orB secondContract (by decide)
    exact (left.select right).select
      (CandidateResult.supports_markOvercomplete _ _)
  · change (firstPair.dsat.combine secondPair.dsat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    exact firstContract.orB secondContract (by decide)

/-- Generated support for `or_c`: either the satisfying unit selector skips
    the V child, or the canonical false selector runs it. -/
theorem or_c
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨.V, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedContract
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat) } : CandidatePair)
      scriptCtx (.or_c first second)
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
      }⟩ flags txCtx := by
  refine ⟨.or_c firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, CandidateResult.supports_impossible _⟩
  change (firstPair.sat.select
    (firstPair.dsat.combine secondPair.sat)).Supports _
  have left : firstPair.sat.Supports
      (fun witness => GeneratedContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) :=
    firstSupported.sat.mono fun _ contract => contract.orC_left firstUnit
  have right : (firstPair.dsat.combine secondPair.sat).Supports
      (fun witness => GeneratedContract (.or_c first second) witness true
        flags txCtx ⟨.V, {
          z := firstMods.z && secondMods.z
          o := firstMods.o && secondMods.z }⟩) := by
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.sat) witness selected
    exact firstContract.orC_right firstUnit secondContract
  exact left.select right

/-- Generated support for all direct, alternate, and dissatisfaction paths of
    `or_d`. -/
theorem or_d
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨.B, secondMods⟩ flags txCtx) :
    CandidatePair.SupportsGeneratedContract
      ({ sat := firstPair.sat.select
           (firstPair.dsat.combine secondPair.sat)
         dsat := firstPair.dsat.combine secondPair.dsat } : CandidatePair)
      scriptCtx (.or_d first second)
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u
      }⟩ flags txCtx := by
  refine ⟨.or_d firstSupported.typed firstD firstUnit secondSupported.typed,
    ?_, ?_⟩
  · change (firstPair.sat.select
      (firstPair.dsat.combine secondPair.sat)).Supports _
    have left : firstPair.sat.Supports
        (fun witness => GeneratedContract (.or_d first second) witness true
          flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) :=
      firstSupported.sat.mono fun _ contract => contract.orD_left firstUnit
    have right : (firstPair.dsat.combine secondPair.sat).Supports
        (fun witness => GeneratedContract (.or_d first second) witness true
          flags txCtx ⟨.B, {
            z := firstMods.z && secondMods.z
            o := firstMods.o && secondMods.z
            d := secondMods.d
            u := secondMods.u }⟩) := by
      intro witness selected
      obtain ⟨firstWitness, secondWitness, rfl,
        firstContract, secondContract⟩ :=
        (firstSupported.dsat.combine secondSupported.sat) witness selected
      exact firstContract.orD_right firstUnit secondContract
    exact left.select right
  · change (firstPair.dsat.combine secondPair.dsat).Supports _
    intro witness selected
    obtain ⟨firstWitness, secondWitness, rfl,
      firstContract, secondContract⟩ :=
      (firstSupported.dsat.combine secondSupported.dsat) witness selected
    exact firstContract.orD_right firstUnit secondContract

private theorem orILeftSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedContract first witness expected flags txCtx ⟨base, firstMods⟩)
    (branch : branchBase base) :
    (result.withSelector trueElement).Supports fun witness =>
      GeneratedContract (.or_i first second) witness expected flags txCtx
        ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u
        }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector trueElement) witness selected
  cases base with
  | B => exact contract.orILeft_b
  | K => exact contract.orILeft_k
  | V => exact contract.orILeft_v
  | W => simp [branchBase] at branch

private theorem orIRightSupport
    {result : CandidateResult}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (supported : result.Supports fun witness =>
      GeneratedContract second witness expected flags txCtx ⟨base, secondMods⟩)
    (branch : branchBase base) :
    (result.withSelector falseElement).Supports fun witness =>
      GeneratedContract (.or_i first second) witness expected flags txCtx
        ⟨base, {
          o := firstMods.z && secondMods.z
          d := firstMods.d || secondMods.d
          u := firstMods.u && secondMods.u
        }⟩ := by
  intro witness selected
  obtain ⟨inner, rfl, contract⟩ :=
    (supported.withSelector falseElement) witness selected
  cases base with
  | B => exact contract.orIRight_b
  | K => exact contract.orIRight_k
  | V => exact contract.orIRight_v
  | W => simp [branchBase] at branch

/-- Generated support for both tagged branches of `or_i`, for each admissible
    B/K/V branch base and for both satisfaction projections. -/
theorem or_i
    {firstPair secondPair : CandidatePair} {scriptCtx : ScriptContext}
    {first second : CoreFragment} {base : BaseType}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨base, firstMods⟩ flags txCtx)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨base, secondMods⟩ flags txCtx) (branch : branchBase base) :
    CandidatePair.SupportsGeneratedContract
      ({ sat := (firstPair.sat.withSelector trueElement).select
           (secondPair.sat.withSelector falseElement)
         dsat := (firstPair.dsat.withSelector trueElement).select
           (secondPair.dsat.withSelector falseElement) } : CandidatePair)
      scriptCtx (.or_i first second)
      ⟨base, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ flags txCtx := by
  refine ⟨.or_i firstSupported.typed secondSupported.typed branch rfl, ?_, ?_⟩
  · change ((firstPair.sat.withSelector trueElement).select
      (secondPair.sat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.sat branch).select
      (orIRightSupport secondSupported.sat branch)
  · change ((firstPair.dsat.withSelector trueElement).select
      (secondPair.dsat.withSelector falseElement)).Supports _
    exact (orILeftSupport firstSupported.dsat branch).select
      (orIRightSupport secondSupported.dsat branch)

private theorem andorTrueSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedContract first witness true flags txCtx ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedContract second witness expected flags txCtx ⟨base, secondMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedContract (.andor first second third) witness expected flags txCtx
        ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u
        }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  cases base with
  | B => exact firstContract.andorTrue_b firstUnit branchContract
  | K => exact firstContract.andorTrue_k firstUnit branchContract
  | V => exact firstContract.andorTrue_v firstUnit branchContract
  | W => simp [branchBase] at branch

private theorem andorFalseSupport
    {firstResult branchResult : CandidateResult}
    {first second third : CoreFragment} {base : BaseType}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstResult.Supports fun witness =>
      GeneratedContract first witness false flags txCtx ⟨.B, firstMods⟩)
    (branchSupported : branchResult.Supports fun witness =>
      GeneratedContract third witness expected flags txCtx ⟨base, thirdMods⟩)
    (firstUnit : firstMods.u = true) (branch : branchBase base) :
    (firstResult.combine branchResult).Supports fun witness =>
      GeneratedContract (.andor first second third) witness expected flags txCtx
        ⟨base, {
          z := firstMods.z && secondMods.z && thirdMods.z
          o := (firstMods.z && secondMods.o && thirdMods.o) ||
            (firstMods.o && secondMods.z && thirdMods.z)
          d := thirdMods.d
          u := secondMods.u && thirdMods.u
        }⟩ := by
  intro witness selected
  obtain ⟨firstWitness, branchWitness, rfl, firstContract, branchContract⟩ :=
    (firstSupported.combine branchSupported) witness selected
  cases base with
  | B => exact firstContract.andorFalse_b firstUnit branchContract
  | K => exact firstContract.andorFalse_k firstUnit branchContract
  | V => exact firstContract.andorFalse_v firstUnit branchContract
  | W => simp [branchBase] at branch

/-- Generated support for every usable `andor` path. The non-canonical
    satisfying-selector dissatisfaction remains a real executable row. -/
theorem andor
    {firstPair secondPair thirdPair : CandidatePair}
    {scriptCtx : ScriptContext} {first second third : CoreFragment}
    {base : BaseType} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx) (firstD : firstMods.d = true)
    (firstUnit : firstMods.u = true)
    (secondSupported : secondPair.SupportsGeneratedContract scriptCtx second
      ⟨base, secondMods⟩ flags txCtx)
    (thirdSupported : thirdPair.SupportsGeneratedContract scriptCtx third
      ⟨base, thirdMods⟩ flags txCtx) (branch : branchBase base) :
    CandidatePair.SupportsGeneratedContract
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
        u := secondMods.u && thirdMods.u
      }⟩ flags txCtx := by
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
        firstSupported.sat secondSupported.dsat
        firstUnit branch)
    exact canonical.select noncanonical

/-! ## Threshold candidate composition -/

/-- Strong generated support for the exact-count threshold candidate formula.
    The arithmetic premise is the candidate guard's only condition not already
    carried by the Miniscript typing constructor. -/
theorem thresh
    {firstPair : CandidatePair} {restPairs : List CandidatePair}
    {scriptCtx : ScriptContext} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstSupported : firstPair.SupportsGeneratedContract scriptCtx first
      ⟨.B, firstMods⟩ flags txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedContractList scriptCtx flags txCtx
      restPairs fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    ({ sat := CandidatePair.selectExactly threshold (firstPair :: restPairs)
       dsat := CandidatePair.thresholdDissatisfaction threshold
         (CandidatePair.countCandidates (firstPair :: restPairs)) } :
      CandidatePair).SupportsGeneratedContract scriptCtx
      (.thresh threshold (first :: fragments))
      ⟨.B, {
        z := CorrectnessModifiers.allZ
          (firstMods :: MiniType.modifiers restTypes)
        o := CorrectnessModifiers.oneOWithRestZ
          (firstMods :: MiniType.modifiers restTypes)
        d := true
        u := true }⟩ flags txCtx := by
  have allSupported := restSupported.cons firstSupported
  have valid : candidateThresholdValid threshold (first :: fragments).length :=
    ⟨by omega, atMost, safe⟩
  refine ⟨.thresh firstSupported.typed firstD firstUnit restSupported.typed
    restTyped positive atMost, ?_, ?_⟩
  · change (CandidatePair.selectExactly threshold
      (firstPair :: restPairs)).Supports _
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.selectExactly_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    have generated := choices.generated allSupported
    apply GeneratedContract.b
    · simpa [MiniType.modifiers] using
        (generated.thresholdInput (expected := true) trace)
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack]
      exact generated.thresholdExecution firstUnit restTyped safe sumEq (by simp)
  · change (CandidatePair.thresholdDissatisfaction threshold
      (CandidatePair.countCandidates (firstPair :: restPairs))).Supports _
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.thresholdDissatisfaction_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    have generated := choices.generated allSupported
    apply GeneratedContract.b
    · simpa [MiniType.modifiers] using
        (generated.thresholdInput (expected := false) trace)
    · exact BooleanResultFacts.canonical false _ flags
    · rw [trace.toInitialStack]
      exact generated.thresholdExecution firstUnit restTyped
        (ArithmeticScriptNatSafe.of_lt (by decide)) sumEq
        (by simp [candidateThresholdValid_scriptNat_ne_zero valid])

end CandidatePair.SupportsGeneratedContract

/-- Recursive-facing threshold theorem for the executable candidate row. Child
    support is supplied in source order; typing and candidate validity follow
    from the same premises. -/
theorem generatedContract_thresh
    {scriptCtx : ScriptContext} {env : SatEnv} {first : CoreFragment}
    {fragments : List CoreFragment} {threshold : Nat}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {flags : ScriptFlags}
    (firstSupported : (satisfactionCandidates first env).SupportsGeneratedContract
      scriptCtx first ⟨.B, firstMods⟩ flags env.txCtx)
    (firstD : firstMods.d = true) (firstUnit : firstMods.u = true)
    (restSupported : SupportsGeneratedContractList scriptCtx flags env.txCtx
      (satisfactionCandidatesList fragments env) fragments restTypes)
    (restTyped : thresholdRestTypes restTypes)
    (positive : 1 ≤ threshold)
    (atMost : threshold ≤ (first :: fragments).length)
    (safe : ArithmeticScriptNatSafe threshold) :
    CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates (.thresh threshold (first :: fragments)) env)
      scriptCtx
        (.thresh threshold (first :: fragments))
        ⟨.B, {
          z := CorrectnessModifiers.allZ
            (firstMods :: MiniType.modifiers restTypes)
          o := CorrectnessModifiers.oneOWithRestZ
            (firstMods :: MiniType.modifiers restTypes)
          d := true
          u := true }⟩ flags env.txCtx := by
  have valid : candidateThresholdValid threshold (first :: fragments).length :=
    ⟨by omega, atMost, safe⟩
  rw [satisfactionCandidates_thresh_valid threshold (first :: fragments) env valid]
  simpa [satisfactionCandidatesList_eq_map] using
    (CandidatePair.SupportsGeneratedContract.thresh firstSupported firstD
      firstUnit restSupported restTyped positive atMost safe)

/-- An invalid raw threshold has no projected witness, while an explicit typing
    derivation still supplies the pair-global type carried by strong support. -/
theorem generatedContract_thresh_invalid
    {scriptCtx : ScriptContext} {env : SatEnv} {threshold : Nat}
    {fragments : List CoreFragment} {ty : MiniType} {flags : ScriptFlags}
    (typed : HasType scriptCtx (.thresh threshold fragments) ty)
    (invalid : ¬ candidateThresholdValid threshold fragments.length) :
    CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates (.thresh threshold fragments) env)
      scriptCtx (.thresh threshold fragments) ty
        flags env.txCtx := by
  rw [satisfactionCandidates_thresh_invalid threshold fragments env invalid]
  exact ⟨typed, CandidateResult.supports_impossible _,
    CandidateResult.supports_impossible _⟩

end LeanMiniscript.Miniscript
