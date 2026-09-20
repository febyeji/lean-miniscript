import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Properties.ResourceBounds

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Generated witness stack paths

The satisfaction algorithm builds witnesses compositionally. This module
tracks their item counts through the same path choices used by
`stackPathBounds`, independently of cryptographic or execution assumptions.
-/

/-- Final frame size contributed by each Miniscript base type when its complete
    generated witness is used. -/
private def baseWitnessResultOffset : BaseType → Int
  | .B | .W => 1
  | .V => 0
  | .K => 2

namespace StackTraceSet

/-- One generated witness fits a nonempty stack-path summary at a given final
    frame offset. -/
private def BoundsWitnessOffset (summary : StackTraceSet) (offset : Int)
    (witness : Witness) : Prop :=
  ∃ trace, summary = some trace ∧
    Int.ofNat witness.length ≤ trace.netDiff + offset

/-- Base-type specialization of `BoundsWitnessOffset`. -/
private def BoundsWitness (summary : StackTraceSet) (base : BaseType)
    (witness : Witness) : Prop :=
  BoundsWitnessOffset summary (baseWitnessResultOffset base) witness

private theorem BoundsWitnessOffset.choiceLeft
    {left right : StackTraceSet} {offset : Int} {witness : Witness}
    (bounded : BoundsWitnessOffset left offset witness) :
    BoundsWitnessOffset (StackTraceSet.choice left right) offset witness := by
  obtain ⟨leftTrace, rfl, bound⟩ := bounded
  cases right with
  | none => exact ⟨leftTrace, rfl, bound⟩
  | some rightTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl, by
        exact Int.le_trans bound
          (Int.add_le_add_right (Int.le_max_left _ _) offset)⟩

private theorem BoundsWitnessOffset.choiceRight
    {left right : StackTraceSet} {offset : Int} {witness : Witness}
    (bounded : BoundsWitnessOffset right offset witness) :
    BoundsWitnessOffset (StackTraceSet.choice left right) offset witness := by
  obtain ⟨rightTrace, rfl, bound⟩ := bounded
  cases left with
  | none => exact ⟨rightTrace, rfl, bound⟩
  | some leftTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl, by
        exact Int.le_trans bound
          (Int.add_le_add_right (Int.le_max_right _ _) offset)⟩

private theorem BoundsWitnessOffset.combine
    {left right : StackTraceSet} {leftOffset rightOffset : Int}
    {leftWitness rightWitness : Witness}
    (leftBounded : BoundsWitnessOffset left leftOffset leftWitness)
    (rightBounded : BoundsWitnessOffset right rightOffset rightWitness) :
    BoundsWitnessOffset (StackTraceSet.sequential left right)
      (leftOffset + rightOffset)
      (Witness.combine leftWitness rightWitness) := by
  obtain ⟨leftTrace, rfl, leftBound⟩ := leftBounded
  obtain ⟨rightTrace, rfl, rightBound⟩ := rightBounded
  refine ⟨leftTrace.sequential rightTrace, rfl, ?_⟩
  simp [Witness.combine, StackTraceBound.sequential] at *
  omega

/-- Append a fixed stack effect while changing the final-frame offset. -/
private theorem BoundsWitnessOffset.sequentialRight
    {summary : StackTraceSet} {sourceOffset targetOffset : Int}
    {witness : Witness} {suffix : StackTraceBound}
    (bounded : BoundsWitnessOffset summary sourceOffset witness)
    (offset : sourceOffset ≤ suffix.netDiff + targetOffset) :
    BoundsWitnessOffset
      (StackTraceSet.sequential summary (some suffix)) targetOffset witness := by
  obtain ⟨trace, rfl, bound⟩ := bounded
  refine ⟨trace.sequential suffix, rfl, ?_⟩
  simp only [StackTraceBound.sequential]
  omega

/-- Prepend a fixed stack effect while changing the final-frame offset. -/
private theorem BoundsWitnessOffset.sequentialLeft
    {summary : StackTraceSet} {sourceOffset targetOffset : Int}
    {witness : Witness} {prefixTrace : StackTraceBound}
    (bounded : BoundsWitnessOffset summary sourceOffset witness)
    (offset : sourceOffset ≤ prefixTrace.netDiff + targetOffset) :
    BoundsWitnessOffset
      (StackTraceSet.sequential (some prefixTrace) summary) targetOffset witness := by
  obtain ⟨trace, rfl, bound⟩ := bounded
  refine ⟨prefixTrace.sequential trace, rfl, ?_⟩
  simp only [StackTraceBound.sequential]
  omega

/-- A general prefix consumes a selector appended to the generated witness. -/
private theorem BoundsWitnessOffset.withSelectorPrefix
    {summary : StackTraceSet} {sourceOffset targetOffset : Int}
    {witness : Witness} {prefixTrace : StackTraceBound}
    (bounded : BoundsWitnessOffset summary sourceOffset witness)
    (offset : sourceOffset + 1 ≤ prefixTrace.netDiff + targetOffset)
    (selector : StackElement) :
    BoundsWitnessOffset
      (StackTraceSet.sequential (some prefixTrace) summary) targetOffset
      (Witness.withSelector witness selector) := by
  obtain ⟨trace, rfl, bound⟩ := bounded
  refine ⟨prefixTrace.sequential trace, rfl, ?_⟩
  simp [Witness.withSelector, StackTraceBound.sequential] at *
  omega

/-- Prepending a branch consumes the selector appended to a witness. -/
private theorem BoundsWitnessOffset.withSelector
    {summary : StackTraceSet} {offset : Int} {witness : Witness}
    (bounded : BoundsWitnessOffset summary offset witness)
    (selector : StackElement) :
    BoundsWitnessOffset
      (StackTraceSet.sequential (some StackTraceBound.branch) summary)
      offset (Witness.withSelector witness selector) := by
  obtain ⟨trace, rfl, bound⟩ := bounded
  refine ⟨StackTraceBound.branch.sequential trace, rfl, ?_⟩
  simp [Witness.withSelector, StackTraceBound.sequential,
    StackTraceBound.branch] at *
  omega

end StackTraceSet

/-- Candidate-wide witness-length support aligned with a typed fragment's
    satisfaction and dissatisfaction stack summaries. -/
private structure SupportsStackPathBounds (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports
    (StackTraceSet.BoundsWitness (stackPathBounds fragment).sat ty.base)
  dsat : pair.dsat.Supports
    (StackTraceSet.BoundsWitness (stackPathBounds fragment).dsat ty.base)

private theorem supportsBoundsChoice
    {left right : CandidateResult} {leftSummary rightSummary : StackTraceSet}
    {offset : Int}
    (leftSupported : left.Supports
      (StackTraceSet.BoundsWitnessOffset leftSummary offset))
    (rightSupported : right.Supports
      (StackTraceSet.BoundsWitnessOffset rightSummary offset)) :
    (left.select right).Supports
      (StackTraceSet.BoundsWitnessOffset
        (StackTraceSet.choice leftSummary rightSummary) offset) :=
  (leftSupported.mono fun _ bounded => bounded.choiceLeft).select
    (rightSupported.mono fun _ bounded => bounded.choiceRight)

private theorem supportsBoundsCombine
    {left right : CandidateResult} {leftSummary rightSummary : StackTraceSet}
    {leftOffset rightOffset : Int}
    (leftSupported : left.Supports
      (StackTraceSet.BoundsWitnessOffset leftSummary leftOffset))
    (rightSupported : right.Supports
      (StackTraceSet.BoundsWitnessOffset rightSummary rightOffset)) :
    (left.combine right).Supports
      (StackTraceSet.BoundsWitnessOffset
        (StackTraceSet.sequential leftSummary rightSummary)
        (leftOffset + rightOffset)) := by
  have combined := leftSupported.combine rightSupported
  exact combined.mono fun _ provenance => by
    obtain ⟨leftWitness, rightWitness, rfl, leftBound, rightBound⟩ := provenance
    exact leftBound.combine rightBound

private theorem supportsBoundsWithSelector
    {result : CandidateResult} {summary : StackTraceSet} {offset : Int}
    (supported : result.Supports
      (StackTraceSet.BoundsWitnessOffset summary offset))
    (selector : StackElement) :
    (result.withSelector selector).Supports
      (StackTraceSet.BoundsWitnessOffset
        (StackTraceSet.sequential (some StackTraceBound.branch) summary)
        offset) := by
  have selected := supported.withSelector selector
  exact selected.mono fun _ provenance => by
    obtain ⟨inner, rfl, bounded⟩ := provenance
    exact bounded.withSelector selector

/-- Source-order list support used by threshold children. -/
private inductive SupportsStackPathBoundsList (scriptCtx : ScriptContext) :
    List CandidatePair → List CoreFragment → List MiniType → Prop where
  | nil : SupportsStackPathBoundsList scriptCtx [] [] []
  | snoc {pairs : List CandidatePair} {fragments : List CoreFragment}
      {types : List MiniType} {pair : CandidatePair}
      {fragment : CoreFragment} {ty : MiniType}
      (prior : SupportsStackPathBoundsList scriptCtx pairs fragments types)
      (child : SupportsStackPathBounds pair scriptCtx fragment ty) :
      SupportsStackPathBoundsList scriptCtx (pairs ++ [pair])
        (fragments ++ [fragment]) (types ++ [ty])

namespace SupportsStackPathBoundsList

private theorem nil_inv {scriptCtx : ScriptContext}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsStackPathBoundsList scriptCtx [] fragments types) :
    fragments = [] ∧ types = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at supported
  cases supported with
  | nil => exact ⟨rfl, rfl⟩
  | snoc prior child => simp at pairsEq

private theorem snoc_inv {scriptCtx : ScriptContext}
    {pairs : List CandidatePair} {pair : CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsStackPathBoundsList scriptCtx (pairs ++ [pair])
      fragments types) :
    ∃ priorFragments priorTypes fragment ty,
      fragments = priorFragments ++ [fragment] ∧
      types = priorTypes ++ [ty] ∧
      SupportsStackPathBoundsList scriptCtx pairs priorFragments priorTypes ∧
      SupportsStackPathBounds pair scriptCtx fragment ty := by
  generalize pairsEq : pairs ++ [pair] = allPairs at supported
  cases supported with
  | nil => simp at pairsEq
  | @snoc otherPairs otherFragments otherTypes otherPair fragment ty prior child =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherFragments, otherTypes, fragment, ty, rfl, rfl, prior, child⟩

/-- Prepend one supported source child. -/
private theorem cons {scriptCtx : ScriptContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {pair : CandidatePair}
    {fragment : CoreFragment} {ty : MiniType}
    (child : SupportsStackPathBounds pair scriptCtx fragment ty)
    (rest : SupportsStackPathBoundsList scriptCtx pairs fragments types) :
    SupportsStackPathBoundsList scriptCtx (pair :: pairs)
      (fragment :: fragments) (ty :: types) := by
  induction rest with
  | nil => exact .snoc .nil child
  | snoc prior last ih => exact .snoc ih last

end SupportsStackPathBoundsList

/-- Every type in a threshold row contributes the same one-item result offset
    used by its B head and W tail. -/
private def thresholdTypeOffsets (types : List MiniType) : Prop :=
  ∀ ty ∈ types, baseWitnessResultOffset ty.base = 1

private theorem thresholdTypeOffsets_of_rest
    (firstMods : CorrectnessModifiers) {restTypes : List MiniType}
    (rest : thresholdRestTypes restTypes) :
    thresholdTypeOffsets (⟨.B, firstMods⟩ :: restTypes) := by
  intro ty member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · rfl
  · induction restTypes with
    | nil => simp at member
    | cons head tail ih =>
        simp only [thresholdRestTypes] at rest
        rcases rest with ⟨base, headD, headU, rest⟩
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp [base, baseWitnessResultOffset]
        · exact ih rest member

@[simp] private theorem stackPathBoundsList_eq_nil_iff
    (fragments : List CoreFragment) :
    stackPathBoundsList fragments = [] ↔ fragments = [] := by
  cases fragments <;> simp [stackPathBoundsList]

@[simp] private theorem stackPathBoundsList_append
    (left right : List CoreFragment) :
    stackPathBoundsList (left ++ right) =
      stackPathBoundsList left ++ stackPathBoundsList right := by
  induction left with
  | nil => rfl
  | cons fragment fragments ih => simp [stackPathBoundsList, ih]

/-- Exact-count candidate provenance transports to a concrete threshold stack
    path, while the combined witness keeps the path's correct aggregate offset. -/
private theorem CandidatePair.ChoiceTrace.toThresholdStackPath
    {scriptCtx : ScriptContext} {pairs : List CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    {count : Nat} {frames : List Witness} {witness : Witness}
    (trace : CandidatePair.ChoiceTrace pairs count frames witness)
    (supported : SupportsStackPathBoundsList scriptCtx pairs fragments types)
    (offsets : thresholdTypeOffsets types) :
    ∃ netDiff,
      ThresholdStackPath (stackPathBoundsList fragments) count netDiff ∧
      Int.ofNat witness.length ≤ netDiff + if fragments = [] then 0 else 1 := by
  induction trace generalizing fragments types with
  | nil =>
      obtain ⟨rfl, rfl⟩ := SupportsStackPathBoundsList.nil_inv supported
      exact ⟨0, .nil, by simp⟩
  | @sat pairs count frames witness pair childWitness prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsStackPathBoundsList.snoc_inv supported
      have priorOffsets : thresholdTypeOffsets priorTypes := by
        intro item member
        exact offsets item (by simp [member])
      have childOffset : baseWitnessResultOffset ty.base = 1 :=
        offsets ty (by simp)
      obtain ⟨priorNet, priorPath, priorBound⟩ :=
        ih priorSupported priorOffsets
      have childFit := childSupported.sat childWitness selected
      unfold StackTraceSet.BoundsWitness
        StackTraceSet.BoundsWitnessOffset at childFit
      obtain ⟨childTrace, childTraceEq, childBound⟩ := childFit
      rw [childOffset] at childBound
      change (childWitness.length : Int) ≤ childTrace.netDiff + 1 at childBound
      refine ⟨priorNet + childTrace.netDiff +
          (if priorFragments = [] then 0 else 1), ?_, ?_⟩
      · simpa [stackPathBoundsList] using
          ThresholdStackPath.sat priorPath childTraceEq
      · simp [Witness.combine, Int.add_assoc] at priorBound ⊢
        omega
  | @dsat pairs count frames witness pair childWitness prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsStackPathBoundsList.snoc_inv supported
      have priorOffsets : thresholdTypeOffsets priorTypes := by
        intro item member
        exact offsets item (by simp [member])
      have childOffset : baseWitnessResultOffset ty.base = 1 :=
        offsets ty (by simp)
      obtain ⟨priorNet, priorPath, priorBound⟩ :=
        ih priorSupported priorOffsets
      have childFit := childSupported.dsat childWitness selected
      unfold StackTraceSet.BoundsWitness
        StackTraceSet.BoundsWitnessOffset at childFit
      obtain ⟨childTrace, childTraceEq, childBound⟩ := childFit
      rw [childOffset] at childBound
      change (childWitness.length : Int) ≤ childTrace.netDiff + 1 at childBound
      refine ⟨priorNet + childTrace.netDiff +
          (if priorFragments = [] then 0 else 1), ?_, ?_⟩
      · simpa [stackPathBoundsList] using
          ThresholdStackPath.dsat priorPath childTraceEq
      · simp [Witness.combine, Int.add_assoc] at priorBound ⊢
        omega


private theorem listSnocInductionPaths {α : Type} {motive : List α → Prop}
    (nil : motive [])
    (snoc : ∀ (items : List α) (item : α),
      motive items → motive (items ++ [item])) :
    ∀ items, motive items := by
  intro items
  have reversed : motive items.reverse.reverse := by
    have aux : ∀ reversedItems : List α, motive reversedItems.reverse := by
      intro reversedItems
      induction reversedItems with
      | nil => simpa using nil
      | cons item reversedItems ih =>
          simpa using snoc reversedItems.reverse item ih
    exact aux items.reverse
  simpa using reversed

private theorem CandidatePair.ChoiceTrace.multiA_witness_length
    {env : SatEnv} {keys : List PubKey} {count : Nat}
    {frames : List Witness} {witness : Witness}
    (trace : CandidatePair.ChoiceTrace
      (keys.map fun key => multiAKeyChoice key env) count frames witness) :
    witness.length = keys.length := by
  induction keys using listSnocInductionPaths generalizing count frames witness with
  | nil =>
      simp only [List.map_nil] at trace
      generalize pairsEq : ([] : List CandidatePair) = pairs at trace
      cases trace
      · rfl
      · simp at pairsEq
      · simp at pairsEq
  | snoc keys key ih =>
      rw [List.map_append, List.map_singleton] at trace
      generalize pairsEq :
        (keys.map fun key => multiAKeyChoice key env) ++
          [multiAKeyChoice key env] = pairs at trace
      cases trace with
      | nil => simp at pairsEq
      | @sat children priorCount priorFrames priorWitness child childWitness
          prior selected =>
          have pairsEq' :
              (keys.map fun key => multiAKeyChoice key env).concat
                (multiAKeyChoice key env) = children.concat child := by
            simpa only [List.concat_eq_append] using pairsEq
          obtain ⟨childrenEq, childEq⟩ := List.concat_inj.mp pairsEq'
          subst children
          subst child
          cases selectedSig : env.signatureFor key with
          | none => simp [multiAKeyChoice, selectedSig] at selected
          | some signature =>
              have frameEq : childWitness = [signature] := by
                simpa [multiAKeyChoice, selectedSig] using selected.symm
              subst childWitness
              simp [Witness.combine, ih prior]
      | @dsat children priorCount priorFrames priorWitness child childWitness
          prior selected =>
          have pairsEq' :
              (keys.map fun key => multiAKeyChoice key env).concat
                (multiAKeyChoice key env) = children.concat child := by
            simpa only [List.concat_eq_append] using pairsEq
          obtain ⟨childrenEq, childEq⟩ := List.concat_inj.mp pairsEq'
          subst children
          subst child
          have frameEq : childWitness = [falseElement] := by
            simpa [multiAKeyChoice] using selected.symm
          subst childWitness
          simp [Witness.combine, ih prior]

mutual
private theorem supportsStackPathBounds_of_wellFormed_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx) :
    SupportsStackPathBounds (satisfactionCandidates fragment env)
      scriptCtx fragment ty := by
  cases typed with
  | zero =>
      refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
      apply CandidateResult.supports_usable
      exact ⟨StackTraceBound.push, rfl, by
        simp [baseWitnessResultOffset, StackTraceBound.push]⟩
  | one =>
      refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
      apply CandidateResult.supports_usable
      exact ⟨StackTraceBound.push, rfl, by
        simp [baseWitnessResultOffset, StackTraceBound.push]⟩
  | pk_k key =>
      refine ⟨.pk_k key, ?_, ?_⟩
      · cases selected : env.signatureFor key with
        | none => simp [satisfactionCandidates, keyCandidates, selected,
            CandidateResult.Supports]
        | some signature =>
            rw [show (satisfactionCandidates (.pk_k key) env).sat =
              .usable [signature] true by
                simp [satisfactionCandidates, keyCandidates, selected]]
            apply CandidateResult.supports_usable
            exact ⟨StackTraceBound.push, rfl, by
              simp [baseWitnessResultOffset, StackTraceBound.push]⟩
      · apply CandidateResult.supports_usable
        exact ⟨StackTraceBound.push, rfl, by
          simp [baseWitnessResultOffset, StackTraceBound.push]⟩
  | pk_h key =>
      refine ⟨.pk_h key, ?_, ?_⟩
      · cases selected : env.signatureFor key with
        | none => simp [satisfactionCandidates, keyCandidates, selected,
            CandidateResult.Supports]
        | some signature =>
            rw [show (satisfactionCandidates (.pk_h key) env).sat =
              .usable [signature, key.bytes] true by
                simp [satisfactionCandidates, keyCandidates, selected]]
            apply CandidateResult.supports_usable
            exact ⟨_, rfl, by
              simp [baseWitnessResultOffset, StackTraceBound.sequential,
                StackTraceBound.dup, StackTraceBound.hash, StackTraceBound.push,
                StackTraceBound.equalVerify]⟩
      · apply CandidateResult.supports_usable
        exact ⟨_, rfl, by
          simp [baseWitnessResultOffset, StackTraceBound.sequential,
            StackTraceBound.dup, StackTraceBound.hash, StackTraceBound.push,
            StackTraceBound.equalVerify]⟩
  | older n =>
      refine ⟨.older n, ?_, CandidateResult.supports_impossible _⟩
      by_cases satisfied : sequenceSatisfied n env.txCtx
      · rw [show (satisfactionCandidates (.older n) env).sat =
          .usable [] false by simp [satisfactionCandidates, satisfied]]
        apply CandidateResult.supports_usable
        exact ⟨_, rfl, by
          simp [baseWitnessResultOffset, StackTraceBound.sequential,
            StackTraceBound.push, StackTraceBound.nop]⟩
      · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]
  | after n =>
      refine ⟨.after n, ?_, CandidateResult.supports_impossible _⟩
      by_cases satisfied : locktimeSatisfied n env.txCtx
      · rw [show (satisfactionCandidates (.after n) env).sat =
          .usable [] false by simp [satisfactionCandidates, satisfied]]
        apply CandidateResult.supports_usable
        exact ⟨_, rfl, by
          simp [baseWitnessResultOffset, StackTraceBound.sequential,
            StackTraceBound.push, StackTraceBound.nop]⟩
      · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]
  | sha256 hash =>
      refine ⟨.sha256 hash, ?_, by
        simp [satisfactionCandidates, hashCandidates, CandidateResult.Supports]⟩
      cases selected : env.preimageFor (.sha256 hash) with
      | none => simp [satisfactionCandidates, hashCandidates, selected,
          CandidateResult.Supports]
      | some preimage =>
          rw [show (satisfactionCandidates (.sha256 hash) env).sat =
            .usable [preimage] false by
              simp [satisfactionCandidates, hashCandidates, selected]]
          apply CandidateResult.supports_usable
          exact ⟨_, rfl, by
            simp [baseWitnessResultOffset, StackTraceBound.sequential,
              StackTraceBound.size, StackTraceBound.push,
              StackTraceBound.equalVerify, StackTraceBound.hash,
              StackTraceBound.equal]⟩
  | hash256 hash =>
      refine ⟨.hash256 hash, ?_, by
        simp [satisfactionCandidates, hashCandidates, CandidateResult.Supports]⟩
      cases selected : env.preimageFor (.hash256 hash) with
      | none => simp [satisfactionCandidates, hashCandidates, selected,
          CandidateResult.Supports]
      | some preimage =>
          rw [show (satisfactionCandidates (.hash256 hash) env).sat =
            .usable [preimage] false by
              simp [satisfactionCandidates, hashCandidates, selected]]
          apply CandidateResult.supports_usable
          exact ⟨_, rfl, by
            simp [baseWitnessResultOffset, StackTraceBound.sequential,
              StackTraceBound.size, StackTraceBound.push,
              StackTraceBound.equalVerify, StackTraceBound.hash,
              StackTraceBound.equal]⟩
  | ripemd160 hash =>
      refine ⟨.ripemd160 hash, ?_, by
        simp [satisfactionCandidates, hashCandidates, CandidateResult.Supports]⟩
      cases selected : env.preimageFor (.ripemd160 hash) with
      | none => simp [satisfactionCandidates, hashCandidates, selected,
          CandidateResult.Supports]
      | some preimage =>
          rw [show (satisfactionCandidates (.ripemd160 hash) env).sat =
            .usable [preimage] false by
              simp [satisfactionCandidates, hashCandidates, selected]]
          apply CandidateResult.supports_usable
          exact ⟨_, rfl, by
            simp [baseWitnessResultOffset, StackTraceBound.sequential,
              StackTraceBound.size, StackTraceBound.push,
              StackTraceBound.equalVerify, StackTraceBound.hash,
              StackTraceBound.equal]⟩
  | hash160 hash =>
      refine ⟨.hash160 hash, ?_, by
        simp [satisfactionCandidates, hashCandidates, CandidateResult.Supports]⟩
      cases selected : env.preimageFor (.hash160 hash) with
      | none => simp [satisfactionCandidates, hashCandidates, selected,
          CandidateResult.Supports]
      | some preimage =>
          rw [show (satisfactionCandidates (.hash160 hash) env).sat =
            .usable [preimage] false by
              simp [satisfactionCandidates, hashCandidates, selected]]
          apply CandidateResult.supports_usable
          exact ⟨_, rfl, by
            simp [baseWitnessResultOffset, StackTraceBound.sequential,
              StackTraceBound.size, StackTraceBound.push,
              StackTraceBound.equalVerify, StackTraceBound.hash,
              StackTraceBound.equal]⟩
  | @and_v first second firstMods secondType firstTyped secondTyped branch =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2.1
      have firstSat := firstSupported.sat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 0) at firstSat
      have secondSat := secondSupported.sat
      change (satisfactionCandidates second env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat
          (baseWitnessResultOffset secondType.base)) at secondSat
      have secondDsat := secondSupported.dsat
      change (satisfactionCandidates second env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat
          (baseWitnessResultOffset secondType.base)) at secondDsat
      refine ⟨.and_v firstTyped secondTyped branch, ?_, ?_⟩
      · change ((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).Supports
            (StackTraceSet.BoundsWitnessOffset
              (StackTraceSet.sequential (stackPathBounds first).sat
                (stackPathBounds second).sat)
              (baseWitnessResultOffset secondType.base))
        simpa using supportsBoundsCombine firstSat secondSat
      · change ((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).markNonCanonical.Supports
            (StackTraceSet.BoundsWitnessOffset
              (StackTraceSet.sequential (stackPathBounds first).sat
                (stackPathBounds second).dsat)
              (baseWitnessResultOffset secondType.base))
        simpa using (supportsBoundsCombine firstSat secondDsat).markNonCanonical
  | @and_b first second firstMods secondMods firstTyped secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2.1
      have binarySupport : ∀ {left right : CandidateResult}
          {leftSummary rightSummary : StackTraceSet},
          left.Supports (StackTraceSet.BoundsWitnessOffset leftSummary 1) →
          right.Supports (StackTraceSet.BoundsWitnessOffset rightSummary 1) →
          (left.combine right).Supports
            (StackTraceSet.BoundsWitnessOffset
              (StackTraceSet.sequential
                (StackTraceSet.sequential leftSummary rightSummary)
                (some StackTraceBound.binary)) 1) := by
        intro left right leftSummary rightSummary leftOk rightOk
        have combined := supportsBoundsCombine leftOk rightOk
        exact combined.mono fun _ bounded =>
          bounded.sequentialRight (by simp [StackTraceBound.binary])
      have firstSat := firstSupported.sat
      have firstDsat := firstSupported.dsat
      have secondSat := secondSupported.sat
      have secondDsat := secondSupported.dsat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at firstSat
      change (satisfactionCandidates first env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 1) at firstDsat
      change (satisfactionCandidates second env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat 1) at secondSat
      change (satisfactionCandidates second env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat 1) at secondDsat
      have satBound := binarySupport firstSat secondSat
      have dsatBound := binarySupport firstDsat secondDsat
      refine ⟨.and_b firstTyped secondTyped, ?_, ?_⟩
      · change ((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).sat).Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential
              (StackTraceSet.sequential (stackPathBounds first).sat
                (stackPathBounds second).sat)
              (some StackTraceBound.binary)) 1)
        exact satBound
      · change (((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).select
            (((satisfactionCandidates first env).dsat.combine
              (satisfactionCandidates second env).sat).markOvercomplete) |>.select
            (((satisfactionCandidates first env).sat.combine
              (satisfactionCandidates second env).dsat).markOvercomplete)).Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential
              (StackTraceSet.sequential (stackPathBounds first).dsat
                (stackPathBounds second).dsat)
              (some StackTraceBound.binary)) 1)
        exact (dsatBound.select
          (CandidateResult.supports_markOvercomplete _ _)).select
          (CandidateResult.supports_markOvercomplete _ _)
  | @or_b first second firstMods secondMods firstTyped firstD secondTyped secondD =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2
      have firstSat := firstSupported.sat
      have firstDsat := firstSupported.dsat
      have secondSat := secondSupported.sat
      have secondDsat := secondSupported.dsat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at firstSat
      change (satisfactionCandidates first env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 1) at firstDsat
      change (satisfactionCandidates second env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat 1) at secondSat
      change (satisfactionCandidates second env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat 1) at secondDsat
      let leftSummary := StackTraceSet.sequential
        (stackPathBounds first).sat (stackPathBounds second).dsat
      let rightSummary := StackTraceSet.sequential
        (stackPathBounds first).dsat (stackPathBounds second).sat
      let satSummary := StackTraceSet.sequential
        (StackTraceSet.choice leftSummary rightSummary)
        (some StackTraceBound.binary)
      have leftPath := supportsBoundsCombine firstSat secondDsat
      have rightPath := supportsBoundsCombine firstDsat secondSat
      have leftBound :
          ((satisfactionCandidates first env).sat.combine
            (satisfactionCandidates second env).dsat).Supports
            (StackTraceSet.BoundsWitnessOffset satSummary 1) :=
        leftPath.mono fun _ bounded =>
          (bounded.choiceLeft (right := rightSummary)).sequentialRight
            (by simp [StackTraceBound.binary])
      have rightBound :
          ((satisfactionCandidates first env).dsat.combine
            (satisfactionCandidates second env).sat).Supports
            (StackTraceSet.BoundsWitnessOffset satSummary 1) :=
        rightPath.mono fun _ bounded =>
          (bounded.choiceRight (left := leftSummary)).sequentialRight
            (by simp [StackTraceBound.binary])
      have dsatCombined := supportsBoundsCombine firstDsat secondDsat
      have dsatBound := dsatCombined.mono fun _ bounded =>
        bounded.sequentialRight (suffix := StackTraceBound.binary)
          (targetOffset := 1)
          (by simp [StackTraceBound.binary])
      refine ⟨.or_b firstTyped firstD secondTyped secondD, ?_, ?_⟩
      · change (((satisfactionCandidates first env).sat.combine
          (satisfactionCandidates second env).dsat).select
            ((satisfactionCandidates first env).dsat.combine
              (satisfactionCandidates second env).sat) |>.select
            (((satisfactionCandidates first env).sat.combine
              (satisfactionCandidates second env).sat).markOvercomplete)).Supports
          (StackTraceSet.BoundsWitnessOffset satSummary 1)
        exact (leftBound.select rightBound).select
          (CandidateResult.supports_markOvercomplete _ _)
      · change ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential
              (StackTraceSet.sequential (stackPathBounds first).dsat
                (stackPathBounds second).dsat)
              (some StackTraceBound.binary)) 1)
        exact dsatBound
  | @or_c first second firstMods secondMods firstTyped firstD firstUnit secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2
      have firstSat := firstSupported.sat
      have firstDsat := firstSupported.dsat
      have secondSat := secondSupported.sat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at firstSat
      change (satisfactionCandidates first env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 1) at firstDsat
      change (satisfactionCandidates second env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat 0) at secondSat
      let leftSummary := StackTraceSet.sequential (stackPathBounds first).sat
        (some StackTraceBound.branch)
      let rightSummary := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.branch)) (stackPathBounds second).sat
      have leftBound := firstSat.mono fun _ bounded =>
        bounded.sequentialRight (suffix := StackTraceBound.branch)
          (targetOffset := 0) (by simp [StackTraceBound.branch])
      have firstFalse := firstDsat.mono fun _ bounded =>
        bounded.sequentialRight (suffix := StackTraceBound.branch)
          (targetOffset := 0) (by simp [StackTraceBound.branch])
      have rightBound := supportsBoundsCombine firstFalse secondSat
      refine ⟨.or_c firstTyped firstD firstUnit secondTyped, ?_,
        CandidateResult.supports_impossible _⟩
      change ((satisfactionCandidates first env).sat.select
          ((satisfactionCandidates first env).dsat.combine
            (satisfactionCandidates second env).sat)).Supports
        (StackTraceSet.BoundsWitnessOffset
          (StackTraceSet.choice leftSummary rightSummary) 0)
      exact supportsBoundsChoice leftBound rightBound
  | @or_d first second firstMods secondMods firstTyped firstD firstUnit secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2
      have firstSat := firstSupported.sat
      have firstDsat := firstSupported.dsat
      have secondSat := secondSupported.sat
      have secondDsat := secondSupported.dsat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at firstSat
      change (satisfactionCandidates first env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 1) at firstDsat
      change (satisfactionCandidates second env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat 1) at secondSat
      change (satisfactionCandidates second env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat 1) at secondDsat
      let leftSummary := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).sat
          (some StackTraceBound.ifdupTrue)) (some StackTraceBound.branch)
      let falsePrefix := StackTraceSet.sequential
        (StackTraceSet.sequential (stackPathBounds first).dsat
          (some StackTraceBound.ifdupFalse)) (some StackTraceBound.branch)
      let rightSatSummary := StackTraceSet.sequential falsePrefix
        (stackPathBounds second).sat
      let rightDsatSummary := StackTraceSet.sequential falsePrefix
        (stackPathBounds second).dsat
      have leftBound := firstSat.mono fun _ bounded =>
        (bounded.sequentialRight (suffix := StackTraceBound.ifdupTrue)
          (targetOffset := 2) (by simp [StackTraceBound.ifdupTrue])).sequentialRight
            (suffix := StackTraceBound.branch) (targetOffset := 1)
            (by simp [StackTraceBound.branch])
      have firstFalse := firstDsat.mono fun _ bounded =>
        (bounded.sequentialRight (suffix := StackTraceBound.ifdupFalse)
          (targetOffset := 1) (by simp [StackTraceBound.ifdupFalse])).sequentialRight
            (suffix := StackTraceBound.branch) (targetOffset := 0)
            (by simp [StackTraceBound.branch])
      have rightSatBound := supportsBoundsCombine firstFalse secondSat
      have rightDsatBound := supportsBoundsCombine firstFalse secondDsat
      refine ⟨.or_d firstTyped firstD firstUnit secondTyped, ?_, ?_⟩
      · change ((satisfactionCandidates first env).sat.select
          ((satisfactionCandidates first env).dsat.combine
            (satisfactionCandidates second env).sat)).Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.choice leftSummary rightSatSummary) 1)
        exact supportsBoundsChoice leftBound rightSatBound
      · change ((satisfactionCandidates first env).dsat.combine
          (satisfactionCandidates second env).dsat).Supports
          (StackTraceSet.BoundsWitnessOffset rightDsatSummary 1)
        exact rightDsatBound
  | @or_i first second firstType secondType firstTyped secondTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2
      cases firstType with
      | mk firstBase firstMods =>
        cases secondType with
        | mk secondBase secondMods =>
          change firstBase = secondBase at baseEq
          subst secondBase
          let satSummary := StackTraceSet.choice
            (stackPathBounds first).sat (stackPathBounds second).sat
          let dsatSummary := StackTraceSet.choice
            (stackPathBounds first).dsat (stackPathBounds second).dsat
          have firstSat := firstSupported.sat
          have secondSat := secondSupported.sat
          have firstDsat := firstSupported.dsat
          have secondDsat := secondSupported.dsat
          change (satisfactionCandidates first env).sat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat
              (baseWitnessResultOffset firstBase)) at firstSat
          change (satisfactionCandidates second env).sat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat
              (baseWitnessResultOffset firstBase)) at secondSat
          change (satisfactionCandidates first env).dsat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat
              (baseWitnessResultOffset firstBase)) at firstDsat
          change (satisfactionCandidates second env).dsat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat
              (baseWitnessResultOffset firstBase)) at secondDsat
          have firstSatCommon := firstSat.mono fun _ bounded =>
            bounded.choiceLeft (right := (stackPathBounds second).sat)
          have secondSatCommon := secondSat.mono fun _ bounded =>
            bounded.choiceRight (left := (stackPathBounds first).sat)
          have firstDsatCommon := firstDsat.mono fun _ bounded =>
            bounded.choiceLeft (right := (stackPathBounds second).dsat)
          have secondDsatCommon := secondDsat.mono fun _ bounded =>
            bounded.choiceRight (left := (stackPathBounds first).dsat)
          refine ⟨.or_i firstTyped secondTyped branch rfl, ?_, ?_⟩
          · change (((satisfactionCandidates first env).sat.withSelector
                trueElement).select
              ((satisfactionCandidates second env).sat.withSelector
                falseElement)).Supports
              (StackTraceSet.BoundsWitnessOffset
                (StackTraceSet.sequential (some StackTraceBound.branch)
                  satSummary) (baseWitnessResultOffset firstBase))
            exact (supportsBoundsWithSelector firstSatCommon trueElement).select
              (supportsBoundsWithSelector secondSatCommon falseElement)
          · change (((satisfactionCandidates first env).dsat.withSelector
                trueElement).select
              ((satisfactionCandidates second env).dsat.withSelector
                falseElement)).Supports
              (StackTraceSet.BoundsWitnessOffset
                (StackTraceSet.sequential (some StackTraceBound.branch)
                  dsatSummary) (baseWitnessResultOffset firstBase))
            exact (supportsBoundsWithSelector firstDsatCommon trueElement).select
              (supportsBoundsWithSelector secondDsatCommon falseElement)
  | @andor first second third firstMods secondType thirdType firstTyped firstD
      firstUnit secondTyped thirdTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have firstSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed.1
      have secondSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) secondTyped wellFormed.2.1
      have thirdSupported := supportsStackPathBounds_of_wellFormed_hasType (env := env) thirdTyped wellFormed.2.2.1
      cases secondType with
      | mk secondBase secondMods =>
        cases thirdType with
        | mk thirdBase thirdMods =>
          change secondBase = thirdBase at baseEq
          subst thirdBase
          have firstSat := firstSupported.sat
          have firstDsat := firstSupported.dsat
          have secondSat := secondSupported.sat
          have secondDsat := secondSupported.dsat
          have thirdSat := thirdSupported.sat
          have thirdDsat := thirdSupported.dsat
          change (satisfactionCandidates first env).sat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at firstSat
          change (satisfactionCandidates first env).dsat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 1) at firstDsat
          change (satisfactionCandidates second env).sat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).sat
              (baseWitnessResultOffset secondBase)) at secondSat
          change (satisfactionCandidates second env).dsat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds second).dsat
              (baseWitnessResultOffset secondBase)) at secondDsat
          change (satisfactionCandidates third env).sat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds third).sat
              (baseWitnessResultOffset secondBase)) at thirdSat
          change (satisfactionCandidates third env).dsat.Supports
            (StackTraceSet.BoundsWitnessOffset (stackPathBounds third).dsat
              (baseWitnessResultOffset secondBase)) at thirdDsat
          have firstTrue := firstSat.mono fun _ bounded =>
            bounded.sequentialRight (suffix := StackTraceBound.branch)
              (targetOffset := 0) (by simp [StackTraceBound.branch])
          have firstFalse := firstDsat.mono fun _ bounded =>
            bounded.sequentialRight (suffix := StackTraceBound.branch)
              (targetOffset := 0) (by simp [StackTraceBound.branch])
          let trueSatSummary := StackTraceSet.sequential
            (StackTraceSet.sequential (stackPathBounds first).sat
              (some StackTraceBound.branch)) (stackPathBounds second).sat
          let falseSatSummary := StackTraceSet.sequential
            (StackTraceSet.sequential (stackPathBounds first).dsat
              (some StackTraceBound.branch)) (stackPathBounds third).sat
          let falseDsatSummary := StackTraceSet.sequential
            (StackTraceSet.sequential (stackPathBounds first).dsat
              (some StackTraceBound.branch)) (stackPathBounds third).dsat
          let trueDsatSummary := StackTraceSet.sequential
            (StackTraceSet.sequential (stackPathBounds first).sat
              (some StackTraceBound.branch)) (stackPathBounds second).dsat
          have trueSatBound := supportsBoundsCombine firstTrue secondSat
          have falseSatBound := supportsBoundsCombine firstFalse thirdSat
          have falseDsatBound := supportsBoundsCombine firstFalse thirdDsat
          have trueDsatBound := supportsBoundsCombine firstTrue secondDsat
          refine ⟨.andor firstTyped firstD firstUnit secondTyped thirdTyped branch rfl,
            ?_, ?_⟩
          · change (((satisfactionCandidates first env).sat.combine
                (satisfactionCandidates second env).sat).select
              ((satisfactionCandidates first env).dsat.combine
                (satisfactionCandidates third env).sat)).Supports
              (StackTraceSet.BoundsWitnessOffset
                (StackTraceSet.choice trueSatSummary falseSatSummary)
                (baseWitnessResultOffset secondBase))
            exact supportsBoundsChoice
              (by simpa [trueSatSummary] using trueSatBound)
              (by simpa [falseSatSummary] using falseSatBound)
          · change (((satisfactionCandidates first env).dsat.combine
                (satisfactionCandidates third env).dsat).select
              (((satisfactionCandidates first env).sat.combine
                (satisfactionCandidates second env).dsat).markNonCanonical)).Supports
              (StackTraceSet.BoundsWitnessOffset
                (StackTraceSet.choice falseDsatSummary trueDsatSummary)
                (baseWitnessResultOffset secondBase))
            exact supportsBoundsChoice
              (by simpa [falseDsatSummary] using falseDsatBound)
              (by simpa [trueDsatSummary] using
                trueDsatBound.markNonCanonical)
  | @c_wrap first firstMods firstTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      have sat := supported.sat
      have dsat := supported.dsat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 2) at sat
      change (satisfactionCandidates first env).dsat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).dsat 2) at dsat
      refine ⟨.c_wrap firstTyped, ?_, ?_⟩
      · change (satisfactionCandidates first env).sat.Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential (stackPathBounds first).sat
              (some StackTraceBound.checkSig)) 1)
        exact sat.mono fun _ bounded =>
          bounded.sequentialRight (by simp [StackTraceBound.checkSig])
      · change (satisfactionCandidates first env).dsat.Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential (stackPathBounds first).dsat
              (some StackTraceBound.checkSig)) 1)
        exact dsat.mono fun _ bounded =>
          bounded.sequentialRight (by simp [StackTraceBound.checkSig])
  | @v_wrap first firstMods firstTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      have sat := supported.sat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at sat
      refine ⟨.v_wrap firstTyped, ?_, CandidateResult.supports_impossible _⟩
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset
          (StackTraceSet.sequential (stackPathBounds first).sat
            (some StackTraceBound.verify)) 0)
      exact sat.mono fun _ bounded =>
        bounded.sequentialRight (by simp [StackTraceBound.verify])
  | @a_wrap first firstMods firstTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      simpa [satisfactionCandidates, stackPathBounds,
        StackTraceSet.BoundsWitness, baseWitnessResultOffset] using
        ⟨HasType.a_wrap firstTyped, supported.sat, supported.dsat⟩
  | @s_wrap first firstMods firstTyped firstOne =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      simpa [satisfactionCandidates, stackPathBounds,
        StackTraceSet.BoundsWitness, baseWitnessResultOffset] using
        ⟨HasType.s_wrap firstTyped firstOne, supported.sat, supported.dsat⟩
  | @d_wrap first firstMods firstTyped firstZero =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      have sat := supported.sat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 0) at sat
      let prefixTrace := StackTraceBound.dup.sequential StackTraceBound.branch
      refine ⟨.d_wrap firstTyped firstZero, ?_, ?_⟩
      · change ((satisfactionCandidates first env).sat.withSelector
            trueElement).Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential (some prefixTrace)
              (stackPathBounds first).sat) 1)
        have selected := sat.withSelector trueElement
        exact selected.mono fun _ provenance => by
          obtain ⟨inner, rfl, bounded⟩ := provenance
          exact bounded.withSelectorPrefix
            (prefixTrace := prefixTrace)
            (by simp [prefixTrace, StackTraceBound.sequential,
              StackTraceBound.dup, StackTraceBound.branch]) trueElement
      · apply CandidateResult.supports_usable
        exact ⟨prefixTrace, rfl, by
          simp [baseWitnessResultOffset, prefixTrace,
            StackTraceBound.sequential, StackTraceBound.dup,
            StackTraceBound.branch]⟩
  | @j_wrap first firstMods firstTyped firstNonzero =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      have sat := supported.sat
      change (satisfactionCandidates first env).sat.Supports
        (StackTraceSet.BoundsWitnessOffset (stackPathBounds first).sat 1) at sat
      let prefixTrace := StackTraceBound.size
        |>.sequential StackTraceBound.zeroNotEqual
        |>.sequential StackTraceBound.branch
      refine ⟨.j_wrap firstTyped firstNonzero, ?_, ?_⟩
      · change (satisfactionCandidates first env).sat.Supports
          (StackTraceSet.BoundsWitnessOffset
            (StackTraceSet.sequential (some prefixTrace)
              (stackPathBounds first).sat) 1)
        exact sat.mono fun _ bounded =>
          bounded.sequentialLeft
            (prefixTrace := prefixTrace) (targetOffset := 1)
            (by simp [prefixTrace, StackTraceBound.sequential,
              StackTraceBound.size, StackTraceBound.zeroNotEqual,
              StackTraceBound.branch])
      · intro witness selected
        have witnessShape := CandidateResult.usable_false_select_witness selected
        subst witness
        exact ⟨prefixTrace, rfl, by
          simp [baseWitnessResultOffset, prefixTrace, StackTraceBound.sequential,
            StackTraceBound.size, StackTraceBound.zeroNotEqual,
            StackTraceBound.branch]⟩
  | @n_wrap first firstMods firstTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have supported := supportsStackPathBounds_of_wellFormed_hasType (env := env) firstTyped wellFormed
      simpa [satisfactionCandidates, stackPathBounds,
        StackTraceSet.BoundsWitness, baseWitnessResultOffset] using
        ⟨HasType.n_wrap firstTyped, supported.sat, supported.dsat⟩
  | @thresh threshold first rest firstMods restTypes firstTyped firstD firstUnit
      restTyped restThreshold positive atMost =>
      by_cases valid : candidateThresholdValid threshold (first :: rest).length
      · have childrenWellFormed := wellFormed.2.1
        simp only [CoreFragment.allWellFormed] at childrenWellFormed
        have firstSupported := supportsStackPathBounds_of_wellFormed_hasType
          (env := env) firstTyped childrenWellFormed.1
        have restSupported := supportsStackPathBoundsList_of_allWellFormed_hasTypeList
          (env := env) restTyped childrenWellFormed.2
        have allSupported := SupportsStackPathBoundsList.cons
          firstSupported restSupported
        simp only [satisfactionCandidatesList_eq_map] at allSupported
        have offsets := thresholdTypeOffsets_of_rest firstMods restThreshold
        rw [satisfactionCandidates_thresh_valid threshold (first :: rest) env valid]
        refine ⟨.thresh firstTyped firstD firstUnit restTyped restThreshold
          positive atMost, ?_, ?_⟩
        · change (CandidatePair.selectExactly threshold
            (List.map (fun fragment => satisfactionCandidates fragment env)
              (first :: rest))).Supports
            (StackTraceSet.BoundsWitness
              (stackPathBounds (.thresh threshold (first :: rest))).sat .B)
          intro witness selected
          obtain ⟨frames, trace⟩ :=
            CandidatePair.selectExactly_choiceTrace selected
          obtain ⟨netDiff, path, witnessBound⟩ :=
            LeanMiniscript.Properties.CandidatePair.ChoiceTrace.toThresholdStackPath
              trace allSupported offsets
          simp only [List.cons_ne_nil, ↓reduceIte] at witnessBound
          obtain ⟨summaryTrace, summaryEq, pathBound⟩ := path.bounds_thresh
          refine ⟨summaryTrace, summaryEq, ?_⟩
          simp only [baseWitnessResultOffset]
          omega
        · change (CandidatePair.thresholdDissatisfaction threshold
            (CandidatePair.countCandidates
              (List.map (fun fragment => satisfactionCandidates fragment env)
                (first :: rest)))).Supports
            (StackTraceSet.BoundsWitness
              (stackPathBounds (.thresh threshold (first :: rest))).dsat .B)
          intro witness selected
          obtain ⟨frames, trace⟩ :=
            CandidatePair.thresholdDissatisfaction_choiceTrace selected
          obtain ⟨netDiff, path, witnessBound⟩ :=
            LeanMiniscript.Properties.CandidatePair.ChoiceTrace.toThresholdStackPath
              trace allSupported offsets
          simp only [List.cons_ne_nil, ↓reduceIte] at witnessBound
          obtain ⟨summaryTrace, summaryEq, pathBound⟩ :=
            path.bounds_thresh_dsat (threshold := threshold)
          refine ⟨summaryTrace, summaryEq, ?_⟩
          simp only [baseWitnessResultOffset]
          omega
      · rw [satisfactionCandidates_thresh_invalid threshold (first :: rest) env valid]
        exact ⟨.thresh firstTyped firstD firstUnit restTyped restThreshold
          positive atMost, CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩
  | multi threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
        simpa [validLegacyMultiKeyCount, maxPubKeysPerMultiSig] using
          wellFormed.2.2.1
      have guard : ¬ (threshold = 0 ∨ keys.length < threshold ∨
          maxPubKeysPerMultiSig < keys.length) := by
        simp only [not_or]
        exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBound⟩
      rw [satisfactionCandidates_multi]
      refine ⟨.multi threshold keys positive atMost, ?_, ?_⟩
      · rw [show (legacyMultiCandidates threshold keys env).sat =
          finalizeLegacyMulti (CandidatePair.selectExactly threshold
            (keys.map fun key => legacyMultiKeyChoice key env)) by
            simp [legacyMultiCandidates, guard]]
        intro witness selected
        rw [CandidateResult.finalizeLegacyMulti_usableWitness_iff] at selected
        obtain ⟨inner, innerSelected, rfl⟩ := selected
        obtain ⟨frames, trace⟩ :=
          CandidatePair.selectExactly_choiceTrace innerSelected
        have signatureCount := trace.toOrderedMultiSignatures.2
        refine ⟨{
          netDiff := Int.ofNat threshold
          exec := Int.ofNat (threshold + keys.length + 2) }, rfl, ?_⟩
        simp [signatureCount, baseWitnessResultOffset]
      · rw [show (legacyMultiCandidates threshold keys env).dsat =
          .usable (List.replicate (threshold + 1) falseElement) false by
            simp [legacyMultiCandidates, guard]]
        apply CandidateResult.supports_usable
        refine ⟨{
          netDiff := Int.ofNat threshold
          exec := Int.ofNat (threshold + keys.length + 2) }, rfl, ?_⟩
        simp [baseWitnessResultOffset]
  | multi_a threshold keys positive atMost =>
      by_cases valid : candidateThresholdValid threshold keys.length
      · refine ⟨.multi_a threshold keys positive atMost, ?_, ?_⟩
        · rw [show (satisfactionCandidates (.multi_a threshold keys) env).sat =
            CandidatePair.selectExactly threshold
              (keys.map fun key => multiAKeyChoice key env) by
              simp [multiACandidates, valid]]
          intro witness selected
          obtain ⟨frames, trace⟩ :=
            CandidatePair.selectExactly_choiceTrace selected
          have witnessLength :=
            CandidatePair.ChoiceTrace.multiA_witness_length trace
          refine ⟨{
            netDiff := Int.ofNat keys.length - 1
            exec := Int.ofNat keys.length }, rfl, ?_⟩
          simp [baseWitnessResultOffset]
          omega
        · rw [show (satisfactionCandidates (.multi_a threshold keys) env).dsat =
            .usable (List.replicate keys.length falseElement) false by
              simp [multiACandidates, valid]]
          apply CandidateResult.supports_usable
          exact ⟨{
            netDiff := Int.ofNat keys.length - 1
            exec := Int.ofNat keys.length }, rfl, by
              simp [baseWitnessResultOffset]⟩
      · have empty : multiACandidates threshold keys env = {} := by
          simp [multiACandidates, valid]
        rw [satisfactionCandidates_multi_a, empty]
        exact ⟨.multi_a threshold keys positive atMost,
          CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩

private theorem supportsStackPathBoundsList_of_allWellFormed_hasTypeList
    {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType} {env : SatEnv}
    (typed : HasTypeList scriptCtx fragments types)
    (wellFormed : CoreFragment.allWellFormed scriptCtx fragments) :
    SupportsStackPathBoundsList scriptCtx
      (satisfactionCandidatesList fragments env) fragments types := by
  cases typed with
  | nil => exact .nil
  | @cons fragment ty fragments types head tail =>
      simp only [CoreFragment.allWellFormed] at wellFormed
      exact SupportsStackPathBoundsList.cons
        (supportsStackPathBounds_of_wellFormed_hasType (env := env) head wellFormed.1)
        (supportsStackPathBoundsList_of_allWellFormed_hasTypeList (env := env) tail wellFormed.2)
end

/-- A final generated satisfaction for a valid top-level fragment fits the
    fragment's computed maximum initial stack size. -/
theorem satisfyFinal_length_le_maxSatisfactionInitialStack
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {env : SatEnv}
    {witness : Witness}
    (valid : ValidMiniscript scriptCtx fragment)
    (selected : satisfyFinal fragment env = some witness) :
    ∃ limit,
      maxSatisfactionInitialStack fragment = some limit ∧
      Int.ofNat witness.length ≤ limit := by
  obtain ⟨mods, valid⟩ := valid
  have supported := supportsStackPathBounds_of_wellFormed_hasType
    (env := env) valid.hasType valid.wellFormed
  have ordinary := satisfyFinal_some_satisfy selected
  have fit := supported.sat witness (by
    simpa [satisfy] using ordinary)
  unfold StackTraceSet.BoundsWitness
    StackTraceSet.BoundsWitnessOffset at fit
  obtain ⟨trace, traceEq, bound⟩ := fit
  refine ⟨trace.netDiff + 1, ?_, ?_⟩
  · simp [maxSatisfactionInitialStack, traceEq]
  · simpa [baseWitnessResultOffset] using bound

end LeanMiniscript.Properties

namespace LeanMiniscript.Miniscript.SaneFragment

open LeanMiniscript.Properties

/-- A sane fragment inherits the generated final-witness stack bound from its
    top-level validity evidence. -/
theorem satisfyFinal_length_le_maxSatisfactionInitialStack
    {scriptCtx : ScriptContext} (sane : SaneFragment scriptCtx)
    {env : SatEnv} {witness : Witness}
    (selected : satisfyFinal sane.checked.fragment env = some witness) :
    ∃ limit,
      maxSatisfactionInitialStack sane.checked.fragment = some limit ∧
      Int.ofNat witness.length ≤ limit :=
  LeanMiniscript.Properties.satisfyFinal_length_le_maxSatisfactionInitialStack
    sane.validMiniscript selected

end LeanMiniscript.Miniscript.SaneFragment
