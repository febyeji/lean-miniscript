import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: execution contracts

The `GeneratedExecution` and `GeneratedContract` relations, candidate-pair
support predicates, generated child lists and choice frames, and the threshold
accumulator bridges.
-/

/-!
# Typed execution of generated witnesses

This module connects candidate provenance to the arbitrary-stack execution
frames in `SatisfactionProofs`. The proof-only carrier keeps the fragment's
typing derivation together with the exact execution contract selected by its
base type. In particular, a K execution separates the K fragment's own
arguments from the pending signature consumed by wrapper `c`.

The stable execution layer covers `0`, `1`, both key leaves, both timelocks,
all four hash leaves, and the `c` lift. The compositional refinement below adds
the input-shape and numeric-result invariants used by the remaining linear and
guarded wrapper proofs.
-/

/-- Exact execution contract selected by the fragment's base type. K
    fragments retain the pending signature below their own runtime arguments;
    this is the precise frame consumed by a following `OP_CHECKSIG`. -/
inductive GeneratedExecution (fragment : CoreFragment) (witness : Witness)
    (expected : Bool) (flags : ScriptFlags) (txCtx : TxContext) :
    BaseType → Prop where
  | b (executed : BExecutionOutcome fragment witness.toInitialStack expected
      flags txCtx) : GeneratedExecution fragment witness expected flags txCtx .B
  | v (expectedTrue : expected = true)
      (executed : VExecution fragment witness.toInitialStack flags txCtx) :
      GeneratedExecution fragment witness expected flags txCtx .V
  | k (ownArgs : Stack) (key signature : StackElement)
      (stackShape : witness.toInitialStack = ownArgs ++ [signature])
      (executed : KExecution fragment ownArgs key flags txCtx)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
        signature key = .ok expected) :
      GeneratedExecution fragment witness expected flags txCtx .K
  | w (order : WStackOrder)
      (executed : WExecutionOutcome fragment witness.toInitialStack expected
        order flags txCtx) :
      GeneratedExecution fragment witness expected flags txCtx .W

/-- Witness-side invariants contributed by correctness modifiers. The `n`
    obligation applies only to satisfying executions, matching its role as a
    nonzero-input precondition rather than a dissatisfaction requirement. -/
structure GeneratedInput (witness : Witness) (expected : Bool)
    (mods : CorrectnessModifiers) : Prop where
  bounded : witness.ItemsBounded
  zeroArgs : mods.z = true → witness.toInitialStack = []
  oneArg : mods.o = true → ∃ argument, witness.toInitialStack = [argument]
  nonzeroTop : mods.n = true → expected = true →
    ∃ top rest, witness.toInitialStack = top :: rest ∧ top.size ≠ 0

namespace GeneratedInput

/-- Transport input obligations to a modifier set whose asserted flags imply
    the corresponding source flags. -/
theorem mono {witness : Witness} {expected : Bool}
    {source target : CorrectnessModifiers}
    (input : GeneratedInput witness expected source)
    (zero : target.z = true → source.z = true)
    (one : target.o = true → source.o = true)
    (nonzero : target.n = true → source.n = true) :
    GeneratedInput witness expected target :=
  ⟨input.bounded,
    fun enabled => input.zeroArgs (zero enabled),
    fun enabled => input.oneArg (one enabled),
    fun enabled truth => input.nonzeroTop (nonzero enabled) truth⟩

/-- Compose the input invariants of two sequential child witnesses. The
    logical premises mirror the `z`, `o`, and `n` formulas used by connective
    typing, while keeping this helper independent of a particular constructor. -/
theorem combine {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods targetMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness firstExpected firstMods)
    (second : GeneratedInput secondWitness secondExpected secondMods)
    (zero : targetMods.z = true →
      firstMods.z = true ∧ secondMods.z = true)
    (one : targetMods.o = true →
      (firstMods.z = true ∧ secondMods.o = true) ∨
      (firstMods.o = true ∧ secondMods.z = true))
    (nonzero : targetMods.n = true →
      (firstMods.n = true ∧ (expected = true → firstExpected = true)) ∨
      (firstMods.z = true ∧ secondMods.n = true ∧
        (expected = true → secondExpected = true))) :
    GeneratedInput (Witness.combine firstWitness secondWitness)
      expected targetMods := by
  refine ⟨first.bounded.combine second.bounded, ?_, ?_, ?_⟩
  · intro enabled
    obtain ⟨firstZero, secondZero⟩ := zero enabled
    simp [first.zeroArgs firstZero, second.zeroArgs secondZero]
  · intro enabled
    rcases one enabled with left | right
    · obtain ⟨firstZero, secondOne⟩ := left
      obtain ⟨argument, secondShape⟩ := second.oneArg secondOne
      exact ⟨argument, by
        simp [first.zeroArgs firstZero, secondShape]⟩
    · obtain ⟨firstOne, secondZero⟩ := right
      obtain ⟨argument, firstShape⟩ := first.oneArg firstOne
      exact ⟨argument, by
        simp [firstShape, second.zeroArgs secondZero]⟩
  · intro enabled truth
    rcases nonzero enabled with firstNonzero | secondNonzero
    · obtain ⟨firstN, firstTruth⟩ := firstNonzero
      obtain ⟨top, rest, shape, nonempty⟩ :=
        first.nonzeroTop firstN (firstTruth truth)
      exact ⟨top, rest ++ secondWitness.toInitialStack, by
        simp [shape], nonempty⟩
    · obtain ⟨firstZero, secondN, secondTruth⟩ := secondNonzero
      obtain ⟨top, rest, shape, nonempty⟩ :=
        second.nonzeroTop secondN (secondTruth truth)
      exact ⟨top, rest, by
        simp [first.zeroArgs firstZero, shape], nonempty⟩

/-- Prefixing a branch selector preserves bounds and can satisfy an outer
    one-argument condition exactly when the selected child is zero-argument. -/
theorem withSelector {witness : Witness} {childExpected expected : Bool}
    {source target : CorrectnessModifiers} {selector : StackElement}
    (input : GeneratedInput witness childExpected source)
    (selectorBounded : selector.size ≤ maxScriptElementSize)
    (zero : target.z = true → False)
    (one : target.o = true → source.z = true)
    (nonzero : target.n = true → expected = true → selector.size ≠ 0) :
    GeneratedInput (witness.withSelector selector) expected target := by
  refine ⟨input.bounded.withSelector selectorBounded, ?_, ?_, ?_⟩
  · intro enabled
    exact (zero enabled).elim
  · intro enabled
    exact ⟨selector, by simp [input.zeroArgs (one enabled)]⟩
  · intro enabled truth
    exact ⟨selector, witness.toInitialStack, by simp,
      nonzero enabled truth⟩

end GeneratedInput

/-- Exact numeric and canonical-form facts for a B-like result. Keeping the
    decoded integer explicit makes `n` and later arithmetic connectors compose
    without recovering a number from truthiness. -/
structure BooleanResultFacts (result : StackElement) (value : Int)
    (expected : Bool) (mods : CorrectnessModifiers) (flags : ScriptFlags) : Prop where
  decoded : decodeScriptNum result flags.minimalData
    maxArithmeticScriptNumBytes = .ok value
  nonzero : (value != 0) = expected
  truth : castToBool result = expected
  falseCanonical : expected = false → result = falseElement
  unitCanonical : mods.u = true → expected = true → result = trueElement

namespace BooleanResultFacts

/-- Canonical boolean elements satisfy every result invariant, independently
    of the surrounding fragment's modifiers. -/
theorem canonical (expected : Bool) (mods : CorrectnessModifiers)
    (flags : ScriptFlags) :
    BooleanResultFacts (boolToElement expected)
      (if expected then 1 else 0) expected mods flags := by
  cases expected <;> cases minimal : flags.minimalData <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [minimal, boolToElement, decodeScriptNum, falseElement,
    trueElement, ByteArray.size, ByteArray.ext_iff,
    maxArithmeticScriptNumBytes, scriptNumIsMinimal, scriptNumIsNegative,
    clearScriptNumSignBit, decodeUnsignedLEAux, castToBool]

/-- Transport exact result facts when only the unit implication changes. -/
theorem monoUnit {result : StackElement} {value : Int} {expected : Bool}
    {source target : CorrectnessModifiers} {flags : ScriptFlags}
    (facts : BooleanResultFacts result value expected source flags)
    (unit : target.u = true → source.u = true) :
    BooleanResultFacts result value expected target flags :=
  ⟨facts.decoded, facts.nonzero, facts.truth, facts.falseCanonical,
    fun enabled truth => facts.unitCanonical (unit enabled) truth⟩

/-- Retype exact result facts across a modifier implication. -/
theorem retype {result : StackElement} {value : Int} {expected : Bool}
    {source target : CorrectnessModifiers} {flags : ScriptFlags}
    (facts : BooleanResultFacts result value expected source flags)
    (unit : target.u = true → source.u = true) :
    BooleanResultFacts result value expected target flags :=
  facts.monoUnit unit

/-- A unit B result is the canonical boolean encoding of its truth value. -/
theorem eq_boolToElement_of_unit
    {result : StackElement} {value : Int} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags}
    (facts : BooleanResultFacts result value expected mods flags)
    (unit : mods.u = true) : result = boolToElement expected := by
  cases expected with
  | false => simpa [boolToElement] using facts.falseCanonical rfl
  | true => simpa [boolToElement] using facts.unitCanonical unit rfl

/-- Unit result facts discharge MINIMALIF for child-produced selectors. -/
theorem minimalIfSatisfied
    {result : StackElement} {value : Int} {expected : Bool}
    {mods : CorrectnessModifiers} {flags : ScriptFlags}
    {version : SignatureVersion}
    (facts : BooleanResultFacts result value expected mods flags)
    (unit : mods.u = true) :
    LeanMiniscript.Script.minimalIfSatisfied flags version result := by
  rw [facts.eq_boolToElement_of_unit unit]
  apply LeanMiniscript.Script.minimalIfSatisfied_of_arg
  cases expected
  · exact falseElement_minimalIfArg
  · exact trueElement_minimalIfArg

/-- Exact child result decodes assemble the operand-order premise used by a
    binary opcode after either W stack layout. -/
theorem binaryDecoded
    {firstResult secondResult : StackElement} {firstValue secondValue : Int}
    {firstExpected secondExpected : Bool}
    {firstMods secondMods : CorrectnessModifiers} {flags : ScriptFlags}
    (first : BooleanResultFacts firstResult firstValue firstExpected
      firstMods flags)
    (second : BooleanResultFacts secondResult secondValue secondExpected
      secondMods flags) (order : WStackOrder) :
    order.BinaryDecoded flags firstResult secondResult firstValue secondValue := by
  cases order <;>
    simp [WStackOrder.BinaryDecoded, decodeBinaryScriptNums,
      first.decoded, second.decoded]
  all_goals rfl

end BooleanResultFacts

/-- Compositional generated-witness contract. This strengthens the stable
    `GeneratedExecution` API with input-shape, element-size, and exact numeric
    result facts while indexing the contract by the complete Miniscript type. -/
inductive GeneratedContract (fragment : CoreFragment) (witness : Witness)
    (expected : Bool) (flags : ScriptFlags) (txCtx : TxContext) :
    MiniType → Prop where
  | b {mods : CorrectnessModifiers} {result : StackElement} {value : Int}
      (input : GeneratedInput witness expected mods)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : BExecution fragment witness.toInitialStack result flags txCtx) :
      GeneratedContract fragment witness expected flags txCtx ⟨.B, mods⟩
  | v {mods : CorrectnessModifiers} (input : GeneratedInput witness expected mods)
      (expectedTrue : expected = true)
      (executed : VExecution fragment witness.toInitialStack flags txCtx) :
      GeneratedContract fragment witness expected flags txCtx ⟨.V, mods⟩
  | k {mods : CorrectnessModifiers} (input : GeneratedInput witness expected mods)
      (ownArgs : Stack) (key signature : StackElement)
      (stackShape : witness.toInitialStack = ownArgs ++ [signature])
      (executed : KExecution fragment ownArgs key flags txCtx)
      (checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
        signature key = .ok expected) :
      GeneratedContract fragment witness expected flags txCtx ⟨.K, mods⟩
  | w {mods : CorrectnessModifiers} {result : StackElement} {value : Int}
      (input : GeneratedInput witness expected mods)
      (order : WStackOrder)
      (facts : BooleanResultFacts result value expected mods flags)
      (executed : WExecution fragment witness.toInitialStack result order
        flags txCtx) :
      GeneratedContract fragment witness expected flags txCtx ⟨.W, mods⟩

namespace GeneratedContract

/-- Forget compositional facts and recover the stable execution carrier. -/
theorem execution {fragment : CoreFragment} {witness : Witness}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext} {ty : MiniType}
    (contract : GeneratedContract fragment witness expected flags txCtx ty) :
    GeneratedExecution fragment witness expected flags txCtx ty.base := by
  cases contract with
  | b input facts executed => exact .b ⟨_, executed, facts.truth⟩
  | v input expectedTrue executed => exact .v expectedTrue executed
  | k input ownArgs key signature stackShape executed checked =>
      exact .k ownArgs key signature stackShape executed checked
  | w input order facts executed =>
      exact .w order ⟨_, executed, facts.truth⟩

/-- Every strong contract exposes its witness input invariants. -/
theorem input {fragment : CoreFragment} {witness : Witness}
    {expected : Bool} {flags : ScriptFlags} {txCtx : TxContext} {ty : MiniType}
    (contract : GeneratedContract fragment witness expected flags txCtx ty) :
    GeneratedInput witness expected ty.mods := by
  cases contract <;> assumption

end GeneratedContract

/-- A candidate pair carries one global typing derivation plus an execution
    invariant for every projected satisfaction and dissatisfaction. Keeping
    typing outside the projections also covers pairs with impossible sides. -/
structure CandidatePair.SupportsGenerated (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports fun witness =>
    GeneratedExecution fragment witness true flags txCtx ty.base
  dsat : pair.dsat.Supports fun witness =>
    GeneratedExecution fragment witness false flags txCtx ty.base

/-- Candidate-wide support for the compositional generated contract. -/
structure CandidatePair.SupportsGeneratedContract (pair : CandidatePair)
    (scriptCtx : ScriptContext) (fragment : CoreFragment) (ty : MiniType)
    (flags : ScriptFlags) (txCtx : TxContext) : Prop where
  typed : HasType scriptCtx fragment ty
  sat : pair.sat.Supports fun witness =>
    GeneratedContract fragment witness true flags txCtx ty
  dsat : pair.dsat.Supports fun witness =>
    GeneratedContract fragment witness false flags txCtx ty

namespace CandidatePair.SupportsGeneratedContract

/-- The strong layer remains a conservative extension of the existing public
    generated-execution support API. -/
theorem toSupportsGenerated
    {pair : CandidatePair} {scriptCtx : ScriptContext}
    {fragment : CoreFragment} {ty : MiniType}
    {flags : ScriptFlags} {txCtx : TxContext}
    (supported : pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx) :
    pair.SupportsGenerated scriptCtx fragment ty flags txCtx :=
  ⟨supported.typed,
    fun witness selected => (supported.sat witness selected).execution,
    fun witness selected => (supported.dsat witness selected).execution⟩

/-- Project a strong satisfaction contract through the public witness API. -/
theorem satisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : satisfy fragment env = some witness) :
    GeneratedContract fragment witness true flags env.txCtx ty :=
  supported.sat witness generated

/-- Project a strong dissatisfaction contract through the public witness API. -/
theorem dissatisfyContract
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates fragment env) scriptCtx fragment ty flags env.txCtx)
    (generated : dissatisfy fragment env = some witness) :
    GeneratedContract fragment witness false flags env.txCtx ty :=
  supported.dsat witness generated

end CandidatePair.SupportsGeneratedContract

namespace CandidatePair.SupportsGenerated

/-- Project the satisfaction execution contract through the public
    `satisfy` API. -/
theorem satisfyExecution
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : (satisfactionCandidates fragment env).SupportsGenerated
      scriptCtx fragment ty flags env.txCtx)
    (generated : satisfy fragment env = some witness) :
    GeneratedExecution fragment witness true flags env.txCtx ty.base :=
  supported.sat witness generated

/-- Project the dissatisfaction execution contract through the public
    `dissatisfy` API. -/
theorem dissatisfyExecution
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags} {witness : Witness}
    (supported : (satisfactionCandidates fragment env).SupportsGenerated
      scriptCtx fragment ty flags env.txCtx)
    (generated : dissatisfy fragment env = some witness) :
    GeneratedExecution fragment witness false flags env.txCtx ty.base :=
  supported.dsat witness generated

end CandidatePair.SupportsGenerated

/-! ## Generated child lists -/

/-- Strong generated support aligned with a source-order fragment/type list.
    The snoc presentation matches the exact-count choice trace without changing
    the executable list representation. -/
inductive SupportsGeneratedContractList (scriptCtx : ScriptContext)
    (flags : ScriptFlags) (txCtx : TxContext) :
    List CandidatePair → List CoreFragment → List MiniType → Prop where
  | nil : SupportsGeneratedContractList scriptCtx flags txCtx [] [] []
  | snoc {pairs : List CandidatePair} {fragments : List CoreFragment}
      {types : List MiniType} {pair : CandidatePair} {fragment : CoreFragment}
      {ty : MiniType}
      (prior : SupportsGeneratedContractList scriptCtx flags txCtx
        pairs fragments types)
      (child : pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx) :
      SupportsGeneratedContractList scriptCtx flags txCtx
        (pairs ++ [pair]) (fragments ++ [fragment]) (types ++ [ty])

namespace HasTypeList

/-- Pointwise typing is closed under appending one source child. -/
theorem snoc {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType} {fragment : CoreFragment} {ty : MiniType}
    (prior : HasTypeList scriptCtx fragments types)
    (child : HasType scriptCtx fragment ty) :
    HasTypeList scriptCtx (fragments ++ [fragment]) (types ++ [ty]) := by
  apply HasTypeList.recOn
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun fragments types _ =>
      HasTypeList scriptCtx (fragments ++ [fragment]) (types ++ [ty])) prior
  all_goals simp_all
  · exact .cons child .nil
  · intros
    apply HasTypeList.cons <;> assumption

end HasTypeList

namespace SupportsGeneratedContractList

private theorem nil_inv {scriptCtx : ScriptContext} {flags : ScriptFlags}
    {txCtx : TxContext} {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedContractList scriptCtx flags txCtx
      [] fragments types) : fragments = [] ∧ types = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at supported
  cases supported with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc pairs fragments types pair fragment ty prior child =>
      simp at pairsEq

private theorem snoc_inv {scriptCtx : ScriptContext} {flags : ScriptFlags}
    {txCtx : TxContext} {pairs : List CandidatePair} {pair : CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedContractList scriptCtx flags txCtx
      (pairs ++ [pair]) fragments types) :
    ∃ priorFragments priorTypes fragment ty,
      fragments = priorFragments ++ [fragment] ∧
      types = priorTypes ++ [ty] ∧
      SupportsGeneratedContractList scriptCtx flags txCtx
        pairs priorFragments priorTypes ∧
      pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx := by
  generalize pairsEq : pairs ++ [pair] = allPairs at supported
  cases supported with
  | nil => simp at pairsEq
  | @snoc otherPairs otherFragments otherTypes otherPair fragment ty prior child =>
      obtain ⟨rfl, singletonEq⟩ := List.append_inj' pairsEq rfl
      cases singletonEq
      exact ⟨otherFragments, otherTypes, fragment, ty, rfl, rfl, prior, child⟩

/-- List support retains the pointwise typing evidence needed by the threshold
    typing constructor. -/
theorem typed {scriptCtx : ScriptContext} {flags : ScriptFlags}
    {txCtx : TxContext} {pairs : List CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    (supported : SupportsGeneratedContractList scriptCtx flags txCtx
      pairs fragments types) :
    HasTypeList scriptCtx fragments types := by
  induction supported with
  | nil => exact .nil
  | snoc prior child ih => exact ih.snoc child.typed

/-- Prepend one strongly supported source child. -/
theorem cons {scriptCtx : ScriptContext} {flags : ScriptFlags}
    {txCtx : TxContext} {pairs : List CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    {pair : CandidatePair} {fragment : CoreFragment} {ty : MiniType}
    (child : pair.SupportsGeneratedContract scriptCtx fragment ty flags txCtx)
    (rest : SupportsGeneratedContractList scriptCtx flags txCtx
      pairs fragments types) :
    SupportsGeneratedContractList scriptCtx flags txCtx
      (pair :: pairs) (fragment :: fragments) (ty :: types) := by
  induction rest with
  | nil => exact .snoc .nil child
  | snoc prior last ih => exact .snoc ih last

end SupportsGeneratedContractList

/-- Executable contracts selected by a source-order Boolean choice row. This
    relation is head-recursive so threshold execution can consume the first B
    child followed by its W tail directly. -/
inductive GeneratedChoiceFrames (flags : ScriptFlags) (txCtx : TxContext) :
    List CoreFragment → List MiniType → List Bool → List Witness → Prop where
  | nil : GeneratedChoiceFrames flags txCtx [] [] [] []
  | cons {fragment : CoreFragment} {ty : MiniType} {truth : Bool}
      {frame : Witness} {fragments : List CoreFragment} {types : List MiniType}
      {truths : List Bool} {frames : List Witness}
      (head : GeneratedContract fragment frame truth flags txCtx ty)
      (tail : GeneratedChoiceFrames flags txCtx fragments types truths frames) :
      GeneratedChoiceFrames flags txCtx (fragment :: fragments) (ty :: types)
        (truth :: truths) (frame :: frames)

namespace GeneratedChoiceFrames

/-- Append one selected child contract while preserving source order. -/
theorem snoc {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    {fragment : CoreFragment} {ty : MiniType} {truth : Bool} {frame : Witness}
    (prior : GeneratedChoiceFrames flags txCtx fragments types truths frames)
    (child : GeneratedContract fragment frame truth flags txCtx ty) :
    GeneratedChoiceFrames flags txCtx (fragments ++ [fragment]) (types ++ [ty])
      (truths ++ [truth]) (frames ++ [frame]) := by
  induction prior with
  | nil => exact .cons child .nil
  | cons head tail ih => exact .cons head ih

/-- Every selected child frame inherits the per-item witness bound from its
    strong generated contract. -/
theorem framesBounded {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedChoiceFrames flags txCtx fragments types truths frames) :
    ∀ frame ∈ frames, frame.ItemsBounded := by
  induction generated with
  | nil => simp
  | cons head tail ih =>
      intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact head.input.bounded
      · exact ih frame member

/-- If every child is zero-argument, the concatenated runtime frame is empty. -/
theorem allZ {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedChoiceFrames flags txCtx fragments types truths frames)
    (zero : CorrectnessModifiers.allZ (MiniType.modifiers types) = true) :
    (frames.map Witness.toInitialStack).flatten = [] := by
  induction generated with
  | nil => rfl
  | @cons fragment ty truth frame fragments types truths frames head tail ih =>
      cases ty with
      | mk base mods =>
          simp only [MiniType.modifiers, CorrectnessModifiers.allZ,
            Bool.and_eq_true] at zero
          rw [List.map_cons, List.flatten_cons, head.input.zeroArgs zero.1,
            ih zero.2]
          rfl

/-- If exactly one child is one-argument and every other child is zero-argument,
    the concatenated runtime frame is a singleton. -/
theorem oneOWithRestZ {flags : ScriptFlags} {txCtx : TxContext}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedChoiceFrames flags txCtx fragments types truths frames)
    (one : CorrectnessModifiers.oneOWithRestZ
      (MiniType.modifiers types) = true) :
    ∃ argument, (frames.map Witness.toInitialStack).flatten = [argument] := by
  induction generated with
  | nil => simp [MiniType.modifiers, CorrectnessModifiers.oneOWithRestZ] at one
  | @cons fragment ty truth frame fragments types truths frames head tail ih =>
      cases ty with
      | mk base mods =>
          simp only [MiniType.modifiers, CorrectnessModifiers.oneOWithRestZ,
            Bool.or_eq_true, Bool.and_eq_true] at one
          rcases one with headOne | tailOne
          · obtain ⟨argument, shape⟩ := head.input.oneArg headOne.1
            refine ⟨argument, ?_⟩
            rw [List.map_cons, List.flatten_cons, shape, allZ tail headOne.2]
            rfl
          · obtain ⟨argument, shape⟩ := ih tailOne.2
            refine ⟨argument, ?_⟩
            rw [List.map_cons, List.flatten_cons,
              head.input.zeroArgs tailOne.1, shape]
            rfl

end GeneratedChoiceFrames

/-- Source-choice provenance and aligned strong child support recover the exact
    generated contract selected for every child frame. -/
theorem CandidatePair.ChoiceFrames.generated
    {scriptCtx : ScriptContext} {flags : ScriptFlags} {txCtx : TxContext}
    {pairs : List CandidatePair} {fragments : List CoreFragment}
    {types : List MiniType} {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames pairs truths frames)
    (supported : SupportsGeneratedContractList scriptCtx flags txCtx
      pairs fragments types) :
    GeneratedChoiceFrames flags txCtx fragments types truths frames := by
  induction choices generalizing fragments types with
  | nil =>
      obtain ⟨rfl, rfl⟩ := SupportsGeneratedContractList.nil_inv supported
      exact .nil
  | snocSat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedContractList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.sat _ selected)
  | snocDsat prior selected ih =>
      obtain ⟨priorFragments, priorTypes, fragment, ty, rfl, rfl,
        priorSupported, childSupported⟩ :=
        SupportsGeneratedContractList.snoc_inv supported
      exact (ih priorSupported).snoc (childSupported.dsat _ selected)

/-! ## Threshold accumulator bridges -/

/-- A valid positive threshold literal has bytes distinct from canonical zero. -/
theorem candidateThresholdValid_scriptNat_ne_zero
    {threshold arity : Nat} (valid : candidateThresholdValid threshold arity) :
    scriptNat threshold ≠ scriptNat 0 := by
  intro encodedEq
  have thresholdDecoded := valid.2.2.decode false
  have zeroDecoded := decodeScriptNum_scriptNat_of_lt
    (n := 0) (by decide) false
  rw [encodedEq, zeroDecoded] at thresholdDecoded
  simp only [Except.ok.injEq] at thresholdDecoded
  apply valid.1
  exact Int.ofNat.inj thresholdDecoded.symm

/-- A canonical accumulator and Boolean child satisfy the exact numeric decoder
    premise for either W result order. -/
theorem WStackOrder.binaryDecoded_scriptNat_boolToElement
    {count : Nat} (safe : ArithmeticScriptNatSafe count)
    (truth : Bool) (flags : ScriptFlags) (order : WStackOrder) :
    order.BinaryDecoded flags (scriptNat count) (boolToElement truth)
      (Int.ofNat count) (Int.ofNat truth.toNat) := by
  have accumulatorDecoded := safe.decode flags.minimalData
  have childDecoded :=
    (BooleanResultFacts.canonical truth ({} : CorrectnessModifiers) flags).decoded
  cases truth <;> cases order <;>
    simp [WStackOrder.BinaryDecoded, decodeBinaryScriptNums,
      accumulatorDecoded, childDecoded]
  all_goals rfl

/-- Arithmetic Script-number safety is downward closed. -/
theorem arithmeticScriptNatSafe_of_le
    {small total : Nat} (safe : ArithmeticScriptNatSafe total)
    (bound : small ≤ total) : ArithmeticScriptNatSafe small := by
  apply ArithmeticScriptNatSafe.of_lt
  exact Nat.lt_of_le_of_lt bound safe.1

/-- The current accumulator is bounded by its final count. -/
theorem threshold_accumulator_safe
    {count total : Nat} {truths : List Bool}
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    ArithmeticScriptNatSafe count := by
  apply arithmeticScriptNatSafe_of_le safe
  omega

/-- Consuming one Boolean preserves the exact remaining-sum invariant. -/
theorem threshold_accumulator_step
    {count total : Nat} {truth : Bool} {truths : List Bool}
    (totalEq : count + ((truth :: truths).map Bool.toNat).sum = total) :
    (count + truth.toNat) + (truths.map Bool.toNat).sum = total := by
  simp only [List.map_cons, List.sum_cons] at totalEq
  omega

/-- Execute source-order W child frames as a threshold tail. Final-count safety
    is enough because every intermediate accumulator is bounded by that total. -/
theorem GeneratedChoiceFrames.thresholdTail
    {flags : ScriptFlags} {txCtx : TxContext} {count total : Nat}
    {fragments : List CoreFragment} {types : List MiniType}
    {truths : List Bool} {frames : List Witness}
    (generated : GeneratedChoiceFrames flags txCtx fragments types truths frames)
    (restTyped : thresholdRestTypes types)
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    ThresholdTailExecution flags txCtx count fragments
      (frames.map Witness.toInitialStack) total := by
  induction generated generalizing count total with
  | nil =>
      simp at totalEq
      subst total
      exact .nil count
  | @cons fragment ty truth frame fragments types truths frames head tail ih =>
      cases ty with
      | mk base mods =>
          simp only [thresholdRestTypes] at restTyped
          obtain ⟨baseEq, childD, childUnit, restTyped⟩ := restTyped
          subst base
          cases head with
          | w input order facts executed =>
              have childExec : WExecution fragment frame.toInitialStack
                  (boolToElement truth) order flags txCtx := by
                simpa [facts.eq_boolToElement_of_unit childUnit] using executed
              exact .cons childExec
                (order.binaryDecoded_scriptNat_boolToElement
                  (threshold_accumulator_safe safe totalEq) truth flags)
                (ih restTyped safe (threshold_accumulator_step totalEq))

/-- Execute a nonempty generated threshold frame list. The first child is Bdu,
    every remaining child is Wdu, and `total` is the exact number of satisfying
    source choices. -/
theorem GeneratedChoiceFrames.thresholdExecution
    {flags : ScriptFlags} {txCtx : TxContext} {threshold total : Nat}
    {first : CoreFragment} {fragments : List CoreFragment}
    {firstMods : CorrectnessModifiers} {restTypes : List MiniType}
    {truths : List Bool} {frames : List Witness} {expected : Bool}
    (generated : GeneratedChoiceFrames flags txCtx (first :: fragments)
      (⟨.B, firstMods⟩ :: restTypes) truths frames)
    (firstUnit : firstMods.u = true)
    (restTyped : thresholdRestTypes restTypes)
    (safe : ArithmeticScriptNatSafe total)
    (sumEq : (truths.map Bool.toNat).sum = total)
    (comparison : decide (scriptNat threshold = scriptNat total) = expected) :
    BExecution (.thresh threshold (first :: fragments))
      (frames.map Witness.toInitialStack).flatten (boolToElement expected)
      flags txCtx := by
  cases generated with
  | @cons _ _ firstTruth firstFrame _ _ tailTruths tailFrames
      firstContract tail =>
      cases firstContract with
      | b firstInput firstFacts firstExec =>
          have normalizedFirst : BExecution first firstFrame.toInitialStack
              (boolToElement firstTruth) flags txCtx := by
            simpa [firstFacts.eq_boolToElement_of_unit firstUnit] using firstExec
          have totalEq : firstTruth.toNat +
              (tailTruths.map Bool.toNat).sum = total := by
            simpa using sumEq
          have tailExec := tail.thresholdTail restTyped safe totalEq
          simpa [comparison] using
            (normalizedFirst.thresh (threshold := threshold) tailExec)

/-- Rebuild the threshold's aggregate input modifiers from the selected child
    frames and the exact combined witness trace. -/
theorem GeneratedChoiceFrames.thresholdInput
    {flags : ScriptFlags} {txCtx : TxContext} {pairs : List CandidatePair}
    {fragments : List CoreFragment} {types : List MiniType}
    {count : Nat} {truths : List Bool} {frames : List Witness}
    {witness : Witness} {expected : Bool}
    (generated : GeneratedChoiceFrames flags txCtx fragments types truths frames)
    (trace : CandidatePair.ChoiceTrace pairs count frames witness) :
    GeneratedInput witness expected {
      z := CorrectnessModifiers.allZ (MiniType.modifiers types)
      o := CorrectnessModifiers.oneOWithRestZ (MiniType.modifiers types)
      d := true
      u := true } := by
  refine ⟨trace.itemsBounded generated.framesBounded, ?_, ?_, ?_⟩
  · intro enabled
    exact trace.toInitialStack.trans (generated.allZ enabled)
  · intro enabled
    obtain ⟨argument, shape⟩ := generated.oneOWithRestZ enabled
    exact ⟨argument, trace.toInitialStack.trans shape⟩
  · simp

end LeanMiniscript.Miniscript
