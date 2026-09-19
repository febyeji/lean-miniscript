import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Numeric and encoding bridges -/

/-- The two codec facts needed to execute a well-formed timelock literal. -/
structure TimelockExecutionFacts (n : Nat) (flags : ScriptFlags) : Prop where
  decoded : decodeScriptNum (scriptNat n) flags.minimalData
    maxTimelockScriptNumBytes = .ok (Int.ofNat n)
  positive : castToBool (scriptNat n) = true

namespace TimelockExecutionFacts

/-- BIP 379's positive, below-bit-31 timelock bound supplies both the extended
    five-byte decoder result and the truthiness of the canonical operand. -/
theorem of_validTimelockArg {n : Nat} {flags : ScriptFlags}
    (valid : validTimelockArg n) : TimelockExecutionFacts n flags := by
  rcases valid with ⟨positive, bound⟩
  constructor
  · apply decodeScriptNum_mono (small := maxArithmeticScriptNumBytes)
    · native_decide
    · apply decodeScriptNum_scriptNat_of_lt
      simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
        maxArithmeticScriptNatExclusive] using bound
  · apply castToBool_scriptNat_of_pos_of_lt
    · omega
    · simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
        maxArithmeticScriptNatExclusive] using bound

end TimelockExecutionFacts

/-- A context-valid key accepts the canonical empty signature under the flags
    and signature version required by that Miniscript context. -/
theorem checkSigEncodingFor_empty_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {flags : ScriptFlags}
    {txCtx : TxContext} (wellFormed : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx txCtx)
    (modeled : ModeledContextFlags scriptCtx flags) :
    checkSigEncodingFor flags txCtx.sigVersion falseElement key.bytes =
      .ok () := by
  cases scriptCtx with
  | p2wsh =>
      rcases wellFormed with ⟨keySize, keyPrefix⟩
      rcases modeled with ⟨_, _, _, _, strict⟩
      simp only [ModeledContextVersion] at version
      have h0 : 0 < key.bytes.size := by omega
      have dataH0 : 0 < key.bytes.data.size := by
        simpa [ByteArray.size_data] using h0
      have indexEq : key.bytes[0]! = key.bytes.get! 0 := by
        rw [getElem!_pos key.bytes 0 h0]
        change key.bytes.data[0] = key.bytes.data[0]!
        rw [getElem!_pos key.bytes.data 0 dataH0]
      have compressed : isCompressedPubKey key.bytes = true := by
        unfold isCompressedPubKey
        rw [indexEq]
        simp [keySize, keyPrefix]
      have ordinary : isCompressedOrUncompressedPubKey key.bytes = true := by
        unfold isCompressedOrUncompressedPubKey
        rw [indexEq]
        simp [keySize, keyPrefix]
      simp [checkSigEncodingFor, version, checkECDSAEncoding,
        checkPubKeyEncoding, strict, compressed, ordinary]
      rfl
  | tapscript =>
      simp only [validResolvedPubKey] at wellFormed
      simp only [ModeledContextVersion] at version
      have keySize : key.bytes.size = 32 := wellFormed
      have falseEq : falseElement = ByteArray.empty := by
        simp [falseElement, ByteArray.ext_iff]
      simp [checkSigEncodingFor, version, keySize, falseEq]
      rfl

private theorem isValidSignatureEncoding_size_le
    {signature : StackElement}
    (valid : isValidSignatureEncoding signature = true) :
    signature.size ≤ 73 := by
  by_cases bound : signature.size ≤ 73
  · exact bound
  · have oversized : signature.size > 73 := by omega
    simp [isValidSignatureEncoding, oversized] at valid

private theorem checkSignatureEncoding_size_le_of_strict
    {flags : ScriptFlags} {signature : StackElement}
    (strict : flags.strictEncoding = true)
    (checked : checkSignatureEncoding flags signature = .ok ()) :
    signature.size ≤ 73 := by
  by_cases empty : signature.size = 0
  · omega
  have valid : isValidSignatureEncoding signature = true := by
    cases validEq : isValidSignatureEncoding signature with
    | false => simp [checkSignatureEncoding, empty, strict, validEq] at checked
    | true => rfl
  exact isValidSignatureEncoding_size_le valid

private theorem checkSchnorrSignatureEncoding_size_le
    {signature : StackElement}
    (checked : checkSchnorrSignatureEncoding signature = .ok ()) :
    signature.size ≤ 65 := by
  by_cases bound : signature.size ≤ 65
  · exact bound
  · have not64 : signature.size ≠ 64 := by omega
    have not65 : signature.size ≠ 65 := by omega
    simp [checkSchnorrSignatureEncoding, not64, not65] at checked

/-- A context-valid key is always a legal witness element. -/
theorem validResolvedPubKey_size_le
    {scriptCtx : ScriptContext} {key : PubKey}
    (valid : validResolvedPubKey scriptCtx key) :
    key.bytes.size ≤ maxScriptElementSize := by
  cases scriptCtx <;>
    simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size,
      maxScriptElementSize]

theorem validResolvedPubKey_size_ne_zero
    {scriptCtx : ScriptContext} {key : PubKey}
    (valid : validResolvedPubKey scriptCtx key) :
    key.bytes.size ≠ 0 := by
  cases scriptCtx <;>
    simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size]

/-- A selected signature which passes the modeled encoding checks is a legal
    witness element. Tapscript additionally uses the context-valid 32-byte key
    shape to select Schnorr encoding. -/
theorem selectedSignature_size_le
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} {signature : StackElement}
    (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (encodings : env.EncodingSound flags)
    (selected : env.signatureFor key = some signature) :
    signature.size ≤ maxScriptElementSize := by
  have encoded := encodings key signature selected
  cases scriptCtx with
  | p2wsh =>
      rcases modeled with ⟨_, _, _, _, strict⟩
      simp only [ModeledContextVersion] at version
      rw [version] at encoded
      have checked : checkSignatureEncoding flags signature = .ok () := by
        cases checkedSig : checkSignatureEncoding flags signature with
        | error error =>
            simp only [checkSigEncodingFor, checkECDSAEncoding] at encoded
            rw [checkedSig] at encoded
            contradiction
        | ok value =>
            cases value
            rfl
      have := checkSignatureEncoding_size_le_of_strict strict checked
      change signature.size ≤ 520
      omega
  | tapscript =>
      simp only [validResolvedPubKey, PubKey.size] at valid
      simp only [ModeledContextVersion] at version
      rw [version] at encoded
      by_cases empty : signature.size = 0
      · change signature.size ≤ 520
        omega
      have checked : checkSchnorrSignatureEncoding signature = .ok () := by
        simpa [checkSigEncodingFor, valid, empty] using encoded
      have := checkSchnorrSignatureEncoding_size_le checked
      change signature.size ≤ 520
      omega

theorem selectedPreimage_size_le
    {env : SatEnv} (sound : env.Sound) {lock : HashLock}
    {preimage : StackElement}
    (selected : env.preimageFor lock = some preimage) :
    preimage.size ≤ maxScriptElementSize := by
  have exactSize := (sound.preimageMatches selected).1
  change preimage.size ≤ 520
  omega

theorem selectedNonPreimage_size_le
    {env : SatEnv} (sound : env.Sound) (lock : HashLock) :
    (env.nonPreimageFor lock).size ≤ maxScriptElementSize := by
  have exactSize := (sound.nonPreimageMismatches lock).1
  change (env.nonPreimageFor lock).size ≤ 520
  omega

theorem falseElement_size_le :
    falseElement.size ≤ maxScriptElementSize := by native_decide

theorem trueElement_size_le :
    trueElement.size ≤ maxScriptElementSize := by native_decide

theorem selectedSignature_size_ne_zero
    {key : PubKey} {env : SatEnv} {signature : StackElement}
    (sound : env.Sound) (selected : env.signatureFor key = some signature) :
    signature.size ≠ 0 := by
  intro empty
  have signatureEmpty : signature = ByteArray.empty :=
    ByteArray.size_eq_zero_iff.mp empty
  have falseEmpty : falseElement = ByteArray.empty := by
    simp [falseElement, ByteArray.ext_iff]
  have signatureFalse : signature = falseElement :=
    signatureEmpty.trans falseEmpty.symm
  have verified := sound.signatureValid selected
  rw [signatureFalse, sound.emptySignatureInvalid key] at verified
  contradiction

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
    (facts : BooleanResultFacts result value expected mods flags)
    (unit : mods.u = true) :
    LeanMiniscript.Script.minimalIfSatisfied flags result := by
  rw [facts.eq_boolToElement_of_unit unit]
  cases expected
  · exact Or.inr falseElement_minimalIfArg
  · exact Or.inr trueElement_minimalIfArg

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
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
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
    (n := 0) (by native_decide) false
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

/-! ## Atomic candidate rows -/

/-- The `0` row has only its canonical empty dissatisfaction. -/
theorem generated_zero (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .zero env).SupportsGenerated scriptCtx .zero
      ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
  apply CandidateResult.supports_usable
  exact .b ⟨falseElement, by simpa using zero_execution flags env.txCtx,
    by native_decide⟩

/-- The `1` row has only its canonical empty satisfaction. -/
theorem generated_one (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGenerated scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
  apply CandidateResult.supports_usable
  exact .b ⟨trueElement, by simpa using one_execution flags env.txCtx,
    by native_decide⟩

/-- Strong generated contract for `0`. -/
theorem generatedContract_zero (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .zero env).SupportsGeneratedContract scriptCtx .zero
      ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.zero, CandidateResult.supports_impossible _, ?_⟩
  apply CandidateResult.supports_usable
  apply GeneratedContract.b
  · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · exact BooleanResultFacts.canonical false _ flags
  · simpa [boolToElement] using zero_execution flags env.txCtx

/-- Strong generated contract for `1`. -/
theorem generatedContract_one (scriptCtx : ScriptContext) (env : SatEnv)
    (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGeneratedContract scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx := by
  refine ⟨.one, ?_, CandidateResult.supports_impossible _⟩
  apply CandidateResult.supports_usable
  apply GeneratedContract.b
  · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · exact BooleanResultFacts.canonical true _ flags
  · simpa [boolToElement] using one_execution flags env.txCtx

/-- A well-formed relative timelock has a generated satisfaction exactly when
    the environment transaction satisfies its sequence predicate. -/
theorem generated_older
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.older n) env).SupportsGenerated scriptCtx
      (.older n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.older n, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.older n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    exact .b ⟨scriptNat n, by simpa [scriptNat] using
      (older_execution facts.decoded satisfied), facts.positive⟩
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- A well-formed absolute timelock has the matching generated-execution
    contract under its transaction locktime predicate. -/
theorem generated_after
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.after n) env).SupportsGenerated scriptCtx
      (.after n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.after n, ?_, CandidateResult.supports_impossible _⟩
  have facts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.after n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    exact .b ⟨scriptNat n, by simpa [scriptNat] using
      (after_execution facts.decoded satisfied), facts.positive⟩
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

private theorem timelockBooleanResultFacts
    {n : Nat} {flags : ScriptFlags} (valid : validTimelockArg n) :
    BooleanResultFacts (scriptNat n) (Int.ofNat n) true
      { z := true } flags := by
  have executionFacts := TimelockExecutionFacts.of_validTimelockArg
    (flags := flags) valid
  rcases valid with ⟨positive, bound⟩
  refine ⟨?_, ?_, executionFacts.positive, ?_, ?_⟩
  · apply decodeScriptNum_scriptNat_of_lt
    simpa [validTimelockArg, MAX_BIP_LOCK_VALUE,
      maxArithmeticScriptNatExclusive] using bound
  · simp
    omega
  · simp
  · simp

/-- Strong relative-timelock contract, including the empty-input and exact
    arithmetic result facts needed by later wrappers. -/
theorem generatedContract_older
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.older n) env).SupportsGeneratedContract scriptCtx
      (.older n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.older n, ?_, CandidateResult.supports_impossible _⟩
  by_cases satisfied : sequenceSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.older n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩ <;> simp
    · exact timelockBooleanResultFacts valid
    · have facts := TimelockExecutionFacts.of_validTimelockArg
        (flags := flags) valid
      simpa [scriptNat] using older_execution facts.decoded satisfied
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- Strong absolute-timelock contract. -/
theorem generatedContract_after
    {scriptCtx : ScriptContext} {n : Nat} {env : SatEnv}
    {flags : ScriptFlags} (valid : validTimelockArg n) :
    (satisfactionCandidates (.after n) env).SupportsGeneratedContract scriptCtx
      (.after n) ⟨.B, { z := true }⟩ flags env.txCtx := by
  refine ⟨.after n, ?_, CandidateResult.supports_impossible _⟩
  by_cases satisfied : locktimeSatisfied n env.txCtx
  · rw [show (satisfactionCandidates (.after n) env).sat =
      .usable [] false by simp [satisfactionCandidates, satisfied]]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨Witness.ItemsBounded.nil, ?_, ?_, ?_⟩ <;> simp
    · exact timelockBooleanResultFacts valid
    · have facts := TimelockExecutionFacts.of_validTimelockArg
        (flags := flags) valid
      simpa [scriptNat] using after_execution facts.decoded satisfied
  · simp [satisfactionCandidates, satisfied, CandidateResult.Supports]

/-- Generated `pk_k` candidates carry the pending signature below the empty K
    argument frame, including the canonical empty dissatisfaction. -/
theorem generated_pk_k
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (emptyEncoding : checkSigEncodingFor flags env.txCtx.sigVersion
      falseElement key.bytes = .ok ()) :
    (satisfactionCandidates (.pk_k key) env).SupportsGenerated scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_k key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_k key) env).sat =
          .usable [signature] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        refine .k [] key.bytes signature rfl
          (pk_k_execution key flags env.txCtx) ?_
        exact checkSigWithEncoding_true (encodings key signature selected)
          (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_k key) env).dsat =
      .usable [falseElement] false by rfl]
    apply CandidateResult.supports_usable
    refine .k [] key.bytes falseElement rfl
      (pk_k_execution key flags env.txCtx) ?_
    exact checkSigWithEncoding_empty
      emptyEncoding
      (sound.emptySignatureInvalid key)

/-- Generated `pk_h` candidates reveal the key in the K argument frame and
    keep the signature below it. -/
theorem generated_pk_h
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (emptyEncoding : checkSigEncodingFor flags env.txCtx.sigVersion
      falseElement key.bytes = .ok ()) :
    (satisfactionCandidates (.pk_h key) env).SupportsGenerated scriptCtx
      (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_h key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_h key) env).sat =
          .usable [signature, key.bytes] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        refine .k [key.bytes] key.bytes signature rfl
          (pk_h_execution key flags env.txCtx) ?_
        exact checkSigWithEncoding_true (encodings key signature selected)
          (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_h key) env).dsat =
      .usable [falseElement, key.bytes] false by rfl]
    apply CandidateResult.supports_usable
    refine .k [key.bytes] key.bytes falseElement rfl
      (pk_h_execution key flags env.txCtx) ?_
    exact checkSigWithEncoding_empty
      emptyEncoding
      (sound.emptySignatureInvalid key)

/-- Modeled context assumptions discharge the empty-signature encoding
    premise of `generated_pk_k` for a context-valid key. -/
theorem generated_pk_k_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_k key) env).SupportsGenerated scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_pk_k sound encodings
    (checkSigEncodingFor_empty_of_modeled valid version modeled)

/-- Modeled context assumptions likewise discharge the exact empty-signature
    boundary for `pk_h`. -/
theorem generated_pk_h_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_h key) env).SupportsGenerated scriptCtx
      (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_pk_h sound encodings
    (checkSigEncodingFor_empty_of_modeled valid version modeled)

/-- Strong `pk_k` contract at the modeled, context-valid boundary. The added
    assumptions are exactly what supplies witness item bounds; the older weak
    theorem remains available when only execution is needed. -/
theorem generatedContract_pk_k_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_k key) env).SupportsGeneratedContract scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_k key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_k key) env).sat =
          .usable [signature] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        apply GeneratedContract.k
          (ownArgs := []) (key := key.bytes) (signature := signature)
        · refine ⟨Witness.ItemsBounded.singleton.mpr
              (selectedSignature_size_le valid version modeled encodings selected),
            ?_, ?_, ?_⟩
          · simp
          · intro _
            exact ⟨signature, rfl⟩
          · intro _ _
            exact ⟨signature, [], rfl,
              selectedSignature_size_ne_zero sound selected⟩
        · rfl
        · exact pk_k_execution key flags env.txCtx
        · exact checkSigWithEncoding_true (encodings key signature selected)
            (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_k key) env).dsat =
      .usable [falseElement] false by rfl]
    apply CandidateResult.supports_usable
    apply GeneratedContract.k
      (ownArgs := []) (key := key.bytes) (signature := falseElement)
    · refine ⟨Witness.ItemsBounded.singleton.mpr falseElement_size_le,
        ?_, ?_, ?_⟩
      · simp
      · intro _
        exact ⟨falseElement, rfl⟩
      · simp
    · rfl
    · exact pk_k_execution key flags env.txCtx
    · exact checkSigWithEncoding_empty
        (checkSigEncodingFor_empty_of_modeled valid version modeled)
        (sound.emptySignatureInvalid key)

/-- Strong modeled `pk_h` contract. The public witness remains wire ordered as
    `[signature, key]`, while the K execution receives `[key]` above the pending
    signature at runtime. -/
theorem generatedContract_pk_h_of_modeled
    {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_h key) env).SupportsGeneratedContract scriptCtx
      (.pk_h key) ⟨.K, { n := true, d := true, u := true }⟩
      flags env.txCtx := by
  refine ⟨.pk_h key, ?_, ?_⟩
  · cases selected : env.signatureFor key with
    | none =>
        simp [satisfactionCandidates, keyCandidates, selected,
          CandidateResult.Supports]
    | some signature =>
        rw [show (satisfactionCandidates (.pk_h key) env).sat =
          .usable [signature, key.bytes] true by simp [satisfactionCandidates,
            keyCandidates, selected]]
        apply CandidateResult.supports_usable
        apply GeneratedContract.k
          (ownArgs := [key.bytes]) (key := key.bytes) (signature := signature)
        · refine ⟨?_, ?_, ?_, ?_⟩
          · simp [Witness.ItemsBounded, selectedSignature_size_le valid version
              modeled encodings selected, validResolvedPubKey_size_le valid]
          · simp
          · simp
          · intro _ _
            exact ⟨key.bytes, [signature], rfl,
              validResolvedPubKey_size_ne_zero valid⟩
        · rfl
        · exact pk_h_execution key flags env.txCtx
        · exact checkSigWithEncoding_true (encodings key signature selected)
            (sound.signatureValid selected)
  · rw [show (satisfactionCandidates (.pk_h key) env).dsat =
      .usable [falseElement, key.bytes] false by rfl]
    apply CandidateResult.supports_usable
    apply GeneratedContract.k
      (ownArgs := [key.bytes]) (key := key.bytes) (signature := falseElement)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le,
          validResolvedPubKey_size_le valid]
      · simp
      · simp
      · simp
    · rfl
    · exact pk_h_execution key flags env.txCtx
    · exact checkSigWithEncoding_empty
        (checkSigEncodingFor_empty_of_modeled valid version modeled)
        (sound.emptySignatureInvalid key)

private theorem generated_hash_sat
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (hashCandidates lock env).sat.Supports fun witness =>
      GeneratedExecution lock.fragment witness true flags env.txCtx .B := by
  cases selected : env.preimageFor lock with
  | none =>
      simpa [hashCandidates, selected] using
        (CandidateResult.supports_impossible (fun witness =>
          GeneratedExecution lock.fragment witness true flags env.txCtx .B))
  | some preimage =>
      rw [show (hashCandidates lock env).sat = .usable [preimage] false by
        simp [hashCandidates, selected]]
      apply CandidateResult.supports_usable
      exact .b ⟨trueElement,
        hash_satisfaction_execution (sound.preimageMatches selected),
        by native_decide⟩

private theorem generated_hash_dsat
    (lock : HashLock) (env : SatEnv) (flags : ScriptFlags) :
    (hashCandidates lock env).dsat.Supports fun witness =>
      GeneratedExecution lock.fragment witness false flags env.txCtx .B := by
  intro witness selected
  simp [hashCandidates, CandidateResult.dontUse,
    CandidateResult.usableWitness?] at selected

/-- All four hashlock rows share the same typed generated-execution proof.
    Their canonical dissatisfaction is DONTUSE, so its public support claim is
    vacuous; `hash_dsat_candidate_execution` retains its raw semantic proof. -/
theorem generated_hash
    {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).SupportsGenerated scriptCtx
      lock.fragment ⟨.B, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  cases lock with
  | sha256 hash =>
      exact ⟨.sha256 hash, generated_hash_sat sound,
        generated_hash_dsat (.sha256 hash) env flags⟩
  | hash256 hash =>
      exact ⟨.hash256 hash, generated_hash_sat sound,
        generated_hash_dsat (.hash256 hash) env flags⟩
  | ripemd160 hash =>
      exact ⟨.ripemd160 hash, generated_hash_sat sound,
        generated_hash_dsat (.ripemd160 hash) env flags⟩
  | hash160 hash =>
      exact ⟨.hash160 hash, generated_hash_sat sound,
        generated_hash_dsat (.hash160 hash) env flags⟩

private theorem generatedContract_hash_sat
    {lock : HashLock} {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) :
    (hashCandidates lock env).sat.Supports fun witness =>
      GeneratedContract lock.fragment witness true flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  cases selected : env.preimageFor lock with
  | none =>
      simpa [hashCandidates, selected] using
        (CandidateResult.supports_impossible (fun witness =>
          GeneratedContract lock.fragment witness true flags env.txCtx
            ⟨.B, { o := true, n := true, d := true, u := true }⟩))
  | some preimage =>
      rw [show (hashCandidates lock env).sat = .usable [preimage] false by
        simp [hashCandidates, selected]]
      apply CandidateResult.supports_usable
      apply GeneratedContract.b
      · refine ⟨Witness.ItemsBounded.singleton.mpr
            (selectedPreimage_size_le sound selected), ?_, ?_, ?_⟩
        · simp
        · intro _
          exact ⟨preimage, rfl⟩
        · intro _ _
          refine ⟨preimage, [], rfl, ?_⟩
          have exactSize := (sound.preimageMatches selected).1
          omega
      · exact BooleanResultFacts.canonical true _ flags
      · simpa [boolToElement, Witness.toInitialStack] using
          hash_satisfaction_execution (sound.preimageMatches selected)

private theorem generatedContract_hash_dsat
    (lock : HashLock) (env : SatEnv) (flags : ScriptFlags) :
    (hashCandidates lock env).dsat.Supports fun witness =>
      GeneratedContract lock.fragment witness false flags env.txCtx
        ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  intro witness selected
  simp [hashCandidates, CandidateResult.dontUse,
    CandidateResult.usableWitness?] at selected

/-- Strong generated contract shared by all four hashlock rows. The raw
    canonical dissatisfaction remains DONTUSE and hence has no public usable
    projection. -/
theorem generatedContract_hash
    {scriptCtx : ScriptContext} {lock : HashLock} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    (satisfactionCandidates lock.fragment env).SupportsGeneratedContract
      scriptCtx lock.fragment
      ⟨.B, { o := true, n := true, d := true, u := true }⟩ flags env.txCtx := by
  cases lock with
  | sha256 hash =>
      exact ⟨.sha256 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.sha256 hash) env flags⟩
  | hash256 hash =>
      exact ⟨.hash256 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.hash256 hash) env flags⟩
  | ripemd160 hash =>
      exact ⟨.ripemd160 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.ripemd160 hash) env flags⟩
  | hash160 hash =>
      exact ⟨.hash160 hash, generatedContract_hash_sat sound,
        generatedContract_hash_dsat (.hash160 hash) env flags⟩

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
            exact ⟨trueElement, [], by simp [childShape], by native_decide⟩
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

/-! ## Compositional connective contracts -/

namespace GeneratedContract

private theorem andVInput
    {firstWitness secondWitness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness true firstMods)
    (second : GeneratedInput secondWitness expected secondMods) :
    GeneratedInput (Witness.combine firstWitness secondWitness) expected {
      z := firstMods.z && secondMods.z
      o := (firstMods.z && secondMods.o) ||
        (firstMods.o && secondMods.z)
      n := firstMods.n || (firstMods.z && secondMods.n)
      d := false
      u := secondMods.u
    } := by
  apply first.combine second
  · intro enabled
    simpa using enabled
  · intro enabled
    simpa [Bool.or_eq_true] using enabled
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with firstN | ⟨firstZero, secondN⟩
    · exact Or.inl ⟨firstN, fun _ => rfl⟩
    · exact Or.inr ⟨firstZero, secondN, fun truth => truth⟩

theorem andV_b
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          exact .b (andVInput firstInput secondInput)
            (secondFacts.retype (by simp))
            (by simpa using firstExec.and_v_b secondExec)

theorem andV_k
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | k secondInput ownArgs key signature stackShape secondExec checked =>
          apply GeneratedContract.k
            (input := andVInput firstInput secondInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.and_v_k secondExec
          · exact checked

theorem andV_v
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | v secondInput secondTrue secondExec =>
          exact .v (andVInput firstInput secondInput) secondTrue
            (by simpa using firstExec.and_v_v secondExec)

private theorem booleanInput
    {firstWitness secondWitness : Witness}
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
      firstMods.n = true ∨
      (firstMods.z = true ∧ secondMods.n = true))
    (truth : expected = true →
      firstExpected = true ∧ secondExpected = true) :
    GeneratedInput (Witness.combine firstWitness secondWitness)
      expected targetMods := by
  apply first.combine second zero one
  intro enabled
  rcases nonzero enabled with firstN | ⟨firstZero, secondN⟩
  · exact Or.inl ⟨firstN, fun expectedTrue => (truth expectedTrue).1⟩
  · exact Or.inr ⟨firstZero, secondN,
      fun expectedTrue => (truth expectedTrue).2⟩

theorem andB
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness firstExpected flags txCtx
      ⟨.B, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness secondExpected
      flags txCtx ⟨.W, secondMods⟩)
    (expectedEq : (firstExpected && secondExpected) = expected) :
    GeneratedContract (.and_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | w secondInput order secondFacts secondExec =>
          apply GeneratedContract.b
          · apply booleanInput firstInput secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · intro expectedTrue
              have both : (firstExpected && secondExpected) = true :=
                expectedEq.trans expectedTrue
              simpa using both
          · exact BooleanResultFacts.canonical expected _ flags
          · have executed := firstExec.and_b secondExec
              (firstFacts.binaryDecoded secondFacts order)
            rw [firstFacts.nonzero, secondFacts.nonzero, expectedEq] at executed
            simpa using executed

theorem orB
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness firstExpected flags txCtx
      ⟨.B, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness secondExpected
      flags txCtx ⟨.W, secondMods⟩)
    (expectedEq : (firstExpected || secondExpected) = expected) :
    GeneratedContract (.or_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := false
        d := true
        u := true
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | w secondInput order secondFacts secondExec =>
          apply GeneratedContract.b
          · apply firstInput.combine secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · simp
          · exact BooleanResultFacts.canonical expected _ flags
          · have executed := firstExec.or_b secondExec
              (firstFacts.binaryDecoded secondFacts order)
            rw [firstFacts.nonzero, secondFacts.nonzero, expectedEq] at executed
            simpa using executed

theorem orC_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedContract (.or_c first second) witness true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
      }⟩ := by
  cases contract with
  | b input facts executed =>
      apply GeneratedContract.v
        (input := input.mono (by simp_all) (by simp_all) (by simp)) rfl
      exact executed.or_c_left (facts.minimalIfSatisfied firstUnit) facts.truth

theorem orC_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness true flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.or_c first second)
      (Witness.combine firstWitness secondWitness) true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | v secondInput secondTrue secondExec =>
          apply GeneratedContract.v
            (input := by
              apply firstInput.combine secondInput
              · intro enabled
                simpa using enabled
              · intro enabled
                right
                simpa using enabled
              · simp)
            rfl
          simpa using firstExec.or_c_right
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec

theorem orD_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedContract (.or_d first second) witness true flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (input.mono (by simp_all) (by simp_all) (by simp))
        (facts.retype (fun _ => firstUnit))
        (executed.or_d_left (facts.minimalIfSatisfied firstUnit) facts.truth)

theorem orD_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.or_d first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          apply GeneratedContract.b
          · apply firstInput.combine secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              right
              simpa using enabled
            · simp
          · exact secondFacts.retype (by simp)
          · simpa using firstExec.or_d_right
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec

private theorem orIInput
    {witness : Witness} {expected : Bool}
    {source firstMods secondMods : CorrectnessModifiers}
    {selector : StackElement}
    (input : GeneratedInput witness expected source)
    (selectorBounded : selector.size ≤ maxScriptElementSize)
    (sourceZero : (firstMods.z && secondMods.z) = true → source.z = true) :
    GeneratedInput (witness.withSelector selector) expected {
      o := firstMods.z && secondMods.z
      d := firstMods.d || secondMods.d
      u := firstMods.u && secondMods.u
    } := by
  apply input.withSelector selectorBounded
  · simp
  · exact sourceZero
  · simp

theorem orILeft_b
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.B, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.B, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (orIInput input trueElement_size_le (by simp_all))
        (facts.retype (by simp_all)) (by simpa using executed.or_i_left)

theorem orIRight_b
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.B, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (orIInput input falseElement_size_le (by simp_all))
        (facts.retype (by simp_all)) (by simpa using executed.or_i_right)

theorem orILeft_k
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.K, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.K, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      apply GeneratedContract.k
        (input := orIInput input trueElement_size_le (by simp_all))
        (ownArgs := trueElement :: ownArgs) (key := key) (signature := signature)
      · simp [stackShape]
      · exact executed.or_i_left
      · exact checked

theorem orIRight_k
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.K, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      apply GeneratedContract.k
        (input := orIInput input falseElement_size_le (by simp_all))
        (ownArgs := falseElement :: ownArgs) (key := key) (signature := signature)
      · simp [stackShape]
      · exact executed.or_i_right
      · exact checked

theorem orILeft_v
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.V, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.V, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | v input expectedTrue executed =>
      exact .v (orIInput input trueElement_size_le (by simp_all)) expectedTrue
        (by simpa using executed.or_i_left)

theorem orIRight_v
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.V, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | v input expectedTrue executed =>
      exact .v (orIInput input falseElement_size_le (by simp_all)) expectedTrue
        (by simpa using executed.or_i_right)

private theorem andorTrueInput
    {firstWitness secondWitness : Witness} {expected : Bool}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness true firstMods)
    (second : GeneratedInput secondWitness expected secondMods) :
    GeneratedInput (Witness.combine firstWitness secondWitness) expected {
      z := firstMods.z && secondMods.z && thirdMods.z
      o := (firstMods.z && secondMods.o && thirdMods.o) ||
        (firstMods.o && secondMods.z && thirdMods.z)
      d := thirdMods.d
      u := secondMods.u && thirdMods.u
    } := by
  apply first.combine second
  · intro enabled
    simp only [Bool.and_eq_true] at enabled
    exact ⟨enabled.1.1, enabled.1.2⟩
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with left | right
    · exact Or.inl ⟨left.1.1, left.1.2⟩
    · exact Or.inr ⟨right.1.1, right.1.2⟩
  · simp

private theorem andorFalseInput
    {firstWitness thirdWitness : Witness} {expected : Bool}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness false firstMods)
    (third : GeneratedInput thirdWitness expected thirdMods) :
    GeneratedInput (Witness.combine firstWitness thirdWitness) expected {
      z := firstMods.z && secondMods.z && thirdMods.z
      o := (firstMods.z && secondMods.o && thirdMods.o) ||
        (firstMods.o && secondMods.z && thirdMods.z)
      d := thirdMods.d
      u := secondMods.u && thirdMods.u
    } := by
  apply first.combine third
  · intro enabled
    simp only [Bool.and_eq_true] at enabled
    exact ⟨enabled.1.1, enabled.2⟩
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with left | right
    · exact Or.inl ⟨left.1.1, left.2⟩
    · exact Or.inr ⟨right.1.1, right.2⟩
  · simp

theorem andorTrue_b
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          exact .b (andorTrueInput firstInput secondInput)
            (secondFacts.retype (by simp_all))
            (by simpa using
              (BExecution.andor_true firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                secondExec))

theorem andorFalse_b
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.B, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | b thirdInput thirdFacts thirdExec =>
          exact .b (andorFalseInput firstInput thirdInput)
            (thirdFacts.retype (by simp_all))
            (by simpa using
              (BExecution.andor_false firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                thirdExec))

theorem andorTrue_k
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | k secondInput ownArgs key signature stackShape secondExec checked =>
          apply GeneratedContract.k
            (input := andorTrueInput firstInput secondInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.andor_true
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec
          · exact checked

theorem andorFalse_k
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.K, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | k thirdInput ownArgs key signature stackShape thirdExec checked =>
          apply GeneratedContract.k
            (input := andorFalseInput firstInput thirdInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.andor_false
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth thirdExec
          · exact checked

theorem andorTrue_v
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | v secondInput expectedTrue secondExec =>
          exact .v (andorTrueInput firstInput secondInput) expectedTrue
            (by simpa using
              (VExecution.andor_true firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                secondExec))

theorem andorFalse_v
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.V, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | v thirdInput expectedTrue thirdExec =>
          exact .v (andorFalseInput firstInput thirdInput) expectedTrue
            (by simpa using
              (VExecution.andor_false firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                thirdExec))

end GeneratedContract

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
        (ArithmeticScriptNatSafe.of_lt (by native_decide)) sumEq
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

/-! ## Tapscript multisignature candidate composition -/

/-- One selected `multi_a` key slot. The witness block is exactly one
    signature element, and its Boolean choice agrees with the encoded signature
    check used by CHECKSIG or CHECKSIGADD. -/
structure MultiASlot (flags : ScriptFlags) (txCtx : TxContext)
    (key : PubKey) (truth : Bool) (frame : Witness)
    (signature : StackElement) : Prop where
  frame_eq : frame = [signature]
  checked : checkSigWithEncoding checkSig checkSchnorrSig flags txCtx
    signature key.bytes = .ok truth
  bounded : signature.size ≤ maxScriptElementSize

/-- Source-order selected key slots for `multi_a`. Serialized child frames stay
    separate until the exact-count trace supplies their combined witness. -/
inductive MultiASlots (flags : ScriptFlags) (txCtx : TxContext) :
    List PubKey → List Bool → List Witness → Stack → Prop where
  | nil : MultiASlots flags txCtx [] [] [] []
  | cons {key : PubKey} {truth : Bool} {frame : Witness}
      {signature : StackElement} {keys : List PubKey} {truths : List Bool}
      {frames : List Witness} {signatures : Stack}
      (head : MultiASlot flags txCtx key truth frame signature)
      (tail : MultiASlots flags txCtx keys truths frames signatures) :
      MultiASlots flags txCtx (key :: keys) (truth :: truths)
        (frame :: frames) (signature :: signatures)

namespace MultiASlots

/-- Append one key slot while preserving source execution order. -/
theorem snoc {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack} {key : PubKey} {truth : Bool} {frame : Witness}
    {signature : StackElement}
    (prior : MultiASlots flags txCtx keys truths frames signatures)
    (last : MultiASlot flags txCtx key truth frame signature) :
    MultiASlots flags txCtx (keys ++ [key]) (truths ++ [truth])
      (frames ++ [frame]) (signatures ++ [signature]) := by
  induction prior with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

/-- The selected one-item frames flatten to source-order runtime signatures. -/
theorem framesShape {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures) :
    (frames.map Witness.toInitialStack).flatten = signatures := by
  induction slots with
  | nil => rfl
  | cons head tail ih => simp [head.frame_eq, ih, Witness.toInitialStack]

/-- Every selected `multi_a` witness frame respects the Script element limit. -/
theorem framesBounded {flags : ScriptFlags} {txCtx : TxContext}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures) :
    ∀ frame ∈ frames, frame.ItemsBounded := by
  induction slots with
  | nil => simp
  | cons head tail ih =>
      intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simpa [head.frame_eq] using
          (Witness.ItemsBounded.singleton.mpr head.bounded)
      · exact ih frame member

end MultiASlots

private theorem choiceFrames_nil_inv
    {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames [] truths frames) :
    truths = [] ∧ frames = [] := by
  generalize pairsEq : ([] : List CandidatePair) = pairs at choices
  cases choices with
  | nil => exact ⟨rfl, rfl⟩
  | snocSat prior selected => simp at pairsEq
  | snocDsat prior selected => simp at pairsEq

private theorem choiceFrames_snoc_inv
    {pairs : List CandidatePair} {pair : CandidatePair}
    {truths : List Bool} {frames : List Witness}
    (choices : CandidatePair.ChoiceFrames (pairs ++ [pair]) truths frames) :
    ∃ priorTruths priorFrames truth frame,
      truths = priorTruths ++ [truth] ∧
      frames = priorFrames ++ [frame] ∧
      CandidatePair.ChoiceFrames pairs priorTruths priorFrames ∧
      ((truth = true ∧ pair.sat.usableWitness? = some frame) ∨
        (truth = false ∧ pair.dsat.usableWitness? = some frame)) := by
  generalize pairsEq : pairs ++ [pair] = allPairs at choices
  cases choices with
  | nil => simp at pairsEq
  | @snocSat otherPairs otherTruths otherFrames otherPair frame prior selected =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherTruths, otherFrames, true, frame, rfl, rfl, prior,
        Or.inl ⟨rfl, selected⟩⟩
  | @snocDsat otherPairs otherTruths otherFrames otherPair frame prior selected =>
      have lengths : pairs.length = otherPairs.length := by
        have := congrArg List.length pairsEq
        simpa using this
      obtain ⟨pairsEq, singletonEq⟩ := List.append_inj pairsEq lengths
      have pairEq : pair = otherPair := by simpa using singletonEq
      subst otherPairs
      subst otherPair
      exact ⟨otherTruths, otherFrames, false, frame, rfl, rfl, prior,
        Or.inr ⟨rfl, selected⟩⟩

private theorem listSnocInductionGenerated {α : Type}
    {motive : List α → Prop} (nil : motive [])
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

private theorem allKeysValid_append
    {scriptCtx : ScriptContext} {first second : List PubKey} :
    CoreFragment.allKeysValid scriptCtx (first ++ second) ↔
      CoreFragment.allKeysValid scriptCtx first ∧
        CoreFragment.allKeysValid scriptCtx second := by
  induction first with
  | nil => simp [CoreFragment.allKeysValid]
  | cons key keys ih =>
      simp [CoreFragment.allKeysValid, ih, and_assoc]

private theorem allKeysValid_of_mem
    {scriptCtx : ScriptContext} {keys : List PubKey}
    (valid : CoreFragment.allKeysValid scriptCtx keys)
    {key : PubKey} (member : key ∈ keys) :
    validResolvedPubKey scriptCtx key := by
  induction keys with
  | nil => simp at member
  | cons head tail ih =>
      simp only [CoreFragment.allKeysValid] at valid
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact valid.1
      · exact ih valid.2 member

/-- Convert exact-count source choices over `multiAKeyChoice` into checked,
    bounded source-order signature slots. -/
theorem CandidatePair.ChoiceFrames.toMultiASlots
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {env : SatEnv} {flags : ScriptFlags}
    (choices : CandidatePair.ChoiceFrames
      (keys.map (fun key => multiAKeyChoice key env)) truths frames)
    (validKeys : CoreFragment.allKeysValid .tapscript keys)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    ∃ signatures, MultiASlots flags env.txCtx keys truths frames signatures := by
  induction keys using listSnocInductionGenerated generalizing truths frames with
  | nil =>
      obtain ⟨rfl, rfl⟩ := choiceFrames_nil_inv choices
      exact ⟨[], .nil⟩
  | snoc keys key ih =>
      have shaped : CandidatePair.ChoiceFrames
          (keys.map (fun child => multiAKeyChoice child env) ++
            [multiAKeyChoice key env]) truths frames := by
        simpa using choices
      obtain ⟨priorTruths, priorFrames, truth, frame, rfl, rfl,
        priorChoices, selected⟩ := choiceFrames_snoc_inv shaped
      have validParts := allKeysValid_append.mp validKeys
      have keyValid : validResolvedPubKey .tapscript key := by
        simpa [CoreFragment.allKeysValid] using validParts.2
      obtain ⟨signatures, priorSlots⟩ :=
        ih priorChoices validParts.1
      rcases selected with satSelected | dsatSelected
      · obtain ⟨rfl, satSelected⟩ := satSelected
        cases signatureFor : env.signatureFor key with
        | none => simp [multiAKeyChoice, signatureFor] at satSelected
        | some signature =>
            have frameEq : frame = [signature] := by
              symm
              simpa [multiAKeyChoice, signatureFor] using satSelected
            refine ⟨signatures ++ [signature], priorSlots.snoc {
              frame_eq := frameEq
              checked := checkSigWithEncoding_true
                (encodings key signature signatureFor)
                (sound.signatureValid signatureFor)
              bounded := selectedSignature_size_le keyValid version modeled
                encodings signatureFor }⟩
      · obtain ⟨rfl, dsatSelected⟩ := dsatSelected
        have frameEq : frame = [falseElement] := by
          symm
          simpa [multiAKeyChoice] using dsatSelected
        refine ⟨signatures ++ [falseElement], priorSlots.snoc {
          frame_eq := frameEq
          checked := checkSigWithEncoding_empty
            (checkSigEncodingFor_empty_of_modeled keyValid version modeled)
            (sound.emptySignatureInvalid key)
          bounded := falseElement_size_le }⟩

/-- A safe canonical natural accumulator decodes for CHECKSIGADD in Tapscript. -/
theorem decodeCheckSigAddCount_scriptNat
    {count : Nat} {flags : ScriptFlags} {txCtx : TxContext}
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe count) :
    decodeCheckSigAddCount flags txCtx (scriptNat count) =
      .ok (Int.ofNat count) := by
  simp [decodeCheckSigAddCount, version, safe.decode flags.minimalData]

/-- The final canonical accumulator and threshold literal satisfy NUMEQUAL's
    two-operand decoder when the shared arithmetic guard holds. -/
theorem decodeBinaryScriptNums_scriptNat_self
    {count : Nat} {flags : ScriptFlags}
    (safe : ArithmeticScriptNatSafe count) :
    decodeBinaryScriptNums flags (scriptNat count) (scriptNat count) =
      .ok (Int.ofNat count, Int.ofNat count) := by
  simp [decodeBinaryScriptNums, safe.decode flags.minimalData]
  rfl

namespace MultiASlots

/-- Execute checked source-order slots as the CHECKSIGADD tail. Arithmetic
    safety of the final exact count is downward closed to every partial
    accumulator. -/
theorem checkSigAddTail
    {flags : ScriptFlags} {txCtx : TxContext} {count total : Nat}
    {keys : List PubKey} {truths : List Bool} {frames : List Witness}
    {signatures : Stack}
    (slots : MultiASlots flags txCtx keys truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe total)
    (totalEq : count + (truths.map Bool.toNat).sum = total) :
    CheckSigAddTailExecution flags txCtx (Int.ofNat count) keys signatures
      (Int.ofNat total) := by
  induction slots generalizing count total with
  | nil =>
      simp at totalEq
      subst total
      exact .nil (Int.ofNat count)
  | @cons key truth frame signature keys truths frames signatures head tail ih =>
      refine CheckSigAddTailExecution.cons (truth := truth)
        (decodeCheckSigAddCount_scriptNat version
          (threshold_accumulator_safe safe totalEq)) head.checked ?_
      simpa using ih safe (threshold_accumulator_step totalEq)

/-- A nonempty exact-count slot list executes `multi_a`: the first key uses
    CHECKSIG, only the remaining source-order keys use CHECKSIGADD, and the
    final canonical accumulator equals the selected threshold. -/
theorem multiAExecution
    {flags : ScriptFlags} {txCtx : TxContext} {threshold : Nat}
    {firstKey : PubKey} {keys : List PubKey} {truths : List Bool}
    {frames : List Witness} {signatures : Stack}
    (slots : MultiASlots flags txCtx (firstKey :: keys) truths frames signatures)
    (version : txCtx.sigVersion = .tapscript)
    (safe : ArithmeticScriptNatSafe threshold)
    (sumEq : (truths.map Bool.toNat).sum = threshold) :
    BExecution (.multi_a threshold (firstKey :: keys)) signatures trueElement
      flags txCtx := by
  cases slots with
  | @cons _ firstTruth _ firstSignature _ tailTruths _ tailSignatures
      firstSlot tail =>
      have tailEq : firstTruth.toNat +
          (tailTruths.map Bool.toNat).sum = threshold := by
        simpa using sumEq
      have tailExec := tail.checkSigAddTail version safe tailEq
      have decoded : decodeBinaryScriptNums flags (scriptNat threshold)
          (scriptNum (Int.ofNat threshold)) =
            .ok (Int.ofNat threshold, Int.ofNat threshold) := by
        simpa [scriptNat] using decodeBinaryScriptNums_scriptNat_self safe
      exact BExecution.multiATrue version firstSlot.checked tailExec decoded
        (by simp)

end MultiASlots

/-- Strong generated contract for the valid nonempty `multi_a` candidate row.
    Satisfaction comes from the exact-count table; dissatisfaction reuses the
    canonical all-empty signature row. -/
theorem generatedContract_multiA_valid
    {threshold : Nat} {firstKey : PubKey} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (valid : candidateThresholdValid threshold (firstKey :: keys).length)
    (validKeys : CoreFragment.allKeysValid .tapscript (firstKey :: keys))
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (multiACandidates threshold (firstKey :: keys) env) .tapscript
        (.multi_a threshold (firstKey :: keys))
        ⟨.B, { d := true, u := true }⟩ flags env.txCtx := by
  have tapVersion : env.txCtx.sigVersion = .tapscript := by
    simpa [ModeledContextVersion] using version
  have typed : HasType .tapscript (.multi_a threshold (firstKey :: keys))
      ⟨.B, { d := true, u := true }⟩ :=
    .multi_a threshold (firstKey :: keys)
      (Nat.one_le_iff_ne_zero.mpr valid.1) valid.2.1
  have valid' : candidateThresholdValid threshold (keys.length + 1) := by
    simpa using valid
  refine ⟨typed, ?_, ?_⟩
  · rw [show (multiACandidates threshold (firstKey :: keys) env).sat =
      CandidatePair.selectExactly threshold
        ((firstKey :: keys).map (fun key => multiAKeyChoice key env)) by
        simp [multiACandidates, valid']]
    intro witness selected
    obtain ⟨frames, trace⟩ :=
      CandidatePair.selectExactly_choiceTrace selected
    obtain ⟨truths, choices, sumEq⟩ := trace.toChoiceFrames
    obtain ⟨signatures, slots⟩ := choices.toMultiASlots validKeys version
      modeled sound encodings
    apply GeneratedContract.b
    · refine ⟨trace.itemsBounded slots.framesBounded, ?_, ?_, ?_⟩ <;> simp
    · exact BooleanResultFacts.canonical true _ flags
    · rw [trace.toInitialStack, slots.framesShape]
      exact slots.multiAExecution tapVersion valid.2.2 sumEq
  · rw [show (multiACandidates threshold (firstKey :: keys) env).dsat =
      .usable (List.replicate (firstKey :: keys).length falseElement) false by
        simp [multiACandidates, valid']]
    apply CandidateResult.supports_usable
    apply GeneratedContract.b
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Witness.ItemsBounded, falseElement_size_le]
      · simp
      · simp
      · simp
    · exact BooleanResultFacts.canonical false _ flags
    · rcases validKeys with ⟨firstValid, restValid⟩
      have firstChecked : checkSigWithEncoding checkSig checkSchnorrSig flags
          env.txCtx falseElement firstKey.bytes = .ok false :=
        checkSigWithEncoding_empty
          (checkSigEncodingFor_empty_of_modeled firstValid version modeled)
          (sound.emptySignatureInvalid firstKey)
      have tailChecked : ∀ key ∈ keys,
          checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx
            falseElement key.bytes = .ok false := by
        intro key member
        have keyValid : validResolvedPubKey .tapscript key :=
          allKeysValid_of_mem restValid member
        exact checkSigWithEncoding_empty
          (checkSigEncodingFor_empty_of_modeled keyValid version modeled)
          (sound.emptySignatureInvalid key)
      have decoded : decodeBinaryScriptNums flags (scriptNat threshold)
          falseElement = .ok (Int.ofNat threshold, 0) := by
        have thresholdDecoded := valid.2.2.decode flags.minimalData
        have zeroDecoded : decodeScriptNum falseElement flags.minimalData
            maxArithmeticScriptNumBytes = .ok 0 := by
          simpa [boolToElement] using
            (BooleanResultFacts.canonical false ({} : CorrectnessModifiers)
              flags).decoded
        simp only [decodeBinaryScriptNums, thresholdDecoded, zeroDecoded]
        rfl
      simpa [Witness.toInitialStack, boolToElement] using
        (multiA_dissatisfaction_execution (threshold := threshold)
          (firstKey := firstKey) (keys := keys) tapVersion valid.1
          firstChecked tailChecked decoded)

/-- Well-formed `multi_a` exposes strong generated support. Well-formedness
    supplies Tapscript key/context and arity facts; the executable arithmetic
    guard is handled separately, with its invalid branch supporting no usable
    witness on either side. -/
theorem generatedContract_multiA_of_wellFormed
    {scriptCtx : ScriptContext} {threshold : Nat} {keys : List PubKey}
    {env : SatEnv} {flags : ScriptFlags}
    (wellFormed : CoreFragment.WellFormed scriptCtx (.multi_a threshold keys))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    CandidatePair.SupportsGeneratedContract
      (satisfactionCandidates (.multi_a threshold keys) env)
      scriptCtx (.multi_a threshold keys)
        ⟨.B, { d := true, u := true }⟩ flags env.txCtx := by
  cases scriptCtx with
  | p2wsh =>
      simp [CoreFragment.WellFormed,
        ScriptContext.permitsCheckSigAddMulti] at wellFormed
  | tapscript =>
      rcases wellFormed with ⟨permits, thresholdValid, validKeys⟩
      have typed : HasType .tapscript (.multi_a threshold keys)
          ⟨.B, { d := true, u := true }⟩ :=
        .multi_a threshold keys thresholdValid.1 thresholdValid.2
      by_cases valid : candidateThresholdValid threshold keys.length
      · cases keys with
        | nil =>
            rcases thresholdValid with ⟨positive, atMost⟩
            simp at atMost
            omega
        | cons firstKey keys =>
            rw [satisfactionCandidates_multi_a]
            exact generatedContract_multiA_valid valid validKeys version modeled
              sound encodings
      · rw [satisfactionCandidates_multi_a]
        have empty : multiACandidates threshold keys env = {} := by
          simp [multiACandidates, valid]
        rw [empty]
        exact ⟨typed, CandidateResult.supports_impossible _,
          CandidateResult.supports_impossible _⟩

end LeanMiniscript.Miniscript
