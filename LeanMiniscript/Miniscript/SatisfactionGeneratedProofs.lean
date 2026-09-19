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

end LeanMiniscript.Miniscript
