import LeanMiniscript.Extraction.MiniscriptCompilation
import LeanMiniscript.Extraction.BitcoinCoreWitnessV0Proofs

/-!
The diagnostic commit `62bf7e5e985c89685f680d59453722465b0dcce7` showed that
`n:` repeated 202 times around `0` passed the old sanity boundary while Core
returned OP_COUNT. The frozen historical predicate and obligation below retain
that counterexample, including its conditional cryptographic/run premises.
The current boundary rejects it; the 201-opcode neighbor remains supported.
-/

namespace LeanMiniscript.Extraction.DissatisfactionCounterexample

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script
open LeanMiniscript.Bitcoin

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option cbv.maxSteps 2000000

def wrapN : Nat → CoreFragment → CoreFragment
  | 0, fragment => fragment
  | n + 1, fragment => .n (wrapN n fragment)
def fragment := wrapN 202 .zero

def flags : CoreVerificationFlags := { witness := true, script := {} }

def context : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty, sigVersion := .witnessV0 }

def bytes := ByteArray.mk (#[0] ++ Array.replicate 202 0x92)

theorem validDissatisfiable : ValidDissatisfiableMiniscript .p2wsh fragment := by
  refine ⟨{ z := true, d := true, u := true }, ⟨?_, ?_⟩, rfl⟩
  · decide
  · exact (inferTyped .p2wsh fragment).get (by decide) |>.property

theorem generated (environment : SatEnv) : dissatisfy fragment environment = some [] := by
  rfl

theorem serialized : serializeScript (compile fragment) = .ok bytes := by rfl

/-- The resource predicate at the preserved diagnostic HEAD, before adding
    any dissatisfaction-path check. -/
def historicalResourceLimitsSatisfied (ctx : ScriptContext) (f : CoreFragment) : Bool :=
  compiledScriptSizeWithinLimit ctx f && satisfactionOpsWithinLimit ctx f &&
    satisfactionStackWithinLimit ctx f

/-- Frozen historical sanity certificate: every original conjunct is retained. -/
structure HistoricalSaneFragment (ctx : ScriptContext) where
  checked : CheckedFragment ctx
  malleability : MalleabilityModifiers
  topLevel : checked.ty.base = .B
  hasMalleability : HasMalleability ctx checked.fragment malleability
  noDuplicateKeys : checked.fragment.NoDuplicateKeys
  nonMalleable : malleability.nonMalleable = true
  needsSignature : malleability.s = true
  withinResourceLimits : historicalResourceLimitsSatisfied ctx checked.fragment = true

def sane : HistoricalSaneFragment .p2wsh where
  checked := {
    fragment := fragment
    ty := (inferTyped .p2wsh fragment).get (by decide) |>.val
    wellFormed := by decide
    hasType := (inferTyped .p2wsh fragment).get (by decide) |>.property
  }
  malleability := (inferMalleabilityTyped .p2wsh fragment).get (by decide) |>.val
  topLevel := by decide
  hasMalleability := (inferMalleabilityTyped .p2wsh fragment).get (by decide) |>.property.1
  noDuplicateKeys := by decide
  nonMalleable := by decide
  needsSignature := by decide
  withinResourceLimits := by decide

/-- The original obligation with only its sanity certificate frozen to the
    diagnostic version. This is not the current `P2WSHDissatisfaction`. -/
def HistoricalP2WSHDissatisfaction : Prop :=
  ∀ (sane : HistoricalSaneFragment .p2wsh) (bytes scriptPubKey : ByteArray)
    (suffix : List ByteArray) (env : SatEnv) (flags : CoreVerificationFlags)
    (ctx : TxContext) (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (keyPath : CoreKeyPathChecker) (arguments : Witness),
    CompiledScriptBytes sane.checked.fragment bytes →
    CompiledScriptSpend .p2wsh bytes scriptPubKey suffix →
    CompiledScriptRun .p2wsh env flags ctx oracles bytes →
    ValidDissatisfiableMiniscript .p2wsh sane.checked.fragment →
    dissatisfy sane.checked.fragment env = some arguments →
    coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      (arguments ++ suffix) = .error (.script .evalFalse)

theorem resourceCounterexample :
    ValidDissatisfiableMiniscript .p2wsh sane.checked.fragment ∧
    (∀ environment, dissatisfy sane.checked.fragment environment = some []) ∧
    nonPushOpCount (compile sane.checked.fragment) > MAX_OPS_PER_SCRIPT := by
  refine ⟨validDissatisfiable, generated, ?_⟩
  decide


theorem rawOpCount :
    executeCoreScript flags context (fun _ _ => CryptoOracle.model)
      { scriptBytes := bytes, stack := [], sigVersion := .witnessV0 } =
      .error (.script .opCount) := by
  cbv

theorem coreOpCount
    (programTruth : castToBool (LeanHash160.SHA256.hash bytes) = true) :
    coreVerifyScript flags context (fun _ _ => CryptoOracle.model)
      (fun _ _ _ => .ok ()) ByteArray.empty (ScriptBytes.p2wsh bytes) [bytes] =
      .error (.script .opCount) := by
  have witnessFailure : verifyCoreWitnessProgram
      (executeCoreScript flags context (fun _ _ => CryptoOracle.model)) flags
      [bytes] 0 (LeanHash160.SHA256.hash bytes) false (fun _ _ _ => .ok ()) =
      .error (.script .opCount) := by
    simp [verifyCoreWitnessProgram, sha256_size, executeCoreWitnessScript,
      rawOpCount, bind, Except.bind]
  have empty : executeCoreScript flags context (fun _ _ => CryptoOracle.model)
      { scriptBytes := ByteArray.empty } = .ok [] := by
    simp [executeCoreScript, CoreScriptExecution.executeCoreRawLoop]
  have pushOnly : coreScriptIsPushOnly ByteArray.empty = true := rfl
  have pub := executeCoreScript_p2wshOutput flags context
    (fun _ _ => CryptoOracle.model) bytes
  simp only [coreVerifyScript, verifyScriptWith, verifyCoreScripts, pushOnly, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, empty, bind, Except.bind, pub]
  change (Except.bind
    (if castToBool (LeanHash160.SHA256.hash bytes) then .ok ()
      else .error (CoreVerificationError.script .evalFalse)) _) = _
  have enabled : flags.witness = true := rfl
  simp [programTruth, enabled, decodeCoreWitnessProgram_p2wsh,
    witnessFailure, ByteArray.size_empty, Except.bind]


theorem incompatible
    (environment : SatEnv)
    (hashes : ∀ data, (LeanMiniscript.Script.hash160 data).size = 20)
    (programTruth : castToBool (LeanHash160.SHA256.hash bytes) = true)
    (run : CompiledScriptRun .p2wsh environment flags context
      (fun _ _ => CryptoOracle.model) bytes) :
    ¬ HistoricalP2WSHDissatisfaction := by
  intro claimed
  have predicted := claimed sane bytes (ScriptBytes.p2wsh bytes) [bytes]
    environment flags context (fun _ _ => CryptoOracle.model)
    (fun _ _ _ => .ok ()) [] ⟨serialized, hashes⟩ ⟨rfl, rfl, programTruth⟩
    run validDissatisfiable (generated environment)
  change coreVerifyScript flags context (fun _ _ => CryptoOracle.model)
    (fun _ _ _ => .ok ()) ByteArray.empty (ScriptBytes.p2wsh bytes) [bytes] =
      .error (.script .evalFalse) at predicted
  rw [coreOpCount programTruth] at predicted
  cases predicted

/-- Absent satisfaction paths no longer hide excessive dissatisfaction cost. -/
theorem noSatisfactionPath : maxSatisfactionOpCount fragment = none := by rfl

theorem correctedRejects :
    checkSane .p2wsh fragment = .error .resourceLimitsExceeded := by rfl

theorem opcodeEdge :
    nonPushOpCount (compile (wrapN 201 .zero)) = 201 ∧
    resourceLimitsSatisfied .p2wsh (wrapN 201 .zero) = true ∧
    resourceLimitsSatisfied .p2wsh fragment = false := by decide

def edgeSane : SaneFragment .p2wsh :=
  (checkSane .p2wsh (wrapN 201 .zero)).toOption.get (by decide)

theorem edgeGenerated (env : SatEnv) :
    dissatisfy edgeSane.checked.fragment env = some [] := by rfl

/-- At the accepted edge, the raw Core run reaches a false singleton. -/
theorem edgeCore :
    executeCoreScript flags context (fun _ _ => CryptoOracle.model)
      { scriptBytes := ByteArray.mk (#[0] ++ Array.replicate 201 0x92),
        stack := [], sigVersion := .witnessV0 } = .ok [ByteArray.empty] := by cbv

private def key (n : UInt8) : PubKey :=
  PubKey.ofBytes ⟨#[2] ++ Array.replicate 31 0 ++ #[n]⟩

private def multi : CoreFragment := .multi 1 [key 1, key 2]
private def alternate : CoreFragment :=
  .or_i multi (.multi 1 [key 3, key 4, key 5])
private def absent : CoreFragment := .and_b .zero (.a multi)

/-- Both branches contribute static opcodes, but only the larger executed
    multisignature contributes dynamic keys. Summing both would reject 201. -/
theorem alternativePaths :
    (opPathBounds alternate).dsat = some 3 ∧
    nonPushOpCount (compile alternate) = 5 ∧
    resourceLimitsSatisfied .p2wsh (wrapN 193 alternate) = true ∧
    resourceLimitsSatisfied .p2wsh (wrapN 194 alternate) = false := by decide

/-- No satisfaction exists, but the dissatisfaction executes CHECKMULTISIG;
    checking static opcodes alone would incorrectly accept the 202 case. -/
theorem absentMultisigPaths :
    (opPathBounds absent).sat = none ∧
    (opPathBounds absent).dsat = some 2 ∧
    nonPushOpCount (compile absent) = 4 ∧
    resourceLimitsSatisfied .p2wsh (wrapN 195 absent) = true ∧
    resourceLimitsSatisfied .p2wsh (wrapN 196 absent) = false := by decide

/-- Signed and multisignature examples retain all sanity checks, including
    unique keys; the absent-satisfaction example remains supported too. -/
theorem supportedExamples :
    (checkSane .p2wsh (.c (.pk_k (key 1)))).toOption.isSome = true ∧
    (checkSane .p2wsh multi).toOption.isSome = true ∧
    (checkSane .p2wsh alternate).toOption.isSome = true ∧
    (checkSane .p2wsh absent).toOption.isSome = true := by decide

private def generatedBranch : CoreFragment :=
  .or_i multi (.and_v (.v (.c (.pk_k (key 3)))) .one)

/-- Each generated example carries the target obligation's `d` validity. -/
theorem validExamples :
    ValidDissatisfiableMiniscript .p2wsh multi ∧
    ValidDissatisfiableMiniscript .p2wsh generatedBranch ∧
    ValidDissatisfiableMiniscript .p2wsh absent := by
  constructor
  · refine ⟨((inferTyped .p2wsh multi).get (by decide)).val.mods,
      ⟨by decide, ?_⟩, by decide⟩
    exact ((inferTyped .p2wsh multi).get (by decide)).property
  · constructor
    · refine ⟨((inferTyped .p2wsh generatedBranch).get (by decide)).val.mods,
        ⟨by decide, ?_⟩, by decide⟩
      exact ((inferTyped .p2wsh generatedBranch).get (by decide)).property
    · refine ⟨((inferTyped .p2wsh absent).get (by decide)).val.mods,
        ⟨by decide, ?_⟩, by decide⟩
      exact ((inferTyped .p2wsh absent).get (by decide)).property

private def noSignatures : SatEnv := {
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => ByteArray.empty
  txCtx := context
}

theorem generatedExamples :
    (checkSane .p2wsh generatedBranch).toOption.isSome = true ∧
    dissatisfy (.c (.pk_k (key 1))) noSignatures = some [falseElement] ∧
    dissatisfy multi noSignatures = some [falseElement, falseElement] ∧
    dissatisfy generatedBranch noSignatures = some [falseElement, falseElement, trueElement] ∧
    dissatisfy absent noSignatures = some [falseElement, falseElement] := by decide

private def encodedBytes (f : CoreFragment) : ByteArray :=
  (serializeScript (compileForResourceAnalysis f)).toOption.getD ByteArray.empty

/-- Representative generated witnesses reach a false singleton in Core with
    a rejecting signature callback, as required for the empty signatures. -/
theorem generatedCoreExamples :
    executeCoreScript flags context
      (fun _ _ => { CryptoOracle.model with checkSig := fun _ _ _ => false })
      { scriptBytes := encodedBytes multi,
        stack := [falseElement, falseElement], sigVersion := .witnessV0 } =
        .ok [falseElement] ∧
    executeCoreScript flags context
      (fun _ _ => { CryptoOracle.model with checkSig := fun _ _ _ => false })
      { scriptBytes := encodedBytes generatedBranch,
        stack := [trueElement, falseElement, falseElement], sigVersion := .witnessV0 } =
        .ok [falseElement] ∧
    executeCoreScript flags context
      (fun _ _ => { CryptoOracle.model with checkSig := fun _ _ _ => false })
      { scriptBytes := encodedBytes absent,
        stack := [falseElement, falseElement], sigVersion := .witnessV0 } =
        .ok [falseElement] := by
  constructor
  · cbv
  constructor <;> cbv

end LeanMiniscript.Extraction.DissatisfactionCounterexample
