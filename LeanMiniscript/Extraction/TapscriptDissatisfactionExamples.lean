import LeanMiniscript.Extraction.MiniscriptObligations
import LeanMiniscript.Extraction.TapscriptDissatisfactionCounterexample

/-! Kernel-checked regressions for the corrected Tapscript dissatisfaction
    domain. Raw execution examples use empty signatures and require no Taproot
    commitment or cryptographic environment witness. -/

namespace LeanMiniscript.Extraction.TapscriptDissatisfactionExamples

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script

set_option maxRecDepth 10000

private def key (n : UInt8) : PubKey :=
  PubKey.ofBytes ⟨Array.replicate 31 0 ++ #[n]⟩

private def signature : CoreFragment := .c (.pk_k (key 1))
private def multi : CoreFragment := .multi_a 1 [key 2, key 3]
private def branch : CoreFragment :=
  .or_i multi (.and_v (.v signature) .one)
private def absent : CoreFragment := .and_b .zero (.a multi)

private def flags : CoreVerificationFlags := { witness := true, taproot := true, script := {} }
private def context : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty, sigVersion := .tapscript }
private def noSignatures : SatEnv := {
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => ByteArray.empty
  txCtx := context
}

/-- All sanity conjuncts, including unique keys and HASSIG, still pass. -/
theorem supportedExamples :
    (checkSane .tapscript signature).toOption.isSome = true ∧
    (checkSane .tapscript multi).toOption.isSome = true ∧
    (checkSane .tapscript branch).toOption.isSome = true ∧
    (checkSane .tapscript absent).toOption.isSome = true := by decide

/-- The absent-satisfaction example has a real dissatisfaction stack bound. -/
theorem absentPath :
    maxSatisfactionExecutionStack absent = none ∧
    maxDissatisfactionExecutionStack absent = some 4 := by decide

/-- Each supported example has the unchanged target's dissatisfaction typing. -/
theorem validExamples :
    ValidDissatisfiableMiniscript .tapscript signature ∧
    ValidDissatisfiableMiniscript .tapscript multi ∧
    ValidDissatisfiableMiniscript .tapscript branch ∧
    ValidDissatisfiableMiniscript .tapscript absent := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨((inferTyped .tapscript signature).get (by decide)).val.mods,
      ⟨by decide, ?_⟩, by decide⟩
    exact (inferTyped .tapscript signature).get (by decide) |>.property
  · refine ⟨((inferTyped .tapscript multi).get (by decide)).val.mods,
      ⟨by decide, ?_⟩, by decide⟩
    exact (inferTyped .tapscript multi).get (by decide) |>.property
  · refine ⟨((inferTyped .tapscript branch).get (by decide)).val.mods,
      ⟨by decide, ?_⟩, by decide⟩
    exact (inferTyped .tapscript branch).get (by decide) |>.property
  · refine ⟨((inferTyped .tapscript absent).get (by decide)).val.mods,
      ⟨by decide, ?_⟩, by decide⟩
    exact (inferTyped .tapscript absent).get (by decide) |>.property

/-- Generation preserves empty-signature and branch-selector witness order. -/
theorem generatedExamples :
    dissatisfy signature noSignatures = some [falseElement] ∧
    dissatisfy multi noSignatures = some [falseElement, falseElement] ∧
    dissatisfy branch noSignatures = some [falseElement, falseElement, trueElement] ∧
    dissatisfy absent noSignatures = some [falseElement, falseElement] := by decide

private def encodedBytes (f : CoreFragment) : ByteArray :=
  (serializeScript (compileForResourceAnalysis f)).toOption.getD ByteArray.empty

private def raw (f : CoreFragment) (arguments : Witness) : Except CoreVerificationError Stack :=
  executeCoreScript flags context (fun _ _ => CryptoOracle.model)
    { scriptBytes := encodedBytes f, stack := arguments.reverse, sigVersion := .tapscript }

/-- Empty CHECKSIG/CHECKSIGADD signatures execute with a zero validation budget
    and leave a false singleton in the Core byte executor. -/
theorem generatedCoreExamples :
    raw signature [falseElement] = .ok [falseElement] ∧
    raw multi [falseElement, falseElement] = .ok [falseElement] ∧
    raw branch [falseElement, falseElement, trueElement] = .ok [falseElement] ∧
    raw absent [falseElement, falseElement] = .ok [falseElement] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

/-- A signature-bearing satisfaction remains selectable inside the corrected
    checked domain. This tests generation without asserting a model signature. -/
theorem generatedSatisfaction :
    satisfyFinal signature { noSignatures with
      signatureFor := fun _ => some (ByteArray.mk (Array.replicate 64 1)) } =
      some [ByteArray.mk (Array.replicate 64 1)] := by decide

/-- Dissatisfaction may execute a satisfied child. Its signature debit is
    funded by the same generated payload contract, under the existing sound
    environment premises; it need not be zero. -/
theorem signedChildFunding
    (env : SatEnv) (scriptFlags : ScriptFlags) (witness : Witness)
    (top : StackElement) (resources : ExecutionResources)
    (sound : env.Sound) (encodings : env.EncodingSound scriptFlags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript scriptFlags)
    (generated : dissatisfy (.and_v (.v signature) multi) env = some witness)
    (observed : EvalResources (compile (.and_v (.v signature) multi))
      witness.toInitialStack [] scriptFlags env.txCtx [top] [] resources) :
    resources.signatureWeight ≤ (witness.map ByteArray.size).sum := by
  apply dissatisfy_signatureWeight_le_payload _ sound encodings version modeled generated observed
  refine ⟨((inferTyped .tapscript (.and_v (.v signature) multi)).get (by decide)).val.mods,
    by decide, ?_⟩
  exact (inferTyped .tapscript (.and_v (.v signature) multi)).get (by decide) |>.property

end LeanMiniscript.Extraction.TapscriptDissatisfactionExamples
