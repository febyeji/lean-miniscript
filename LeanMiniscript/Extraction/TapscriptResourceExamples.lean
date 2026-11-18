import LeanMiniscript.Extraction.MiniscriptObligations
import LeanMiniscript.Extraction.TapscriptDissatisfactionCounterexample

namespace LeanMiniscript.Extraction.TapscriptResourceExamples

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script

private def key (n : UInt8) : PubKey :=
  PubKey.ofBytes ⟨Array.replicate 31 0 ++ #[n]⟩

private def signature : CoreFragment := .c (.pk_k (key 1))
private def multi : CoreFragment := .multi_a 1 [key 2, key 3]
private def branch : CoreFragment := .or_i multi (.and_v (.v signature) .one)
private def absent : CoreFragment := .and_b .zero (.a multi)
private def sig : ByteArray := ⟨Array.replicate 64 1⟩
private def signed (env : SatEnv) : SatEnv :=
  { env with signatureFor := fun _ => some sig }
private def unsigned (env : SatEnv) : SatEnv :=
  { env with signatureFor := fun _ => none }

/-- Signature, CHECKSIGADD and branch paths generate their ordinary witnesses
    inside the accepted checked domain. These vectors test generation only. -/
theorem generatedSatisfactions (env : SatEnv) :
    (checkSane .tapscript signature).toOption.isSome = true ∧
    (checkSane .tapscript multi).toOption.isSome = true ∧
    (checkSane .tapscript branch).toOption.isSome = true ∧
    satisfy signature (signed env) = some [sig] ∧
    satisfy multi (signed env) = some [falseElement, sig] ∧
    satisfy branch (signed env) = some [sig, falseElement] := by
  exact ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

private def saneSignature : SaneFragment .tapscript :=
  (checkSane .tapscript signature).toOption.get (by decide)
private def saneMulti : SaneFragment .tapscript :=
  (checkSane .tapscript multi).toOption.get (by decide)
private def saneBranch : SaneFragment .tapscript :=
  (checkSane .tapscript branch).toOption.get (by decide)

/-- Each supported ordinary satisfaction completes with the budget supplied
    by its full witness under the existing environment contracts. -/
theorem satisfactionRuntime
    (sane : SaneFragment .tapscript)
    (selected : sane = saneSignature ∨ sane = saneMulti ∨ sane = saneBranch)
    (env : SatEnv) (flags : ScriptFlags) (oracle : CryptoOracle)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags) (agreement : oracle.RefinesModel)
    (witness suffix : Witness)
    (generated : satisfy sane.checked.fragment env = some witness) :
    witness.ItemsBounded ∧ witness.length ≤ maxStackSize ∧ ∃ top remaining,
      evaluateWithRuntimeLimits oracle sane.compile witness.toInitialStack [] flags
        env.txCtx (initialValidationWeight (witness ++ suffix)) =
          .success [top] [] remaining ∧ castToBool top = true := by
  have pushes : ∀ element ∈ sane.compile, element.pushSize ≤ maxScriptElementSize := by
    rcases selected with rfl | rfl | rfl <;> decide
  obtain ⟨top, remaining, completed, truth, count⟩ :=
    sane.tapscript_satisfy_runtime_complete_witness sound encodings version modeled generated
      agreement pushes (List.sublist_append_left witness suffix)
  exact ⟨satisfy_itemsBounded sane.validMiniscript sound encodings version modeled generated,
    count, top, remaining, completed, truth⟩

private def saneAbsent : SaneFragment .tapscript :=
  (checkSane .tapscript absent).toOption.get (by decide)

/-- A missing satisfaction path still generates a bounded dissatisfaction. -/
theorem absentGenerated (env : SatEnv) :
    maxSatisfactionExecutionStack absent = none ∧
    satisfy absent (unsigned env) = none ∧
    dissatisfy absent (unsigned env) = some [falseElement, falseElement] := by
  exact ⟨rfl, rfl, rfl⟩

theorem absentRuntime (env : SatEnv) (flags : ScriptFlags) (oracle : CryptoOracle)
    (sound : (unsigned env).Sound) (encodings : (unsigned env).EncodingSound flags)
    (version : ModeledContextVersion .tapscript (unsigned env).txCtx)
    (modeled : ModeledContextFlags .tapscript flags) (agreement : oracle.RefinesModel)
    (suffix : Witness) :
    ∃ top remaining,
      evaluateWithRuntimeLimits oracle saneAbsent.compile [falseElement, falseElement]
        [] flags (unsigned env).txCtx (initialValidationWeight ([falseElement, falseElement] ++ suffix)) =
          .success [top] [] remaining ∧ castToBool top = false := by
  obtain ⟨top, remaining, completed, truth, _⟩ :=
    saneAbsent.tapscript_dissatisfy_runtime_complete_witness sound encodings version modeled
      (absentGenerated env).2.2 agreement (by decide)
      (List.sublist_append_left [falseElement, falseElement] suffix)
  exact ⟨top, remaining, completed, truth⟩

/-- The corrected depth-999 boundary has no satisfaction path. The public
    resource obligation covers its empty dissatisfaction under the original
    byte, spend and run premises, without a satisfaction or d-type premise. -/
theorem edgeCore (bytes scriptPubKey : ByteArray) (suffix : Witness)
    (env : SatEnv) (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (serialized : CompiledScriptBytes
      TapscriptDissatisfactionCounterexample.edgeSane.checked.fragment bytes)
    (spend : CompiledScriptSpend .tapscript bytes scriptPubKey suffix)
    (run : CompiledScriptRun .tapscript env flags ctx oracles bytes)
    (error : CoreVerificationError)
    (failed : coreVerifyScript flags ctx oracles keyPath ByteArray.empty scriptPubKey
      ([] ++ suffix) = .error error) : error.isResourceLimit = false := by
  exact tapscriptResourceLimits TapscriptDissatisfactionCounterexample.edgeSane
    bytes scriptPubKey suffix env flags ctx oracles keyPath [] serialized spend run
    (.inr (TapscriptDissatisfactionCounterexample.generated 999 env)) error failed

example : TapscriptResourceLimits := tapscriptResourceLimits

end LeanMiniscript.Extraction.TapscriptResourceExamples
