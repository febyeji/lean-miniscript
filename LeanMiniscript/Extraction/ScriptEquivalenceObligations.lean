import LeanMiniscript.Extraction.ScriptEquivalenceProofs

/-!
# Script and VerifyScript equivalence obligation list

Each of the nine propositions of `ScriptEquivalence` with the name of the
theorem that proves it. `scripts/script_equivalence_obligations.lean` reports
a theorem as missing when this module and its imports do not declare it, so a
module with a new proof must be imported here. Each theorem states its
proposition by name, such as `theorem baseExecutionAgreement :
BaseExecutionAgreement`.
-/

namespace LeanMiniscript.Extraction

/-- An obligation's proposition and the theorem that proves it. -/
structure ScriptEquivalenceObligation where
  proposition : Lean.Name
  theoremName : Lean.Name

-- TODO(script-equivalence): prove the six VerifyScript obligations below.
def scriptEquivalenceObligations : List ScriptEquivalenceObligation := [
  ⟨``BaseExecutionAgreement, ``baseExecutionAgreement⟩,
  ⟨``WitnessV0ExecutionAgreement, ``witnessV0ExecutionAgreement⟩,
  ⟨``TapscriptExecutionAgreement, ``tapscriptExecutionAgreement⟩,
  ⟨``LegacyVerificationAgreement, `LeanMiniscript.Extraction.legacyVerificationAgreement⟩,
  ⟨``P2SHVerificationAgreement, `LeanMiniscript.Extraction.p2shVerificationAgreement⟩,
  ⟨``WitnessV0VerificationAgreement,
    `LeanMiniscript.Extraction.witnessV0VerificationAgreement⟩,
  ⟨``P2SHWitnessV0VerificationAgreement,
    `LeanMiniscript.Extraction.p2shWitnessV0VerificationAgreement⟩,
  ⟨``TaprootKeyPathVerificationAgreement,
    `LeanMiniscript.Extraction.taprootKeyPathVerificationAgreement⟩,
  ⟨``TaprootScriptPathVerificationAgreement,
    `LeanMiniscript.Extraction.taprootScriptPathVerificationAgreement⟩
]

end LeanMiniscript.Extraction
