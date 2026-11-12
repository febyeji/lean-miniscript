import LeanMiniscript.Extraction.MiniscriptCompilationProofs

/-!
# Miniscript compilation obligation list

Each of the eight propositions of `MiniscriptCompilation` with the name of the
theorem that proves it. `scripts/miniscript_obligations.lean` reports a
theorem as missing when this module and its imports do not declare it, so a
module with a new proof must be imported here. Each theorem states its
proposition by name, such as `theorem p2wshSatisfaction : P2WSHSatisfaction`.
-/

namespace LeanMiniscript.Extraction

/-- An obligation's proposition and the theorem that proves it. -/
structure MiniscriptObligation where
  proposition : Lean.Name
  theoremName : Lean.Name

-- TODO(miniscript-compilation): prove the obligations below other than
-- `tapscriptSatisfaction`.
def miniscriptObligations : List MiniscriptObligation := [
  ⟨``P2WSHSatisfaction, `LeanMiniscript.Extraction.p2wshSatisfaction⟩,
  ⟨``TapscriptSatisfaction, ``tapscriptSatisfaction⟩,
  ⟨``P2WSHDissatisfaction, `LeanMiniscript.Extraction.p2wshDissatisfaction⟩,
  ⟨``TapscriptDissatisfaction, `LeanMiniscript.Extraction.tapscriptDissatisfaction⟩,
  ⟨``P2WSHNonMalleability, `LeanMiniscript.Extraction.p2wshNonMalleability⟩,
  ⟨``TapscriptNonMalleability, `LeanMiniscript.Extraction.tapscriptNonMalleability⟩,
  ⟨``P2WSHResourceLimits, `LeanMiniscript.Extraction.p2wshResourceLimits⟩,
  ⟨``TapscriptResourceLimits, `LeanMiniscript.Extraction.tapscriptResourceLimits⟩
]

end LeanMiniscript.Extraction
