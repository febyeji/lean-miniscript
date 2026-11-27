import LeanMiniscript.Extraction.WitnessFrameAgreement


namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- A third-party witness accepted by Core for a sane Tapscript spend equals
    the generated final satisfaction under the spend's local material hypotheses. -/
theorem tapscriptNonMalleability : TapscriptNonMalleability := by
  intro sane bytes scriptPubKey suffix env flags ctx oracles keyPath arguments other
    serialized spend run generated eligible accepted
  apply TapscriptWitness.nonMalleability_of_rootFrameUnique sane _ bytes scriptPubKey suffix env flags ctx
    oracles keyPath arguments other serialized spend run generated eligible.1 eligible.2 accepted
  exact TapscriptRecovery.root_frame sane

end LeanMiniscript.Extraction
