import LeanMiniscript.Extraction.WitnessFrameAgreement

namespace LeanMiniscript.Extraction

/-- Every eligible, Core-accepted P2WSH witness for a sane fragment equals the
    generated witness under local hash recovery and preimage/signature separation. -/
theorem p2wshNonMalleability : P2WSHNonMalleability := by
  intro sane bytes scriptPubKey suffix env flags ctx oracles keyPath arguments other
    serialized spend run generated eligible accepted
  exact P2WSHRecovery.nonMalleability_of_rootFrameUnique sane (TapscriptRecovery.root_frame sane)
    bytes scriptPubKey suffix env flags ctx oracles keyPath arguments other serialized spend run
    generated eligible.1 eligible.2.1 eligible.2.2 accepted

end LeanMiniscript.Extraction
