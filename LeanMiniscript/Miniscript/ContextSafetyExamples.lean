import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

/-! # Context-safe compiler fixtures -/

private def compressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0x11).toArray⟩

private def oddCompressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x03] ++ (List.replicate 32 0x11).toArray⟩

private def invalidCompressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x04] ++ (List.replicate 32 0x11).toArray⟩

private def xOnlyKey : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0x22).toArray⟩

private def legacyMulti : CoreFragment := .multi 1 [compressedKey]

private def tapscriptMulti : CoreFragment := .multi_a 1 [xOnlyKey, xOnlyKey]

example : legacyMulti.WellFormed .p2wsh := by native_decide

example : (CoreFragment.pk_k oddCompressedKey).WellFormed .p2wsh := by
  native_decide

example : tapscriptMulti.WellFormed .tapscript := by native_decide

/-- Length alone does not make a P2WSH key compressed: BIP 380 requires a
    `02` or `03` serialization prefix. -/
example : ¬ (CoreFragment.pk_k invalidCompressedKey).WellFormed .p2wsh := by
  native_decide

example :
    ¬ (KeyMaterial.publicKey invalidCompressedKey.bytes).CompatibleWith .p2wsh := by
  change ¬ validCompressedPubKeyBytes invalidCompressedKey.bytes
  native_decide

example :
    ¬ (KeyMaterial.publicKey invalidCompressedKey.bytes).CompatibleWith .tapscript := by
  change ¬ validCompressedPubKeyBytes invalidCompressedKey.bytes
  native_decide

example : ScriptAllowed .p2wsh (compile legacyMulti) :=
  compile_scriptAllowed (by native_decide)

example : ScriptAllowed .tapscript (compile tapscriptMulti) :=
  compile_scriptAllowed (by native_decide)

/-- The raw compiler can still compile an invalid context/fragment pair, and
the context-safety predicate detects the legacy opcode in Tapscript. -/
example : ¬ ScriptAllowed .tapscript (compile legacyMulti) := by
  native_decide

/-- The converse mismatch detects `OP_CHECKSIGADD` in P2WSH. -/
example : ¬ ScriptAllowed .p2wsh (compile tapscriptMulti) := by
  native_decide

end LeanMiniscript.Miniscript
