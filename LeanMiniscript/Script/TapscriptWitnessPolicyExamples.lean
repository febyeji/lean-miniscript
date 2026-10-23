import LeanMiniscript.Script.TapscriptWitnessPolicy

namespace LeanMiniscript.Script

private def bytes (size : Nat) : ByteArray :=
  ⟨Array.replicate size 1⟩

private def longControl : ByteArray :=
  ⟨#[0xc0] ++ Array.replicate 96 1⟩

private def witness (arguments : List ByteArray) : TapscriptWitness :=
  { arguments
    scriptBytes := ByteArray.empty
    controlBlock := ByteArray.empty }

/-! The 80-byte relay-policy boundary is inclusive. -/

example : checkTapscriptWitnessPolicy (witness [bytes 80]) = .ok () := by
  native_decide

example : checkTapscriptWitnessPolicy (witness [bytes 81]) =
    .error .stackItemTooLarge := by
  native_decide

/-! Consensus accepts the 520-byte element boundary, while relay policy
rejects the same executable argument. -/

example :
    checkTapscriptInitialStack [bytes 520] = .ok () ∧
      checkTapscriptWitnessPolicy (witness [bytes 520]) =
        .error .stackItemTooLarge := by
  native_decide

/-! Tapscript and control-block bytes are parsed metadata, so their sizes do
not participate in the executable-argument policy check. -/

example : checkTapscriptWitnessPolicy
    { arguments := [bytes 80]
      scriptBytes := bytes 521
      controlBlock := longControl } = .ok () := by
  native_decide

/-! Relay policy imposes no argument-count limit. Consensus independently
rejects 1001 otherwise-standard initial stack arguments. -/

example :
    checkTapscriptWitnessPolicy
        (witness (List.replicate 1001 trueElement)) = .ok () ∧
      checkTapscriptInitialStack (List.replicate 1001 trueElement) =
        .error .stackSize := by
  native_decide

end LeanMiniscript.Script
