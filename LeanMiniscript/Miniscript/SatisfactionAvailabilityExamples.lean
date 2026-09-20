import LeanMiniscript.Miniscript.SatisfactionAvailability

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def fixtureKey : PubKey :=
  PubKey.ofBytes ⟨#[2] ++ (List.replicate 32 17).toArray⟩

private def fixtureSignature : StackElement := trueElement

private def noMaterialEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  nonPreimageFor := fun _ => ⟨(List.replicate 32 34).toArray⟩
  txCtx := { version := 2, locktime := 100, sequence := 50, sigHash := ⟨#[]⟩ }

private def signatureEnv : SatEnv where
  signatureFor := fun _ => some fixtureSignature
  preimageFor := fun _ => none
  nonPreimageFor := noMaterialEnv.nonPreimageFor
  txCtx := noMaterialEnv.txCtx

private def matureEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  nonPreimageFor := noMaterialEnv.nonPreimageFor
  txCtx := { noMaterialEnv.txCtx with sequence := 60 }

private def availabilityOfRaw (ctx : ScriptContext)
    (fragment : CoreFragment) (env : SatEnv) : Option SatisfactionAvailability :=
  (CheckedFragment.ofRaw? ctx fragment).map
    (fun checked => checked.satisfactionAvailability env)

example : availabilityOfRaw .p2wsh .zero noMaterialEnv = some .no := by
  native_decide

example : availabilityOfRaw .p2wsh
    (.c (.pk_k fixtureKey)) noMaterialEnv = some .maybe := by
  native_decide

example : availabilityOfRaw .p2wsh
    (.c (.pk_k fixtureKey)) signatureEnv = some .yes := by
  native_decide

example : availabilityOfRaw .p2wsh (.older 60) noMaterialEnv = some .maybe := by
  native_decide

example : availabilityOfRaw .p2wsh (.older 60) matureEnv = some .yes := by
  native_decide

/-- Candidate presence is independent of the recursive DONTUSE projection. -/
example :
    availabilityOfRaw .p2wsh (.or_i .one .one) noMaterialEnv = some .yes ∧
      satisfy (.or_i .one .one) noMaterialEnv = none := by
  exact ⟨by native_decide, rfl⟩

/-- Candidate presence is also independent of the final HASSIG projection. -/
example :
    availabilityOfRaw .p2wsh .one noMaterialEnv = some .yes ∧
      satisfyFinal .one noMaterialEnv = none := by
  exact ⟨by native_decide, rfl⟩

end LeanMiniscript.Miniscript
