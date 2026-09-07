import LeanMiniscript.Miniscript.SatisfactionProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def key : PubKey := ⟨⟨#[2, 3]⟩⟩
private def signature : StackElement := ⟨#[48, 1]⟩

private def unavailableEnv : SatEnv where
  signatureFor := fun _ => none
  preimageFor := fun _ => none
  txCtx := { version := 2, locktime := 100, sequence := 50, sigHash := ⟨#[]⟩ }

private def signingEnv : SatEnv where
  signatureFor := fun _ => some signature
  preimageFor := fun _ => none
  txCtx := unavailableEnv.txCtx

example : satisfy .one unavailableEnv = some [] := by rfl
example : satisfy .zero unavailableEnv = none := by rfl
example : dissatisfy .zero unavailableEnv = some [] := by rfl
example : dissatisfy .one unavailableEnv = none := by rfl

/-- A signature is emitted as one serialized-order witness item. -/
example : satisfy (.c (.pk_k key)) signingEnv = some [signature] := by rfl

example : satisfy (.c (.pk_k key)) unavailableEnv = none := by rfl

/-- The canonical empty signature is selected without consulting availability. -/
example : dissatisfy (.c (.pk_k key)) unavailableEnv = some [falseElement] := by
  rfl

example : satisfy (.older 40) unavailableEnv = some [] := by native_decide
example : satisfy (.older 60) unavailableEnv = none := by native_decide
example : satisfy (.after 90) unavailableEnv = some [] := by native_decide
example : satisfy (.after 110) unavailableEnv = none := by native_decide

/-- Basic scope does not silently claim support for wrappers or connectives. -/
example : satisfy (.n .one) unavailableEnv = none := by rfl
example : dissatisfy (.or_i .zero .one) unavailableEnv = none := by rfl

end LeanMiniscript.Miniscript
