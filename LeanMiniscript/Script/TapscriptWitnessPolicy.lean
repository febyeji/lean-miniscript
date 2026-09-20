import LeanMiniscript.Script.ValidationWeight

namespace LeanMiniscript.Script

/-!
# Tapscript witness relay policy

This module models the extra standardness checks applied to a parsed
Tapscript script-path witness. Consensus validation remains in
`ValidationWeight`: it accepts annexes and permits initial stack elements up
to `maxScriptElementSize` bytes.

The policy checker receives `TapscriptWitness`, whose `arguments` field has
already excluded the tapscript, control block, and optional annex. It therefore
checks only executable stack arguments. The caller must already have classified
the script path as leaf version `0xc0`; this is not a whole-transaction
`IsWitnessStandard` replacement or a raw-witness parser.
-/

/-- Maximum byte length of a standard Tapscript stack argument. -/
def maxStandardTapscriptStackItemSize : Nat := 80

/-- Relay-policy failures specific to a parsed Tapscript script-path witness. -/
inductive TapscriptWitnessPolicyError where
  | annexPresent
  | stackItemTooLarge
  deriving Repr, DecidableEq, BEq

/-- Declarative standardness predicate for a parsed Tapscript script-path
    witness. The tapscript and control block are metadata fields and do not
    participate in the element-size check. -/
def TapscriptWitnessStandard (witness : TapscriptWitness) : Prop :=
  witness.annex = none ∧
    ∀ item ∈ witness.arguments, item.size ≤ maxStandardTapscriptStackItemSize

instance (witness : TapscriptWitness) :
    Decidable (TapscriptWitnessStandard witness) := by
  unfold TapscriptWitnessStandard
  infer_instance

/-- Check relay policy for a parsed leaf-version-`0xc0` Tapscript script-path
    witness. Annex rejection has deterministic precedence over an oversized
    stack argument. -/
def checkTapscriptWitnessPolicy (witness : TapscriptWitness) :
    Except TapscriptWitnessPolicyError Unit :=
  match witness.annex with
  | some _ => .error .annexPresent
  | none =>
      if witness.arguments.any
          (fun item => item.size > maxStandardTapscriptStackItemSize) then
        .error .stackItemTooLarge
      else
        .ok ()

/-- The executable checker accepts exactly the declarative standardness
    predicate. -/
theorem checkTapscriptWitnessPolicy_ok_iff (witness : TapscriptWitness) :
    checkTapscriptWitnessPolicy witness = .ok () ↔
      TapscriptWitnessStandard witness := by
  cases annexEq : witness.annex with
  | none => simp [checkTapscriptWitnessPolicy, TapscriptWitnessStandard,
      annexEq, List.any_eq_true, Nat.not_lt]
  | some annex => simp [checkTapscriptWitnessPolicy,
      TapscriptWitnessStandard, annexEq]

/-- Any present annex is rejected before stack-argument sizes are inspected. -/
@[simp] theorem checkTapscriptWitnessPolicy_annex
    (witness : TapscriptWitness) (annex : ByteArray)
    (present : witness.annex = some annex) :
    checkTapscriptWitnessPolicy witness = .error .annexPresent := by
  simp [checkTapscriptWitnessPolicy, present]

/-- The 80-byte policy limit is stricter than the 520-byte consensus element
    limit used by Tapscript execution. -/
theorem TapscriptWitnessStandard.consensusElementSize
    {witness : TapscriptWitness}
    (standard : TapscriptWitnessStandard witness) :
    ∀ item ∈ witness.arguments, item.size ≤ maxScriptElementSize := by
  intro item member
  have policyBound := standard.2 item member
  unfold maxStandardTapscriptStackItemSize at policyBound
  unfold maxScriptElementSize
  omega

end LeanMiniscript.Script
