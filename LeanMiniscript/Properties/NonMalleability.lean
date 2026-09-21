import LeanMiniscript.Miniscript.MalleabilityInferenceProofs
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-!
# Non-malleable candidate selection

BIP 379's malleability type is a property of a fragment under the global
no-duplicate-keys assumption. Witness canonicality is kept separate: it says
that the deterministic satisfaction algorithm selected a usable canonical
table row. This distinction matters for signatures, because two signers may
produce different valid low-S signatures even though neither signature is
third-party malleable.
-/

/-- A fragment satisfies the complete BIP 379 non-malleability judgment in a
    script context. The local recursive rules and the global key-uniqueness
    premise are both part of the contract. -/
def NonMalleable (ctx : ScriptContext) (fragment : CoreFragment) : Prop :=
  fragment.NoDuplicateKeys ∧
    ∃ modifiers,
      HasMalleability ctx fragment modifiers ∧
      modifiers.nonMalleable = true

/-- A witness is the usable candidate selected from a canonical BIP 379 table
    row. Signature byte canonicality is supplied separately by
    `SatEnv.EncodingSound`; selectors and the legacy multisig dummy are fixed by
    the candidate constructors themselves. -/
def CanonicalSatisfaction (fragment : CoreFragment) (env : SatEnv)
    (witness : Witness) : Prop :=
  ∃ candidate,
    (satisfactionCandidates fragment env).sat = .candidate candidate ∧
    candidate.status = .usable ∧
    candidate.origin = .canonical ∧
    candidate.witness = witness

/-- A canonical candidate is exactly the ordinary public satisfaction
    projection together with canonical-origin evidence. -/
theorem canonicalSatisfaction_iff
    {fragment : CoreFragment} {env : SatEnv} {witness : Witness} :
    CanonicalSatisfaction fragment env witness ↔
      satisfy fragment env = some witness ∧
      ∃ candidate,
        (satisfactionCandidates fragment env).sat = .candidate candidate ∧
        candidate.origin = .canonical := by
  constructor
  · rintro ⟨candidate, selected, usable, canonical, rfl⟩
    constructor
    · simp [satisfy, selected, CandidateResult.usableWitness?, usable]
    · exact ⟨candidate, selected, canonical⟩
  · rintro ⟨selectedWitness, candidate, selected, canonical⟩
    rw [satisfy, selected] at selectedWitness
    cases statusEq : candidate.status with
    | dontUse =>
        simp [CandidateResult.usableWitness?, statusEq] at selectedWitness
    | usable =>
        simp [CandidateResult.usableWitness?, statusEq] at selectedWitness
        cases selectedWitness
        exact ⟨candidate, selected, statusEq, canonical, rfl⟩

/-- Deterministic candidate selection produces at most one canonical witness
    for a fixed fragment and satisfaction environment. -/
theorem CanonicalSatisfaction.unique
    {fragment : CoreFragment} {env : SatEnv} {first second : Witness}
    (firstCanonical : CanonicalSatisfaction fragment env first)
    (secondCanonical : CanonicalSatisfaction fragment env second) :
    first = second := by
  have firstSelected := (canonicalSatisfaction_iff.mp firstCanonical).1
  have secondSelected := (canonicalSatisfaction_iff.mp secondCanonical).1
  rw [firstSelected] at secondSelected
  exact Option.some.inj secondSelected

/-- The executable inference result characterizes the non-malleability
    property, including the no-duplicate-keys boundary. -/
theorem nonMalleable_iff_infer
    {ctx : ScriptContext} {fragment : CoreFragment} :
    NonMalleable ctx fragment ↔
      ∃ modifiers,
        inferMalleability ctx fragment = some modifiers ∧
        modifiers.nonMalleable = true := by
  constructor
  · rintro ⟨unique, modifiers, typed, nonMalleable⟩
    exact ⟨modifiers,
      inferMalleability_complete unique typed, nonMalleable⟩
  · rintro ⟨modifiers, inferred, nonMalleable⟩
    exact ⟨inferMalleability_noDuplicateKeys inferred, modifiers,
      inferMalleability_sound inferred, nonMalleable⟩

/-- For a BIP 379 non-malleable fragment, two canonical selections made from
    the same material environment coincide. -/
theorem NonMalleable.canonicalWitness_unique
    {ctx : ScriptContext} {fragment : CoreFragment} {env : SatEnv}
    {first second : Witness}
    (_nonMalleable : NonMalleable ctx fragment)
    (firstCanonical : CanonicalSatisfaction fragment env first)
    (secondCanonical : CanonicalSatisfaction fragment env second) :
    first = second :=
  firstCanonical.unique secondCanonical

/-- Surface Miniscript inherits the core non-malleability judgment through
    the unique desugaring boundary. -/
def SurfaceNonMalleable (ctx : ScriptContext)
    (fragment : SurfaceFragment) : Prop :=
  NonMalleable ctx (desugar fragment)

/-- Surface canonical-witness uniqueness is the core theorem after desugaring. -/
theorem SurfaceNonMalleable.canonicalWitness_unique
    {ctx : ScriptContext} {fragment : SurfaceFragment} {env : SatEnv}
    {first second : Witness}
    (nonMalleable : SurfaceNonMalleable ctx fragment)
    (firstCanonical : CanonicalSatisfaction (desugar fragment) env first)
    (secondCanonical : CanonicalSatisfaction (desugar fragment) env second) :
    first = second :=
  NonMalleable.canonicalWitness_unique nonMalleable
    firstCanonical secondCanonical

end LeanMiniscript.Properties
