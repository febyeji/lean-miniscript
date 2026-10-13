import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.ExecutionDecomposition
import LeanMiniscript.Miniscript.TypeSoundnessProofs.Dissatisfaction
import LeanMiniscript.Miniscript.TypeSoundnessProofs.BaseFrames
import LeanMiniscript.Miniscript.TypeSoundnessProofs.SuccessShapes
import LeanMiniscript.Miniscript.TypeSoundnessProofs.BaseType

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type-soundness proof target

The semantic contract keeps arbitrary-input stack safety, generated-witness
correctness, and unconditional dissatisfaction availability as separate proof
obligations. This module is proof-only so the stable executable facade does not
import the recursive generated-contract development.
-/

/-- The generated-witness part of type soundness. `GeneratedContract` gives
    B/V/K/W execution semantics, bounded witnesses, the exact `z`/`o` input
    counts, the satisfying-input `n` condition, and canonical `u` results. -/
def GeneratedTypeGuarantee (scriptCtx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop :=
  ∀ (env : SatEnv) (flags : ScriptFlags),
    ModeledContextVersion scriptCtx env.txCtx →
    ModeledContextFlags scriptCtx flags →
    env.Sound →
    env.EncodingSound flags →
    (satisfactionCandidates m env).SupportsGeneratedContract
      scriptCtx m ty flags env.txCtx

/-- Combined semantic proof target for a correctness type. -/
structure MiniTypeGuarantee (scriptCtx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop where
  base : BaseTypeGuarantee m ty.base
  generated : GeneratedTypeGuarantee scriptCtx m ty
  dissatisfiable : ty.mods.d = true → UnconditionalDissatisfaction m

/-- Generated-witness soundness for every valid core type. -/
def GeneratedTypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    GeneratedTypeGuarantee ctx m ty

/-- Every valid core fragment satisfies the generated-witness contract for its
    complete type. -/
theorem generatedTypeSoundnessCore : GeneratedTypeSoundnessCore := by
  intro ctx m ty valid env flags version modeled sound encodings
  exact supportsGeneratedContract_of_wellFormed_hasType version modeled sound
    encodings valid.hasType valid.wellFormed

/-- Surface generated-witness soundness is inherited through desugaring. -/
def GeneratedTypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    GeneratedTypeGuarantee ctx (desugar m) ty

/-- Desugaring transports the core generated-witness theorem without an
    additional surface proof. -/
theorem generatedTypeSoundnessSurface : GeneratedTypeSoundnessSurface := by
  intro ctx m ty valid
  exact generatedTypeSoundnessCore valid


/-- Correctness typing implies the public arbitrary-input base contract. -/
theorem baseTypeGuarantee_of_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx) :
    BaseTypeGuarantee fragment ty.base := by
  intro stack altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      obtain ⟨altEq, effect⟩ :=
        refinedBaseTypeGuarantee_of_hasType typed wellFormed stack altStack
          flags ctx (.success finalStack finalAltStack) evaluated
      exact ⟨altEq, effect.toBase⟩

/-- The remaining arbitrary-input part of core type soundness. -/
def BaseTypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    BaseTypeGuarantee m ty.base

/-- Core type soundness covers every B, V, K, and W correctness type. -/
def TypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    MiniTypeGuarantee ctx m ty

/-- Arbitrary-input base soundness now suffices for the complete core contract;
    generated-witness correctness and `d` completeness are discharged here. -/
theorem typeSoundnessCore_of_base
    (baseSound : BaseTypeSoundnessCore) : TypeSoundnessCore := by
  intro ctx m ty valid
  exact {
    base := baseSound valid
    generated := generatedTypeSoundnessCore valid
    dissatisfiable := fun enabled =>
      unconditionalDissatisfaction_of_wellFormed_hasType
        valid.hasType valid.wellFormed enabled
  }

/-- Surface type soundness is the same contract after core desugaring. -/
def TypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    MiniTypeGuarantee ctx (desugar m) ty

/-- Any proof of the core theorem immediately supplies the surface theorem. -/
theorem typeSoundnessSurface_of_core
    (sound : TypeSoundnessCore) : TypeSoundnessSurface := by
  intro ctx m ty valid
  exact sound valid

/-- Every valid, correctly typed core fragment satisfies its arbitrary-input
    B/V/K/W stack-frame contract. -/
theorem baseTypeSoundnessCore : BaseTypeSoundnessCore := by
  intro ctx m ty valid
  exact baseTypeGuarantee_of_hasType valid.hasType valid.wellFormed

/-- Complete correctness type soundness for core Miniscript fragments. -/
theorem typeSoundnessCore : TypeSoundnessCore :=
  typeSoundnessCore_of_base baseTypeSoundnessCore

/-- Complete correctness type soundness for surface Miniscript fragments after
    desugaring. -/
theorem typeSoundnessSurface : TypeSoundnessSurface :=
  typeSoundnessSurface_of_core typeSoundnessCore

/-- Total core type soundness: the complete type contract together with a
    unique, terminating outcome for every input state. -/
def TotalTypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    TotalBaseTypeGuarantee m ty.base ∧ MiniTypeGuarantee ctx m ty

/-- Total surface type soundness after core desugaring. -/
def TotalTypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    TotalBaseTypeGuarantee (desugar m) ty.base ∧
      MiniTypeGuarantee ctx (desugar m) ty

/-- Every valid, correctly typed core fragment has exactly one outcome on every
    input state and satisfies its complete type contract. -/
theorem totalTypeSoundnessCore : TotalTypeSoundnessCore := by
  intro ctx m ty valid
  have guarantee := typeSoundnessCore valid
  exact ⟨guarantee.base.total, guarantee⟩

/-- Total type soundness for surface Miniscript fragments after desugaring. -/
theorem totalTypeSoundnessSurface : TotalTypeSoundnessSurface := by
  intro ctx m ty valid
  exact totalTypeSoundnessCore valid

end LeanMiniscript.Miniscript
