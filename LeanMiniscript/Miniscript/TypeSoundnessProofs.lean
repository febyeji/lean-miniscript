import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

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

/-- Core type soundness covers every B, V, K, and W correctness type. -/
def TypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    MiniTypeGuarantee ctx m ty

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

/-!
TODO(theorem): prove `BaseTypeGuarantee` by induction over `HasType`, prove
`UnconditionalDissatisfaction` whenever the derived type has `d`, and combine
those results with `generatedTypeSoundnessCore` to close `TypeSoundnessCore`.
-/

end LeanMiniscript.Miniscript
