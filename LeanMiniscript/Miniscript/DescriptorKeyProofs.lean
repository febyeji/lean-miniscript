import LeanMiniscript.Miniscript.DescriptorKey
import LeanMiniscript.Miniscript.SurfaceParserProofs

namespace LeanMiniscript.Miniscript

/-- Descriptor resolution preserves the surface parser's context/type guarantee. -/
theorem wellFormed_and_hasType_of_parseSurfaceDescriptor_eq_ok
    (context : ScriptContext) (input : String) (wildcardIndex : Option Nat)
    (fragment : SurfaceFragment)
    (h : parseSurfaceDescriptor context input wildcardIndex = .ok fragment) :
    fragment.WellFormed context ∧ ∃ ty, HasType context (desugar fragment) ty := by
  unfold parseSurfaceDescriptor at h
  cases hParsed : parseSurface context (resolveDescriptorKey wildcardIndex) input with
  | error error => simp [hParsed] at h
  | ok parsed =>
      simp [hParsed] at h
      subst fragment
      exact wellFormed_and_hasType_of_parseSurface_eq_ok context
        (resolveDescriptorKey wildcardIndex) input parsed hParsed

end LeanMiniscript.Miniscript
