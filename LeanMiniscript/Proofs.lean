import LeanMiniscript
import LeanMiniscript.Script.RuntimeErasure
import LeanMiniscript.Script.ExecutionResources
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Script.Codec.Proofs
import LeanMiniscript.Miniscript.TypeInferenceProofs
import LeanMiniscript.Miniscript.MalleabilityInferenceProofs
import LeanMiniscript.Miniscript.Conformance
import LeanMiniscript.Miniscript.Structural
import LeanMiniscript.Miniscript.CompileConcreteProofs
import LeanMiniscript.Miniscript.CompileVerifyResourceProofs
import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs
import LeanMiniscript.Miniscript.SatisfactionCorrectnessProofs
import LeanMiniscript.Miniscript.SurfaceTextProofs
import LeanMiniscript.Properties.ResourceBoundsProofs
import LeanMiniscript.Properties.ResourceCompilerMetricProofs
import LeanMiniscript.Properties.ResourcePathProofs
import LeanMiniscript.Properties.SaneExecutionResourceProofs
import LeanMiniscript.Properties.SatisfactionExecutionResourceProofs
import LeanMiniscript.Properties.NonMalleability

/-!
# Proof-oriented lean-miniscript modules

This umbrella exports canonical Script codec round trips, conformance,
structural, inference, surface normalization, generated-satisfaction contracts,
Core/Surface satisfaction and dissatisfaction correctness, stack-growth,
active-path Script resource observations, terminal VERIFY fusion resource
preservation, and runtime prefix-bound guarantees without adding their proof
graph to the stable executable facade. Generated final satisfactions also
expose one concrete resource observation bounded by the jointly selected stack
and dynamic paths, including the context-specific limits certified by sane
fragments.
-/
