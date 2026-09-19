import LeanMiniscript
import LeanMiniscript.Script.RuntimeErasure
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.TypeInferenceProofs
import LeanMiniscript.Miniscript.MalleabilityInferenceProofs
import LeanMiniscript.Miniscript.Conformance
import LeanMiniscript.Miniscript.Structural
import LeanMiniscript.Miniscript.CompileConcreteProofs
import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Miniscript.SurfaceTextProofs
import LeanMiniscript.Properties.ResourceBoundsProofs

/-!
# Proof-oriented lean-miniscript modules

This umbrella exports conformance, structural, inference, surface
normalization, stack-growth, and runtime prefix-bound guarantees without adding
their proof graph to the stable executable facade.
-/
