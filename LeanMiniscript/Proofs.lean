import LeanMiniscript
import LeanMiniscript.Script.RuntimeErasure
import LeanMiniscript.Miniscript.TypeInferenceProofs
import LeanMiniscript.Miniscript.MalleabilityInferenceProofs
import LeanMiniscript.Miniscript.Conformance
import LeanMiniscript.Miniscript.Structural
import LeanMiniscript.Miniscript.CompileConcreteProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Miniscript.SurfaceTextProofs
import LeanMiniscript.Properties.ResourceBoundsProofs

/-!
# Proof-oriented lean-miniscript modules

This umbrella exports conformance, structural, inference, surface
normalization, and final stack-growth guarantees without adding their proof
graph to the stable executable facade.
-/
