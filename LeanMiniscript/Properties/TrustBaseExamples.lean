import LeanMiniscript.Proofs

/-! Headline theorems depend only on Lean's standard axioms. These checks fail
if a proof starts relying on `native_decide`, `sorry`, or a new axiom. -/

open LeanMiniscript.Miniscript LeanMiniscript.Properties

/--
info: 'LeanMiniscript.Miniscript.totalTypeSoundnessSurface' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms totalTypeSoundnessSurface

/--
info: 'LeanMiniscript.Miniscript.compilationPreservesSurfaceSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compilationPreservesSurfaceSemantics

/--
info: 'LeanMiniscript.Miniscript.malleabilityCandidateSound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms malleabilityCandidateSound

/--
info: 'LeanMiniscript.Properties.nonMalleable_iff_infer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms nonMalleable_iff_infer

/--
info: 'LeanMiniscript.Properties.NonMalleable.canonicalWitness_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NonMalleable.canonicalWitness_unique

/--
info: 'LeanMiniscript.Properties.resourceBoundsSound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms resourceBoundsSound
