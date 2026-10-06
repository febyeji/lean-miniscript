import LeanMiniscript
import LeanMiniscript.Script.BigStep
import LeanMiniscript.Script.Equivalence
import LeanMiniscript.Script.Evaluator
import LeanMiniscript.Script.SmallStep
import LeanMiniscript.Script.ValidationWeight
import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.Witness
import LeanMiniscript.Properties.NonMalleability
import LeanMiniscript.Properties.ResourceBounds
import LeanMiniscript.Extraction.BitcoinCoreFixtures
import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Extraction.Taproot
import LeanMiniscript.Extraction.TaprootBytes

/-!
# Experimental lean-miniscript modules

This umbrella contains partial semantics, theorem targets, and executable
components whose interfaces are still expected to change. Stable consumers
should import `LeanMiniscript` instead.
-/
