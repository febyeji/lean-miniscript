import LeanMiniscript.Properties.ResourceBounds
import LeanMiniscript.Script.StackGrowth

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-- Every successfully executed compiled core fragment satisfies the
    conservative combined-stack bound. The general Script theorem makes
    context validity and typing unnecessary for this particular bound. -/
theorem compile_stackGrowth
    {fragment : CoreFragment} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval (compile fragment) stack alt flags ctx (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + scriptElementCount fragment :=
  evaluated.stackGrowth

/-- Discharge the existing resource contract without weakening its statement. -/
theorem resourceBoundsSound : ResourceBoundsSound := by
  intro ctx fragment ty stack alt finalStack finalAlt flags txCtx _ evaluated
  exact compile_stackGrowth evaluated

/-- Surface compilation inherits the core bound through desugaring. -/
theorem compileSurface_stackGrowth
    {fragment : SurfaceFragment} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval (compileSurface fragment) stack alt flags ctx
      (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + scriptElementCount (desugar fragment) :=
  compile_stackGrowth evaluated

end LeanMiniscript.Properties
