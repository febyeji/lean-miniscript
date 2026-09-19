import LeanMiniscript.Properties.ResourceBounds
import LeanMiniscript.Script.RuntimeStackBounds

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

/-- The compiled instruction count also bounds every reachable intermediate
    combined stack, before runtime stack-size checks are applied. -/
theorem compile_prefix_stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : CoreFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compile fragment))
    (budget : before.stack.length + before.altStack.length + scriptElementCount fragment ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBound agreement isPrefix budget

/-- Surface prefix bounds use the instruction count of the desugared core. -/
theorem compileSurface_prefix_stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : SurfaceFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compileSurface fragment))
    (budget : before.stack.length + before.altStack.length +
      scriptElementCount (desugar fragment) ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBound agreement isPrefix budget

/-- The fragment-specific allowance is never weaker than the earlier compiled
    instruction-count allowance. -/
theorem maxStackGrowth_le_scriptElementCount (fragment : CoreFragment) :
    maxStackGrowth fragment ≤ scriptElementCount fragment :=
  stackGrowthAllowance_le_length (compile fragment)

/-- The static fragment allowance bounds every reachable compiled prefix. -/
theorem compile_prefix_maxStackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : CoreFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compile fragment))
    (budget : before.stack.length + before.altStack.length +
      maxStackGrowth fragment ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBoundAllowance agreement isPrefix budget

/-- Surface compilation inherits the fragment-specific allowance through
    desugaring. -/
theorem compileSurface_prefix_maxStackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : SurfaceFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compileSurface fragment))
    (budget : before.stack.length + before.altStack.length +
      maxStackGrowth (desugar fragment) ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBoundAllowance agreement isPrefix budget

end LeanMiniscript.Properties
