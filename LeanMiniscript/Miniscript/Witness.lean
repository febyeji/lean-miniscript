import LeanMiniscript.Script.State

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Witness ordering

Bitcoin serializes witness items from the bottom of the initial stack to the
top. `Script.Stack`, like the rest of this Lean model, stores the current stack
top at the head of the list. Crossing the witness/execution boundary therefore
requires one explicit reversal.
-/

/-- Witness items in serialized order: the first item is the bottom of the
    initial Script stack and the last item is the first item consumed. -/
abbrev Witness := List StackElement

namespace Witness

/-- Convert serialized witness order to the top-first stack representation used
    by the operational semantics. -/
def toInitialStack (witness : Witness) : Stack :=
  witness.reverse

theorem two_items_toInitialStack (bottom top : StackElement) :
    toInitialStack [bottom, top] = [top, bottom] := by
  rfl

end Witness

end LeanMiniscript.Miniscript
