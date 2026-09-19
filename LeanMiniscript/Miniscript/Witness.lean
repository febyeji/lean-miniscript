import LeanMiniscript.Bitcoin.Serialization
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

/-- Every serialized witness item respects the Script element-size limit. -/
def ItemsBounded (witness : Witness) : Prop :=
  ∀ item ∈ witness, item.size ≤ maxScriptElementSize

/-- Convert serialized witness order to the top-first stack representation used
    by the operational semantics. -/
def toInitialStack (witness : Witness) : Stack :=
  witness.reverse

/-- Exact wire size of these witness items, including the outer CompactSize
    item count and each item's CompactSize length prefix. -/
def wireSize (witness : Witness) : Nat :=
  (Bitcoin.serializeWitness witness).size

/-- BIP 379 candidate-selection cost. Each item includes its CompactSize length
    prefix, while the outer witness item-count prefix is excluded so sequential
    candidate composition is additive. -/
def candidateCost (witness : Witness) : Nat :=
  (witness.map (fun item => (Bitcoin.serializeByteVector item).size)).sum

/-- Compose witnesses for fragments that execute in the order `first`, then
    `second`. Wire order is the reverse of execution consumption order. -/
def combine (first second : Witness) : Witness :=
  second ++ first

/-- Append an IF selector so it becomes the first item consumed at runtime. -/
def withSelector (witness : Witness) (selector : StackElement) : Witness :=
  witness ++ [selector]

@[simp] theorem candidateCost_append (left right : Witness) :
    candidateCost (left ++ right) = candidateCost left + candidateCost right := by
  simp [candidateCost]

/-- Candidate cost is additive in fragment execution order even though wire
    order stores the second fragment's items first. -/
@[simp] theorem candidateCost_combine (first second : Witness) :
    candidateCost (combine first second) =
      candidateCost first + candidateCost second := by
  simp [combine, Nat.add_comm]

@[simp] theorem toInitialStack_nil :
    toInitialStack [] = [] := by
  rfl

@[simp] theorem toInitialStack_append (left right : Witness) :
    toInitialStack (left ++ right) =
      toInitialStack right ++ toInitialStack left := by
  simp [toInitialStack]

/-- The first fragment's arguments are on top when two wire-order witnesses
    are composed in execution order. -/
@[simp] theorem toInitialStack_combine (first second : Witness) :
    toInitialStack (combine first second) =
      toInitialStack first ++ toInitialStack second := by
  simp [combine]

/-- A branch selector is consumed before the selected fragment's arguments. -/
@[simp] theorem toInitialStack_withSelector
    (witness : Witness) (selector : StackElement) :
    toInitialStack (withSelector witness selector) =
      selector :: toInitialStack witness := by
  simp [withSelector, toInitialStack]

@[simp] theorem combine_nil_left (witness : Witness) :
    combine [] witness = witness := by
  simp [combine]

@[simp] theorem combine_nil_right (witness : Witness) :
    combine witness [] = witness := by
  simp [combine]

theorem combine_assoc (first second third : Witness) :
    combine (combine first second) third =
      combine first (combine second third) := by
  simp [combine, List.append_assoc]

theorem two_items_toInitialStack (bottom top : StackElement) :
    toInitialStack [bottom, top] = [top, bottom] := by
  rfl

namespace ItemsBounded

@[simp] theorem nil : ItemsBounded [] := by
  simp [ItemsBounded]

@[simp] theorem singleton {item : StackElement} :
    ItemsBounded [item] ↔ item.size ≤ maxScriptElementSize := by
  simp [ItemsBounded]

@[simp] theorem append {left right : Witness} :
    ItemsBounded (left ++ right) ↔ ItemsBounded left ∧ ItemsBounded right := by
  constructor
  · intro bounded
    constructor
    · intro item member
      exact bounded item (List.mem_append.mpr (Or.inl member))
    · intro item member
      exact bounded item (List.mem_append.mpr (Or.inr member))
  · rintro ⟨leftBounded, rightBounded⟩ item member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact leftBounded item inLeft
    · exact rightBounded item inRight

theorem combine {first second : Witness}
    (firstBounded : ItemsBounded first)
    (secondBounded : ItemsBounded second) :
    ItemsBounded (Witness.combine first second) := by
  simpa [Witness.combine] using
    (append.mpr ⟨secondBounded, firstBounded⟩)

theorem withSelector {witness : Witness} {selector : StackElement}
    (bounded : ItemsBounded witness)
    (selectorBounded : selector.size ≤ maxScriptElementSize) :
    ItemsBounded (Witness.withSelector witness selector) := by
  simpa [Witness.withSelector] using
    (append.mpr ⟨bounded, singleton.mpr selectorBounded⟩)

/-- A runtime-top item inherits the bound from its serialized witness. -/
theorem runtimeTop {witness : Witness} {top : StackElement} {rest : Stack}
    (bounded : ItemsBounded witness)
    (shape : witness.toInitialStack = top :: rest) :
    top.size ≤ maxScriptElementSize := by
  have runtimeMember : top ∈ witness.toInitialStack := by
    rw [shape]
    simp
  have wireMember : top ∈ witness := by
    simpa [Witness.toInitialStack] using runtimeMember
  exact bounded top wireMember

end ItemsBounded

end Witness

end LeanMiniscript.Miniscript
