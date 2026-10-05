import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-- Conservative increase in combined main/alt-stack size attributable to one
    successfully executed source element. The `CHECKMULTISIG` variants are
    deliberately charged one item here; proving that their decoded frame
    always shrinks the stack is independent of the useful fragment-level
    bound. -/
def ScriptElement.stackGrowthAllowance : ScriptElement → Nat
  | .op .OP_2DUP | .op .OP_2OVER => 2
  | .op .OP_3DUP => 3
  | .pushData _ | .pushNum _ => 1
  | .op .OP_IFDUP | .op .OP_DEPTH | .op .OP_DUP | .op .OP_OVER | .op .OP_TUCK | .op .OP_SIZE |
      .op .OP_CHECKMULTISIG | .op .OP_CHECKMULTISIGVERIFY => 1
  | .op _ => 0

/-- Sum of per-element combined-stack growth allowances. This is a static
    source bound: inactive conditional branches are still charged. -/
def stackGrowthAllowance : Script → Nat
  | [] => 0
  | element :: rest => element.stackGrowthAllowance + stackGrowthAllowance rest

@[simp]
theorem stackGrowthAllowance_append (left right : Script) :
    stackGrowthAllowance (left ++ right) =
      stackGrowthAllowance left + stackGrowthAllowance right := by
  induction left with
  | nil => simp [stackGrowthAllowance]
  | cons element rest ih => simp [stackGrowthAllowance, ih, Nat.add_assoc]

/-- The instruction-count bound applies when every source element is charged
    at most one stack item. OP_2DUP, OP_2OVER and OP_3DUP require the general
    weighted bound. -/
def OneItemGrowth (script : Script) : Prop :=
  ∀ element ∈ script, element.stackGrowthAllowance ≤ 1

@[simp]
theorem oneItemGrowth_nil : OneItemGrowth [] := by simp [OneItemGrowth]

@[simp]
theorem oneItemGrowth_cons (element : ScriptElement) (script : Script) :
    OneItemGrowth (element :: script) ↔
      element.stackGrowthAllowance ≤ 1 ∧ OneItemGrowth script := by
  simp [OneItemGrowth]

@[simp]
theorem oneItemGrowth_append (left right : Script) :
    OneItemGrowth (left ++ right) ↔ OneItemGrowth left ∧ OneItemGrowth right := by
  simp [OneItemGrowth, List.mem_append, or_imp, forall_and]

/-- All modeled elements except 2DUP, 2OVER and 3DUP have a one-item allowance. -/
theorem ScriptElement.stackGrowthAllowance_le_one (element : ScriptElement)
    (notTwoDup : element ≠ .op .OP_2DUP)
    (notTwoOver : element ≠ .op .OP_2OVER)
    (notThreeDup : element ≠ .op .OP_3DUP) :
    element.stackGrowthAllowance ≤ 1 := by
  cases element with
  | pushData data => simp [ScriptElement.stackGrowthAllowance]
  | pushNum value => simp [ScriptElement.stackGrowthAllowance]
  | op opcode => cases opcode <;> simp_all [ScriptElement.stackGrowthAllowance]

theorem stackGrowthAllowance_le_length (script : Script) (oneItem : OneItemGrowth script) :
    stackGrowthAllowance script ≤ script.length := by
  induction script with
  | nil => simp [stackGrowthAllowance]
  | cons element rest ih =>
      obtain ⟨head, tail⟩ := (oneItemGrowth_cons element rest).mp oneItem
      have tailBound := ih tail
      simp only [stackGrowthAllowance, List.length_cons]
      omega

/-- A source prefix cannot have more growth allowance than the whole script. -/
theorem stackGrowthAllowance_le_of_isPrefix
    {visited script : Script} (isPrefix : visited.IsPrefix script) :
    stackGrowthAllowance visited ≤ stackGrowthAllowance script := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  simp [stackGrowthAllowance_append]

end LeanMiniscript.Script
