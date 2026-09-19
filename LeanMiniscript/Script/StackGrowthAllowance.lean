import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-- Conservative increase in combined main/alt-stack size attributable to one
    successfully executed source element. `CHECKMULTISIG` is deliberately
    charged one item here; proving that its decoded frame always shrinks the
    stack is independent of the useful fragment-level bound. -/
def ScriptElement.stackGrowthAllowance : ScriptElement → Nat
  | .pushData _ | .pushNum _ => 1
  | .op .OP_IFDUP | .op .OP_DUP | .op .OP_SIZE | .op .OP_CHECKMULTISIG => 1
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

/-- Every element allowance is at most one, so the refined allowance never
    exceeds the earlier instruction-count allowance. -/
theorem ScriptElement.stackGrowthAllowance_le_one (element : ScriptElement) :
    element.stackGrowthAllowance ≤ 1 := by
  cases element with
  | pushData data => simp [ScriptElement.stackGrowthAllowance]
  | pushNum value => simp [ScriptElement.stackGrowthAllowance]
  | op opcode => cases opcode <;> simp [ScriptElement.stackGrowthAllowance]

theorem stackGrowthAllowance_le_length (script : Script) :
    stackGrowthAllowance script ≤ script.length := by
  induction script with
  | nil => simp [stackGrowthAllowance]
  | cons element rest ih =>
      simp only [stackGrowthAllowance, List.length_cons]
      have elementBound := element.stackGrowthAllowance_le_one
      omega

/-- A source prefix cannot have more growth allowance than the whole script. -/
theorem stackGrowthAllowance_le_of_isPrefix
    {visited script : Script} (isPrefix : visited.IsPrefix script) :
    stackGrowthAllowance visited ≤ stackGrowthAllowance script := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  simp [stackGrowthAllowance_append]

end LeanMiniscript.Script
