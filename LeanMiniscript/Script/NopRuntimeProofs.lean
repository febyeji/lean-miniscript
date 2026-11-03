import LeanMiniscript.Script.RuntimeLimitsProofs

namespace LeanMiniscript.Script

/-- Upgradeable NOPs retain the complete state unless active policy rejects them. -/
theorem executeRuntimeElement_upgradeableNop (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true) :
    executeRuntimeElement oracle (.op opcode) state flags ctx =
      if state.conditions.all id && flags.discourageUpgradableNops then
        .error .discourageUpgradableNops
      else .ok state := by
  cases opcode <;> simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]
  all_goals
    cases active : state.conditions.all id <;>
      cases discouraged : flags.discourageUpgradableNops <;>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, discouraged, prepareValidationWeight, evaluate] <;> rfl

/-- The upgradeable-NOP policy error precedes the combined stack limit. -/
theorem runtimeInstruction_upgradeableNop (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true) :
    runtimeInstruction oracle (.op opcode) state flags ctx =
      if state.conditions.all id && flags.discourageUpgradableNops then
        .error .discourageUpgradableNops
      else checkRuntimeStack state := by
  rw [runtimeInstruction, executeRuntimeElement_upgradeableNop oracle opcode state flags ctx upgradeable]
  split <;> rfl

/-- Active discouraged NOPs fail for every stack, including an oversized stack. -/
theorem runtimeInstruction_upgradeableNop_discouraged (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (active : state.conditions.all id = true)
    (discouraged : flags.discourageUpgradableNops = true) :
    runtimeInstruction oracle (.op opcode) state flags ctx = .error .discourageUpgradableNops := by
  simp [runtimeInstruction_upgradeableNop oracle opcode state flags ctx upgradeable, active, discouraged]

/-- Permitted upgradeable NOPs perform the stack-cap check on the unchanged state. -/
theorem runtimeInstruction_upgradeableNop_allowed (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) :
    runtimeInstruction oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  simp [runtimeInstruction_upgradeableNop oracle opcode state flags ctx upgradeable, allowed]

/-- Inactive upgradeable NOPs skip policy rejection and retain the shared stack-cap check. -/
theorem runtimeInstruction_upgradeableNop_inactive (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (inactive : state.conditions.all id = false) :
    runtimeInstruction oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  simp [runtimeInstruction_upgradeableNop oracle opcode state flags ctx upgradeable, inactive]

/-- Every successful upgradeable NOP preserves both stacks, conditions, and weight exactly. -/
theorem executeRuntimeElement_upgradeableNop_preserves (oracle : CryptoOracle) (opcode : Opcode)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (executed : executeRuntimeElement oracle (.op opcode) state flags ctx = .ok next) :
    next = state := by
  rw [executeRuntimeElement_upgradeableNop oracle opcode state flags ctx upgradeable] at executed
  split at executed
  · contradiction
  · cases executed
    rfl

/-- After the operation charge, a successful upgradeable NOP preserves the complete state. -/
theorem runtimeInstruction_upgradeableNop_preserves (oracle : CryptoOracle) (opcode : Opcode)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (stepped : runtimeInstruction oracle (.op opcode) state flags ctx = .ok next) :
    next = state := by
  rw [runtimeInstruction_upgradeableNop oracle opcode state flags ctx upgradeable] at stepped
  split at stepped
  · contradiction
  · exact (checkRuntimeStack_ok stepped).1

/-- RETURN fails in active code and retains the complete state in inactive code. -/
theorem executeRuntimeElement_opReturn (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    executeRuntimeElement oracle (.op .OP_RETURN) state flags ctx =
      if state.conditions.all id then .error .opReturn else .ok state := by
  cases active : state.conditions.all id <;>
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate] <;> rfl

/-- Active RETURN fails before the stack-cap check; inactive RETURN performs that check. -/
theorem runtimeInstruction_opReturn (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    runtimeInstruction oracle (.op .OP_RETURN) state flags ctx =
      if state.conditions.all id then .error .opReturn else checkRuntimeStack state := by
  rw [runtimeInstruction, executeRuntimeElement_opReturn oracle state flags ctx]
  split <;> rfl

/-- Active RETURN's error takes precedence for every stack size. -/
theorem runtimeInstruction_opReturn_active (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_RETURN) state flags ctx = .error .opReturn := by
  simp [runtimeInstruction_opReturn, active]

/-- Inactive RETURN retains the shared stack-cap check. -/
theorem runtimeInstruction_opReturn_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeInstruction oracle (.op .OP_RETURN) state flags ctx = checkRuntimeStack state := by
  simp [runtimeInstruction_opReturn, inactive]

/-- After the operation charge, a successful RETURN was inactive and preserves every
    runtime field. -/
theorem runtimeInstruction_opReturn_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeInstruction oracle (.op .OP_RETURN) state flags ctx = .ok next) :
    state.conditions.all id = false ∧ next = state := by
  rw [runtimeInstruction_opReturn] at stepped
  cases active : state.conditions.all id with
  | false =>
      simp only [active, Bool.false_eq_true, ↓reduceIte] at stepped
      exact ⟨rfl, (checkRuntimeStack_ok stepped).1⟩
  | true => simp [active] at stepped

end LeanMiniscript.Script
