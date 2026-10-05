import LeanMiniscript.Script.RuntimeLimits

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
theorem runtimeStep_upgradeableNop (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true) :
    runtimeStep oracle (.op opcode) state flags ctx =
      if state.conditions.all id && flags.discourageUpgradableNops then
        .error .discourageUpgradableNops
      else checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_upgradeableNop oracle opcode state flags ctx upgradeable]
  split <;> rfl

/-- Active discouraged NOPs fail for every stack, including an oversized stack. -/
theorem runtimeStep_upgradeableNop_discouraged (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (active : state.conditions.all id = true)
    (discouraged : flags.discourageUpgradableNops = true) :
    runtimeStep oracle (.op opcode) state flags ctx = .error .discourageUpgradableNops := by
  simp [runtimeStep_upgradeableNop oracle opcode state flags ctx upgradeable, active, discouraged]

/-- Permitted upgradeable NOPs perform the stack-cap check on the unchanged state. -/
theorem runtimeStep_upgradeableNop_allowed (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) :
    runtimeStep oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  simp [runtimeStep_upgradeableNop oracle opcode state flags ctx upgradeable, allowed]

/-- Inactive upgradeable NOPs skip policy rejection and retain the shared stack-cap check. -/
theorem runtimeStep_upgradeableNop_inactive (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  simp [runtimeStep_upgradeableNop oracle opcode state flags ctx upgradeable, inactive]

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

/-- Successful upgradeable NOP runtime steps preserve the complete state. -/
theorem runtimeStep_upgradeableNop_preserves (oracle : CryptoOracle) (opcode : Opcode)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (stepped : runtimeStep oracle (.op opcode) state flags ctx = .ok next) :
    next = state := by
  rw [runtimeStep_upgradeableNop oracle opcode state flags ctx upgradeable] at stepped
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
theorem runtimeStep_opReturn (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (.op .OP_RETURN) state flags ctx =
      if state.conditions.all id then .error .opReturn else checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_opReturn oracle state flags ctx]
  split <;> rfl

/-- Active RETURN's error takes precedence for every stack size. -/
theorem runtimeStep_opReturn_active (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_RETURN) state flags ctx = .error .opReturn := by
  simp [runtimeStep_opReturn, active]

/-- Inactive RETURN retains the shared stack-cap check. -/
theorem runtimeStep_opReturn_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_RETURN) state flags ctx = checkRuntimeStack state := by
  simp [runtimeStep_opReturn, inactive]

/-- A successful RETURN step was inactive and preserves every runtime field. -/
theorem runtimeStep_opReturn_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_RETURN) state flags ctx = .ok next) :
    state.conditions.all id = false ∧ next = state := by
  rw [runtimeStep_opReturn] at stepped
  cases active : state.conditions.all id with
  | false =>
      simp only [active, Bool.false_eq_true, ↓reduceIte] at stepped
      exact ⟨rfl, (checkRuntimeStack_ok stepped).1⟩
  | true => simp [active] at stepped

end LeanMiniscript.Script
