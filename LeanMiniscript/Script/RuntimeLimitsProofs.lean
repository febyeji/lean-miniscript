import LeanMiniscript.Script.RuntimeLimits
import LeanMiniscript.Script.ValidationWeightProofs

/-! Opcode preservation, runtime bounds and agreement with the abstract model. -/

namespace LeanMiniscript.Script

theorem checkRuntimeStack_ok {before after : RuntimeState}
    (checked : checkRuntimeStack before = .ok after) :
    after = before ∧ after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold checkRuntimeStack at checked
  split at checked
  · contradiction
  · cases checked
    exact ⟨rfl, by omega⟩

/-- Tapscript has no operation limit. -/
theorem chargeOperations_tapscript (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) {ctx : TxContext} (version : ctx.sigVersion = .tapscript) :
    chargeOperations element state flags ctx = .ok state := by
  cases element <;> simp [chargeOperations, version]

theorem chargeOperations_pushData (data : ByteArray) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    chargeOperations (.pushData data) state flags ctx = .ok state := rfl

theorem chargeOperations_pushNum (number : Int) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) :
    chargeOperations (.pushNum number) state flags ctx = .ok state := rfl

/-- Charging changes only the operation count. -/
theorem chargeOperations_ok {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (charging : chargeOperations element state flags ctx = .ok charged) :
    charged = { state with operationCount := charged.operationCount } := by
  unfold chargeOperations at charging
  split at charging
  · split at charging
    · cases charging; rfl
    · cases counted : chargedOperationCount _ state flags <;>
        rw [counted] at charging <;> cases charging
      rfl
  · split at charging
    · cases charging; rfl
    · split at charging
      · cases charging
      · cases charging; rfl
  · split at charging
    · cases charging; rfl
    · split at charging
      · cases charging
      · cases charging; rfl
  · cases charging; rfl

/-- When the step hands FindAndDelete no signature, it checks signatures with
the oracle for the script code as given. -/
theorem ScriptCodeOracles.forStep_of_signatures (oracles : ScriptCodeOracles)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (none : ∀ opcode, element = .op opcode →
      (state.conditions.all id && ctx.sigVersion == .base) = true →
        instructionSignatures opcode state flags = []) :
    oracles.forStep element state flags ctx = .ok (oracles.oracleFor oracles.scriptCode) := by
  unfold ScriptCodeOracles.forStep
  cases element with
  | op opcode =>
      simp only
      by_cases base : (state.conditions.all id && ctx.sigVersion == .base) = true
      · simp only [base, ↓reduceIte, none opcode rfl base]
        rfl
      · simp only [base, Bool.false_eq_true, ↓reduceIte]
        rfl
  | pushData | pushNum | badOpcode | illegalOpcode | nonminimalPush | truncatedPush => rfl

/-- A step charges the operation count and picks its oracle, then runs as the
step with that one oracle. -/
theorem runtimeStep_eq_forStep (oracles : ScriptCodeOracles) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracles element state flags ctx =
      (chargeOperations element state flags ctx).bind fun _ =>
        (oracles.forStep element state flags ctx).bind fun oracle =>
          runtimeStep oracle element state flags ctx := by
  conv => lhs; unfold runtimeStep
  cases charging : chargeOperations element state flags ctx with
  | error => rfl
  | ok charged =>
      cases oracles.forStep element state flags ctx with
      | error => rfl
      | ok oracle => simp [runtimeStep_withoutScriptCode, charging, bind, Except.bind]

/-- When the step hands FindAndDelete no signature, it is the step with the
oracle for the script code as given. -/
theorem runtimeStep_of_signatures (oracles : ScriptCodeOracles) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (none : ∀ opcode, element = .op opcode →
      (state.conditions.all id && ctx.sigVersion == .base) = true →
        instructionSignatures opcode state flags = []) :
    runtimeStep oracles element state flags ctx =
      runtimeStep (oracles.oracleFor oracles.scriptCode) element state flags ctx := by
  simp only [runtimeStep, oracles.forStep_of_signatures element state flags ctx none,
    ScriptCodeOracles.forStep_withoutScriptCode]

/-- Outside BASE, the step is the step with the oracle for the script code as
given. -/
theorem runtimeStep_of_ne_base (oracles : ScriptCodeOracles) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) {ctx : TxContext}
    (version : ctx.sigVersion ≠ .base) :
    runtimeStep oracles element state flags ctx =
      runtimeStep (oracles.oracleFor oracles.scriptCode) element state flags ctx :=
  runtimeStep_of_signatures oracles element state flags ctx
    (fun _ _ base => by
      have other : (ctx.sigVersion == .base) = false := by
        cases versionEq : ctx.sigVersion <;> first | exact absurd versionEq version | rfl
      simp [other] at base)

/-- Tapscript steps are the uncounted instruction. -/
theorem runtimeStep_tapscript (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) {ctx : TxContext}
    (version : ctx.sigVersion = .tapscript) :
    runtimeStep oracle element state flags ctx =
      runtimeInstruction oracle element state flags ctx := by
  simp [runtimeStep_withoutScriptCode, chargeOperations_tapscript element state flags version,
    Except.bind]

theorem runtimeStep_pushData (oracle : CryptoOracle) (data : ByteArray)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (.pushData data) state flags ctx =
      runtimeInstruction oracle (.pushData data) state flags ctx := rfl

theorem runtimeStep_pushNumber (oracle : CryptoOracle) (number : Int)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle (.pushNum number) state flags ctx =
      runtimeInstruction oracle (.pushNum number) state flags ctx := rfl

@[simp] theorem ScriptElement.underTimelockFlags_pushData (flags : ScriptFlags) (data : ByteArray) :
    (ScriptElement.pushData data).underTimelockFlags flags = .pushData data := rfl

@[simp] theorem ScriptElement.underTimelockFlags_pushNum (flags : ScriptFlags) (number : Int) :
    (ScriptElement.pushNum number).underTimelockFlags flags = .pushNum number := rfl

@[simp] theorem ScriptElement.underTimelockFlags_op (flags : ScriptFlags) {opcode : Opcode}
    (locktime : opcode ≠ .OP_CHECKLOCKTIMEVERIFY) (sequence : opcode ≠ .OP_CHECKSEQUENCEVERIFY) :
    (ScriptElement.op opcode).underTimelockFlags flags = .op opcode := by
  cases opcode <;> first | rfl | contradiction

@[simp] theorem ScriptElement.underTimelockFlags_checkLockTimeVerify (flags : ScriptFlags) :
    (ScriptElement.op .OP_CHECKLOCKTIMEVERIFY).underTimelockFlags flags =
      if flags.checkLockTimeVerify then .op .OP_CHECKLOCKTIMEVERIFY else .op .OP_NOP := rfl

@[simp] theorem ScriptElement.underTimelockFlags_checkSequenceVerify (flags : ScriptFlags) :
    (ScriptElement.op .OP_CHECKSEQUENCEVERIFY).underTimelockFlags flags =
      if flags.checkSequenceVerify then .op .OP_CHECKSEQUENCEVERIFY else .op .OP_NOP := rfl

/-- With both timelock flags on, the runtime executes every element as written. -/
theorem ScriptElement.underTimelockFlags_eq (element : ScriptElement) {flags : ScriptFlags}
    (locktime : flags.checkLockTimeVerify = true)
    (sequence : flags.checkSequenceVerify = true) :
    element.underTimelockFlags flags = element := by
  unfold ScriptElement.underTimelockFlags
  split <;> simp_all

/-- A timelock that succeeds leaves both stacks unchanged, so OP_NOP gives the
same result when its flag is off. -/
theorem evaluate_underTimelockFlags_success {oracle : CryptoOracle} {element : ScriptElement}
    {stack alt finalStack finalAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (success : evaluate oracle [element] stack alt flags ctx = .success finalStack finalAlt) :
    evaluate oracle [element.underTimelockFlags flags] stack alt flags ctx =
      .success finalStack finalAlt := by
  unfold ScriptElement.underTimelockFlags
  split
  · split
    · exact success
    · cases stack with
      | nil => simp [evaluate] at success
      | cons operand rest =>
          simp only [evaluate] at success
          split at success <;> (try split at success) <;> (try split at success) <;>
            simp_all [evaluate]
  · split
    · exact success
    · cases stack with
      | nil => simp [evaluate] at success
      | cons operand rest =>
          simp only [evaluate] at success
          split at success <;> (try split at success) <;> (try split at success) <;>
            simp_all [evaluate]
  · exact success

/-- With its flag off, OP_CHECKLOCKTIMEVERIFY steps exactly like OP_NOP. -/
theorem runtimeStep_checkLockTimeVerify_off (oracle : CryptoOracle) (state : RuntimeState)
    {flags : ScriptFlags} (ctx : TxContext) (off : flags.checkLockTimeVerify = false) :
    runtimeStep oracle (.op .OP_CHECKLOCKTIMEVERIFY) state flags ctx =
      runtimeStep oracle (.op .OP_NOP) state flags ctx := by
  simp [runtimeStep, chargeOperations, chargedOperationCount, opcodeKeyCount,
    runtimeInstruction, executeRuntimeElement, ScriptElement.underTimelockFlags, off,
    prepareValidationWeight, ScriptElement.pushSize]

/-- With its flag off, OP_CHECKSEQUENCEVERIFY steps exactly like OP_NOP. -/
theorem runtimeStep_checkSequenceVerify_off (oracle : CryptoOracle) (state : RuntimeState)
    {flags : ScriptFlags} (ctx : TxContext) (off : flags.checkSequenceVerify = false) :
    runtimeStep oracle (.op .OP_CHECKSEQUENCEVERIFY) state flags ctx =
      runtimeStep oracle (.op .OP_NOP) state flags ctx := by
  simp [runtimeStep, chargeOperations, chargedOperationCount, opcodeKeyCount,
    runtimeInstruction, executeRuntimeElement, ScriptElement.underTimelockFlags, off,
    prepareValidationWeight, ScriptElement.pushSize]

/-- A successful step charged the operation count, then ran the instruction on
the charged state. -/
theorem runtimeStep_ok {oracle : CryptoOracle} {element : ScriptElement}
    {state next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element state flags ctx = .ok next) :
    ∃ count, chargeOperations element state flags ctx =
        .ok { state with operationCount := count } ∧
      runtimeInstruction oracle element { state with operationCount := count } flags ctx =
        .ok next := by
  rw [runtimeStep_withoutScriptCode] at stepped
  cases charging : chargeOperations element state flags ctx with
  | error error => simp [charging, Except.bind] at stepped
  | ok charged =>
      simp only [charging, Except.bind] at stepped
      have same := chargeOperations_ok charging
      exact ⟨charged.operationCount, by rw [← same], by rw [← same]; exact stepped⟩


theorem executeRuntimeElement_operationCount (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) (count : Nat) :
    executeRuntimeElement oracle element { state with operationCount := count } flags ctx =
      (executeRuntimeElement oracle element state flags ctx).map
        ({ · with operationCount := count }) := by
  obtain ⟨stack, alt, conditions, weight, n⟩ := state
  unfold executeRuntimeElement
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  split
  · rfl
  · split
    all_goals
      by_cases active : conditions.all id = true <;>
        (try simp only [active, ↓reduceIte, Bool.false_eq_true])
    all_goals first
      | rfl
      | (cases stack with
          | nil => rfl
          | cons top rest => simp only; split <;> rfl)
      | (cases conditions <;> rfl)
      | (cases prepareValidationWeight element stack flags ctx weight with
          | error => rfl
          | ok weight =>
              simp only
              cases evaluate oracle [element.underTimelockFlags flags] stack alt flags ctx <;> rfl)

theorem runtimeInstruction_operationCount (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) (count : Nat) :
    runtimeInstruction oracle element { state with operationCount := count } flags ctx =
      (runtimeInstruction oracle element state flags ctx).map
        ({ · with operationCount := count }) := by
  simp only [runtimeInstruction, executeRuntimeElement_operationCount]
  cases executeRuntimeElement oracle element state flags ctx with
  | error => rfl
  | ok next =>
      simp only [Except.map, bind, Except.bind, checkRuntimeStack]
      split <;> rfl

theorem chargedOperationCount_ok {opcode : Opcode} {state : RuntimeState}
    {flags : ScriptFlags} {total : Nat}
    (counted : chargedOperationCount opcode state flags = .ok total) :
    ∃ keys, opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok keys ∧
      total = state.operationCount + 1 + keys ∧ total ≤ maxOpsPerScript := by
  unfold chargedOperationCount at counted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at counted
  split at counted
  · contradiction
  · cases keys : opcodeKeyCount opcode flags (state.conditions.all id) state.stack with
    | error => simp [keys] at counted
    | ok keys' =>
        simp only [keys] at counted
        split at counted
        · contradiction
        · cases counted
          exact ⟨keys', rfl, rfl, by omega⟩

theorem chargedOperationCount_of_keys {opcode : Opcode} {state : RuntimeState}
    {flags : ScriptFlags} {keys : Nat}
    (decoded : opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok keys)
    (bounded : state.operationCount + 1 + keys ≤ maxOpsPerScript) :
    chargedOperationCount opcode state flags = .ok (state.operationCount + 1 + keys) := by
  unfold chargedOperationCount
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    decoded]
  rw [if_neg (by omega), if_neg (by omega)]

/-- Charging only raises the count. -/
theorem chargeOperations_le {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (charging : chargeOperations element state flags ctx = .ok charged) :
    state.operationCount ≤ charged.operationCount := by
  unfold chargeOperations at charging
  split at charging
  · split at charging
    · cases charging; exact Nat.le_refl _
    · cases counted : chargedOperationCount _ state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging; cases charging
          obtain ⟨keys, _, rfl, _⟩ := chargedOperationCount_ok counted
          simp only; omega
  · split at charging
    · cases charging; exact Nat.le_refl _
    · split at charging
      · cases charging
      · cases charging; exact Nat.le_succ _
  · split at charging
    · cases charging; exact Nat.le_refl _
    · split at charging
      · cases charging
      · cases charging; exact Nat.le_succ _
  · cases charging; exact Nat.le_refl _

/-- A lower starting count charges the same keys and stays within the limit. -/
theorem chargeOperations_lower {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {count : Nat}
    (charging : chargeOperations element state flags ctx = .ok charged)
    (lower : count ≤ state.operationCount) :
    ∃ lowered, lowered ≤ charged.operationCount ∧
      chargeOperations element { state with operationCount := count } flags ctx =
        .ok { charged with operationCount := lowered } := by
  have same := chargeOperations_ok charging
  unfold chargeOperations at charging ⊢
  split at charging
  · rename_i opcode
    split at charging
    · rename_i version
      cases charging
      exact ⟨count, lower, by simp [version]⟩
    · rename_i version
      cases counted : chargedOperationCount opcode state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging; cases charging
          obtain ⟨keys, decoded, rfl, bounded⟩ := chargedOperationCount_ok counted
          refine ⟨count + 1 + keys, by simp only; omega, ?_⟩
          rw [if_neg version, chargedOperationCount_of_keys (state := { state with operationCount := count })
            decoded (by simp only; omega)]
          rfl
  · split at charging
    · rename_i version
      cases charging
      exact ⟨count, lower, by simp [version]⟩
    · rename_i version
      split at charging
      · cases charging
      · rename_i within
        cases charging
        refine ⟨count + 1, by simp only; omega, ?_⟩
        simp [version, show ¬ count + 1 > maxOpsPerScript by omega]
  · split at charging
    · rename_i version
      cases charging
      exact ⟨count, lower, by simp [version]⟩
    · rename_i version
      split at charging
      · cases charging
      · rename_i within
        cases charging
        refine ⟨count + 1, by simp only; omega, ?_⟩
        simp [version, show ¬ count + 1 > maxOpsPerScript by omega]
  · cases charging
    exact ⟨count, lower, rfl⟩

theorem runtimeInstruction_operationCount_eq {oracle : CryptoOracle} {element : ScriptElement}
    {state next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeInstruction oracle element state flags ctx = .ok next) :
    next.operationCount = state.operationCount := by
  have moved := runtimeInstruction_operationCount oracle element state flags ctx state.operationCount
  rw [show ({ state with operationCount := state.operationCount } : RuntimeState) = state from rfl,
    stepped] at moved
  simp only [Except.map] at moved
  injection moved with moved
  have counted := congrArg RuntimeState.operationCount moved
  exact counted

/-- Charging reads the conditions only through whether the step is active. -/
theorem chargeOperations_conditions {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} (conditions : List Bool)
    (active : conditions.all id = state.conditions.all id)
    (charging : chargeOperations element state flags ctx = .ok charged) :
    chargeOperations element { state with conditions := conditions } flags ctx =
      .ok { charged with conditions := conditions } := by
  have same := chargeOperations_ok charging
  unfold chargeOperations at charging ⊢
  split at charging
  · rename_i opcode
    split at charging
    · rename_i version
      cases charging
      simp [version]
    · rename_i version
      cases counted : chargedOperationCount opcode state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging; cases charging
          obtain ⟨keys, decoded, rfl, bounded⟩ := chargedOperationCount_ok counted
          rw [if_neg version, chargedOperationCount_of_keys (state := { state with conditions := conditions })
            (by simpa only [active] using decoded) bounded]
          rfl
  · split at charging
    · rename_i version
      cases charging
      simp [version]
    · rename_i version
      split at charging
      · cases charging
      · rename_i within
        cases charging
        simp [version, within]
  · split at charging
    · rename_i version
      cases charging
      simp [version]
    · rename_i version
      split at charging
      · cases charging
      · rename_i within
        cases charging
        simp [version, within]
  · cases charging
    rfl


/-- Opcodes outside conditional control flow. Inactive execution of these is
    the identity on the runtime state, while OP_IF, OP_NOTIF, OP_ELSE and
    OP_ENDIF always update the condition list. -/
def Opcode.isNonConditional (opcode : Opcode) : Bool :=
  match opcode with
  | .OP_IF | .OP_NOTIF | .OP_ELSE | .OP_ENDIF => false
  | _ => true

/-- Inactive execution of a non-conditional opcode leaves the entire state
    unchanged, including malformed or missing operands. -/
theorem executeRuntimeElement_op_inactive (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (nonConditional : opcode.isNonConditional = true)
    (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op opcode) state flags ctx = .ok state := by
  cases opcode <;> simp_all [Opcode.isNonConditional, executeRuntimeElement,
    ScriptElement.pushSize, maxScriptElementSize] <;> rfl

/-- An inactive non-conditional opcode still performs the shared
    post-instruction combined-stack check. -/
theorem runtimeInstruction_op_inactive (oracle : CryptoOracle) (opcode : Opcode)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (nonConditional : opcode.isNonConditional = true)
    (inactive : state.conditions.all id = false) :
    runtimeInstruction oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  rw [runtimeInstruction,
    executeRuntimeElement_op_inactive oracle opcode state flags ctx nonConditional inactive]
  rfl

/-- A successful step coincides with element-level execution: the shared
    post-instruction stack check only rejects oversized states, it never
    modifies the state it returns. -/
theorem executeRuntimeElement_eq_of_runtimeInstruction
    {oracle : CryptoOracle} {element : ScriptElement} {state next : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeInstruction oracle element state flags ctx = .ok next) :
    executeRuntimeElement oracle element state flags ctx = .ok next := by
  unfold runtimeInstruction at stepped
  cases executed : executeRuntimeElement oracle element state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      rfl


/-- Active DEPTH changes only the main stack, preserving the condition stack,
    alternate stack and signature budget for every oracle. -/
theorem executeRuntimeElement_depth (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_DEPTH) state flags ctx =
      .ok { state with stack := scriptNat state.stack.length :: state.stack } := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_depth]
  rfl

/-- The extra DEPTH item must fit in the combined main/alternate stack limit.
    The check runs after the push and retains the remaining signature budget. -/
theorem runtimeInstruction_depth (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_DEPTH) state flags ctx =
      if state.stack.length + state.altStack.length < maxStackSize then
        .ok { state with stack := scriptNat state.stack.length :: state.stack }
      else .error .stackSize := by
  rw [runtimeInstruction, executeRuntimeElement_depth oracle state flags ctx active]
  simp only [bind, Except.bind, checkRuntimeStack, List.length_cons]
  split <;> split <;> first | rfl | omega

/-- Active NOT decodes one operand and preserves every other runtime field.
    Underflow and decoder errors are returned before the stack-limit check. -/
theorem executeRuntimeElement_not (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_NOT) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value => .ok { state with stack := boolToElement (value == 0) :: rest } := by
  cases stackEq : state.stack with
  | nil =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_not, stackEq]
      rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          active, prepareValidationWeight, evaluate_not, stackEq, decoded] <;> rfl

/-- Every successful NOT step before resource checking preserves stack count,
    alternate stack, conditions and signature budget, in active or inactive code. -/
theorem executeRuntimeElement_not_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_NOT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧ next.altStack = state.altStack ∧
      next.conditions = state.conditions ∧ next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_NOT state flags ctx rfl active] at executed
      cases executed
      exact ⟨rfl, rfl, rfl, rfl⟩
  | true =>
      rw [executeRuntimeElement_not oracle state flags ctx active] at executed
      cases stackEq : state.stack with
      | nil => simp [stackEq] at executed
      | cons operand rest =>
          cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
            simp [stackEq, decoded] at executed
          cases executed
          simp

/-- For active NOT, numeric errors precede the combined-stack limit; successful
    decoding keeps the stack count and succeeds exactly within that limit. -/
theorem runtimeInstruction_not (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_NOT) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (value == 0) :: rest } := by
  rw [runtimeInstruction, executeRuntimeElement_not oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active WITHIN decodes value, lower bound, then upper bound. Success removes
    two main-stack items and preserves every other runtime field. -/
theorem executeRuntimeElement_within (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_WITHIN) state flags ctx =
      match state.stack with
      | upperBytes :: lowerBytes :: valueBytes :: rest =>
          match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
          | .error error => .error error
          | .ok (upper, lower, value) =>
              .ok { state with stack := boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨upperBytes, _ | ⟨lowerBytes, _ | ⟨valueBytes, rest⟩⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_within, stackEq]; rfl }
  cases decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_within, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨upper, lower, value⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_within, stackEq, decoded]
      rfl

/-- Successful active WITHIN reduces stack count by two; inactive WITHIN keeps
    it unchanged. Both preserve the alternate stack, conditions and budget. -/
theorem executeRuntimeElement_within_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_WITHIN) state flags ctx = .ok next) :
    next.stack.length + (if state.conditions.all id then 2 else 0) = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_WITHIN state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_within oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨upperBytes, _ | ⟨lowerBytes, _ | ⟨valueBytes, rest⟩⟩⟩
      all_goals try { simp [stackEq] at executed }
      cases decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
      | error error => simp [stackEq, decoded] at executed
      | ok values =>
          rcases values with ⟨upper, lower, value⟩
          simp [stackEq, decoded] at executed
          cases executed
          simp

/-- Underflow and all three decoder errors precede the post-instruction stack
    check. The successful result has one item above the untouched suffix. -/
theorem runtimeInstruction_within (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_WITHIN) state flags ctx =
      match state.stack with
      | upperBytes :: lowerBytes :: valueBytes :: rest =>
          match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
          | .error error => .error error
          | .ok (upper, lower, value) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_within oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨upperBytes, _ | ⟨lowerBytes, _ | ⟨valueBytes, rest⟩⟩⟩
  all_goals try rfl
  cases decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨upper, lower, value⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active NIP removes the second main-stack item and keeps all other bytes
    and runtime fields. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_nip (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_NIP) state flags ctx =
      match state.stack with
      | top :: _ :: rest => .ok { state with stack := top :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_nip, stackEq]
    rfl

/-- Successful active NIP reduces stack count by one; inactive NIP keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_nip_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_NIP) state flags ctx = .ok next) :
    next.stack.length + (if state.conditions.all id then 1 else 0) = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_NIP state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_nip oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- NIP underflow precedes resource checking. Success checks the combined
    main/alternate stack count after removing the second item. -/
theorem runtimeInstruction_nip (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_NIP) state flags ctx =
      match state.stack with
      | top :: _ :: rest =>
          if rest.length + 1 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_nip oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack]

/-- Active 2DROP removes the top two main-stack items and keeps the remaining bytes
    and runtime fields. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_twoDrop (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_2DROP) state flags ctx =
      match state.stack with
      | _ :: _ :: rest => .ok { state with stack := rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_twoDrop, stackEq]
    rfl

/-- Successful active 2DROP reduces stack count by two; inactive 2DROP keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_twoDrop_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_2DROP) state flags ctx = .ok next) :
    next.stack.length + (if state.conditions.all id then 2 else 0) = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_2DROP state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_twoDrop oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp [Nat.add_assoc]

/-- 2DROP underflow precedes resource checking. Success checks the combined
    main/alternate stack count after removing both items. -/
theorem runtimeInstruction_twoDrop (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_2DROP) state flags ctx =
      match state.stack with
      | _ :: _ :: rest =>
          if rest.length + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_twoDrop oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack]

/-- Active 2DUP copies the top pair in order, keeping the original stack
    and every other runtime field. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_twoDup (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_2DUP) state flags ctx =
      match state.stack with
      | top :: below :: rest => .ok { state with stack := top :: below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_twoDup, stackEq]
    rfl

/-- Successful active 2DUP increases stack count by two; inactive 2DUP keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_twoDup_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_2DUP) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 2 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_2DUP state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_twoDup oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- 2DUP underflow precedes resource checking. Success checks the combined
    main/alternate stack count after pushing both copied items. -/
theorem runtimeInstruction_twoDup (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_2DUP) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 4 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_twoDup oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active 2OVER copies the third and fourth items in order, keeping the original
    stack and every other runtime field. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_twoOver (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_2OVER) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: rest =>
          .ok { state with stack := third :: fourth :: top :: second :: third :: fourth :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_twoOver, stackEq]
    rfl

/-- Successful active 2OVER increases stack count by two; inactive 2OVER keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_twoOver_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_2OVER) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 2 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_2OVER state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_twoOver oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- 2OVER underflow precedes resource checking. Success checks the combined
    main/alternate stack count after pushing both copied items. -/
theorem runtimeInstruction_twoOver (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_2OVER) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: rest =>
          if rest.length + 6 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := third :: fourth :: top :: second :: third :: fourth :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_twoOver oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active 3DUP copies the top three items in order, keeping the original stack
    and every other runtime field. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_threeDup (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_3DUP) state flags ctx =
      match state.stack with
      | top :: second :: third :: rest =>
          .ok { state with stack := top :: second :: third :: top :: second :: third :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_threeDup, stackEq]
    rfl

/-- Successful active 3DUP increases stack count by three; inactive 3DUP keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_threeDup_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_3DUP) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 3 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_3DUP state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_threeDup oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- 3DUP underflow precedes resource checking. Success checks the combined
    main/alternate stack count after pushing all three copied items. -/
theorem runtimeInstruction_threeDup (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_3DUP) state flags ctx =
      match state.stack with
      | top :: second :: third :: rest =>
          if rest.length + 6 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: second :: third :: top :: second :: third :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_threeDup oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active OVER copies the second item to the top, keeping the original stack
    and every other runtime field. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_over (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_OVER) state flags ctx =
      match state.stack with
      | top :: below :: rest => .ok { state with stack := below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_over, stackEq]
    rfl

/-- Successful active OVER increases stack count by one; inactive OVER keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_over_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_OVER) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 1 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_OVER state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_over oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- OVER underflow precedes resource checking. Success checks the combined
    main/alternate stack count after pushing the copied item. -/
theorem runtimeInstruction_over (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_OVER) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_over oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active TUCK inserts a top-item copy beneath the top two, preserving the
    remaining stack and every other runtime field. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_tuck (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_TUCK) state flags ctx =
      match state.stack with
      | top :: below :: rest => .ok { state with stack := top :: below :: top :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_tuck, stackEq]
    rfl

/-- Successful active TUCK increases stack count by one; inactive TUCK keeps it.
    Both preserve the alternate stack, conditions and signature budget. -/
theorem executeRuntimeElement_tuck_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_TUCK) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 1 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_TUCK state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_tuck oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- TUCK underflow precedes resource checking. Success checks the combined
    main/alternate stack count after inserting the copied item. -/
theorem runtimeInstruction_tuck (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_TUCK) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: below :: top :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_tuck oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active ROT moves the third item to the top, preserving all other runtime
    fields. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_rot (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_ROT) state flags ctx =
      match state.stack with
      | top :: second :: third :: rest =>
          .ok { state with stack := third :: top :: second :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_rot, stackEq]
    rfl

/-- Successful ROT preserves stack count, alternate stack, conditions and
    signature budget, in both active and inactive branches. -/
theorem executeRuntimeElement_rot_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_ROT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_ROT state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_rot oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- ROT checks its three inputs before the combined-stack bound; rotation
    preserves the count used by that bound. -/
theorem runtimeInstruction_rot (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_ROT) state flags ctx =
      match state.stack with
      | top :: second :: third :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := third :: top :: second :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_rot oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active 2ROT moves the fifth and sixth items to the top, preserving all other runtime
    fields. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_twoRot (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_2ROT) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: fifth :: sixth :: rest =>
          .ok { state with stack := fifth :: sixth :: top :: second :: third :: fourth :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_twoRot, stackEq]
    rfl

/-- Successful 2ROT preserves stack count, alternate stack, conditions and
    signature budget, in both active and inactive branches. -/
theorem executeRuntimeElement_twoRot_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_2ROT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_2ROT state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_twoRot oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- 2ROT checks its six inputs before the combined-stack bound; rotation
    preserves the count used by that bound. -/
theorem runtimeInstruction_twoRot (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_2ROT) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: fifth :: sixth :: rest =>
          if rest.length + 6 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := fifth :: sixth :: top :: second :: third :: fourth :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_twoRot oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- Active 2SWAP exchanges the top two pairs, preserving all other runtime
    fields. Underflow precedes the combined-stack limit. -/
theorem executeRuntimeElement_twoSwap (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_2SWAP) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: rest =>
          .ok { state with stack := third :: fourth :: top :: second :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_twoSwap, stackEq]
    rfl

/-- Successful 2SWAP preserves stack count, alternate stack, conditions and
    signature budget, in both active and inactive branches. -/
theorem executeRuntimeElement_twoSwap_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_2SWAP) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_op_inactive oracle .OP_2SWAP state flags ctx rfl active] at executed
      cases executed
      simp
  | true =>
      rw [executeRuntimeElement_twoSwap oracle state flags ctx active] at executed
      rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
      all_goals simp [stackEq] at executed
      cases executed
      simp

/-- 2SWAP checks its four inputs before the combined-stack bound; pair exchange
    preserves the count used by that bound. -/
theorem runtimeInstruction_twoSwap (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeInstruction oracle (.op .OP_2SWAP) state flags ctx =
      match state.stack with
      | top :: second :: third :: fourth :: rest =>
          if rest.length + 4 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := third :: fourth :: top :: second :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeInstruction, executeRuntimeElement_twoSwap oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

theorem runtimeInstruction_stackBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeInstruction oracle element before flags ctx = .ok after) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold runtimeInstruction at stepped
  cases computed : executeRuntimeElement oracle element before flags ctx with
  | error error => simp [computed, bind, Except.bind] at stepped
  | ok next =>
      simp only [computed, bind, Except.bind] at stepped
      exact (checkRuntimeStack_ok stepped).2

theorem runtimeStep_stackBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  let ⟨_, _, instruction⟩ := runtimeStep_ok stepped
  runtimeInstruction_stackBound instruction

/-- Every visited instruction, active or skipped, passes the push-size bound. -/
theorem runtimeStep_pushBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    element.pushSize ≤ maxScriptElementSize := by
  obtain ⟨_, _, instruction⟩ := runtimeStep_ok stepped
  by_cases exceeded : element.pushSize > maxScriptElementSize
  · simp [runtimeInstruction, executeRuntimeElement, exceeded, bind, Except.bind] at instruction
  · exact Nat.le_of_not_gt exceeded

theorem runtimeInstruction_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeInstruction oracle element state flags ctx =
      runtimeInstruction CryptoOracle.model element state flags ctx := by
  have opcode := evaluate_eq_of_eval agreement
    (evaluate_sound CryptoOracle.model_refines [element.underTimelockFlags flags] state.stack
      state.altStack flags ctx)
  simp only [runtimeInstruction, executeRuntimeElement, opcode]

/-- Resource and control checks do not weaken the existing crypto boundary. -/
theorem runtimeStep_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle element state flags ctx =
      runtimeStep CryptoOracle.model element state flags ctx := by
  simp only [runtimeStep_withoutScriptCode, runtimeInstruction_eq_model agreement]


/-- These resource guarantees hold for every oracle, without a cryptographic
    agreement premise. Successful execution visits every source instruction. -/
theorem evaluateRuntime_bounds
    {oracle : CryptoOracle} {flags : ScriptFlags} {ctx : TxContext}
    (script : Script) {state : RuntimeState} {stack alt : Stack} {weight : Nat}
    (initial : state.stack.length + state.altStack.length ≤ maxStackSize)
    (success : evaluateRuntime oracle script state flags ctx = .success stack alt weight) :
    stack.length + alt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  induction script generalizing state with
  | nil =>
      simp only [evaluateRuntime, finishRuntime] at success
      split at success
      · cases success; exact ⟨initial, by simp⟩
      · contradiction
  | cons element rest ih =>
      simp only [evaluateRuntime] at success
      cases stepped : runtimeStep oracle element state flags ctx with
      | error error => simp [stepped] at success
      | ok next =>
          simp only [stepped] at success
          obtain ⟨bounded, pushes⟩ := ih (runtimeStep_stackBound stepped) success
          refine ⟨bounded, ?_⟩
          intro item member
          rcases List.mem_cons.mp member with same | tail
          · subst item; exact runtimeStep_pushBound stepped
          · exact pushes item tail


/-- Starting from a lower operation count keeps every successful result. -/
theorem evaluateRuntime_lower {oracle : CryptoOracle} {script : Script}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight count : Nat}
    (success : evaluateRuntime oracle script state flags ctx = .success stack alt weight)
    (lower : count ≤ state.operationCount) :
    evaluateRuntime oracle script { state with operationCount := count } flags ctx =
      .success stack alt weight := by
  induction script generalizing state count with
  | nil => simpa [evaluateRuntime, finishRuntime] using success
  | cons element rest ih =>
      simp only [evaluateRuntime] at success ⊢
      cases stepped : runtimeStep oracle element state flags ctx with
      | error error => simp [stepped] at success
      | ok next =>
          simp only [stepped] at success
          obtain ⟨charged, charging, instruction⟩ := runtimeStep_ok stepped
          obtain ⟨lowered, below, charging'⟩ := chargeOperations_lower charging lower
          have moved := runtimeInstruction_operationCount oracle element
            { state with operationCount := charged } flags ctx lowered
          rw [instruction] at moved
          have counted := runtimeInstruction_operationCount_eq instruction
          have next_step : runtimeStep oracle element { state with operationCount := count } flags ctx =
              .ok { next with operationCount := lowered } := by
            simp only [runtimeStep_withoutScriptCode, charging', Except.bind]
            exact moved
          rw [next_step]
          exact ih success (by simp only at below counted; omega)


/-- The most one source element adds to the BASE or witness-v0 operation
count: one per opcode, `badOpcode`, or `illegalOpcode`, plus at most
`maxPubKeysPerMultiSig` multisig keys. -/
def ScriptElement.operationBound : ScriptElement → Nat
  | .op .OP_CHECKMULTISIG | .op .OP_CHECKMULTISIGVERIFY => 1 + maxPubKeysPerMultiSig
  | .op _ | .badOpcode _ | .illegalOpcode _ => 1
  | _ => 0

/-- A source-only bound on the operations any run charges, skipped branches
included. -/
def staticOperationCount (script : Script) : Nat :=
  (script.map ScriptElement.operationBound).sum

theorem staticOperationCount_cons (element : ScriptElement) (rest : Script) :
    staticOperationCount (element :: rest) =
      element.operationBound + staticOperationCount rest := by
  simp [staticOperationCount]

theorem staticOperationCount_sublist {selected script : Script}
    (sub : selected.Sublist script) :
    staticOperationCount selected ≤ staticOperationCount script := by
  induction sub <;> simp_all [staticOperationCount] <;> omega

theorem multisigKeyCount_le {flags : ScriptFlags} {stack : Stack} {keys : Nat}
    (decoded : multisigKeyCount flags stack = .ok keys) : keys ≤ maxPubKeysPerMultiSig := by
  cases stack with
  | nil => cases decoded
  | cons top rest =>
      simp only [multisigKeyCount, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at decoded
      cases number : decodeScriptNum top flags.minimalData maxArithmeticScriptNumBytes with
      | error => simp [number] at decoded
      | ok value =>
          by_cases outside : value < 0 ∨ (maxPubKeysPerMultiSig : Int) < value
          · simp [number, outside] at decoded
          · simp only [number, outside, ↓reduceIte, Except.ok.injEq] at decoded
            subst keys
            simp only [not_or, Int.not_lt] at outside
            omega

theorem opcodeKeyCount_le {opcode : Opcode} {flags : ScriptFlags} {active : Bool}
    {stack : Stack} {keys : Nat}
    (decoded : opcodeKeyCount opcode flags active stack = .ok keys) :
    1 + keys ≤ (ScriptElement.op opcode).operationBound := by
  cases opcode
  case OP_CHECKMULTISIG | OP_CHECKMULTISIGVERIFY =>
    simp only [opcodeKeyCount] at decoded
    split at decoded
    · have := multisigKeyCount_le decoded
      simp [ScriptElement.operationBound]; omega
    · cases decoded; simp [ScriptElement.operationBound]
  all_goals
    simp only [opcodeKeyCount] at decoded
    cases decoded
    simp [ScriptElement.operationBound]

/-- One step charges at most the element's source bound. -/
theorem chargeOperations_bound {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (charging : chargeOperations element state flags ctx = .ok charged) :
    charged.operationCount ≤ state.operationCount + element.operationBound := by
  unfold chargeOperations at charging
  split at charging
  · split at charging
    · cases charging; omega
    · cases counted : chargedOperationCount _ state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging; cases charging
          obtain ⟨keys, decoded, rfl, _⟩ := chargedOperationCount_ok counted
          have := opcodeKeyCount_le decoded
          simp only; omega
  · split at charging
    · cases charging; omega
    · split at charging
      · cases charging
      · cases charging; simp [ScriptElement.operationBound]
  · split at charging
    · cases charging; omega
    · split at charging
      · cases charging
      · cases charging; simp [ScriptElement.operationBound]
  · cases charging; omega

/-- A higher starting count charges the same keys when the element's source
bound still fits. -/
theorem chargeOperations_raise {element : ScriptElement} {state charged : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {count : Nat}
    (charging : chargeOperations element state flags ctx = .ok charged)
    (higher : state.operationCount ≤ count)
    (fits : ctx.sigVersion = .tapscript ∨ count + element.operationBound ≤ maxOpsPerScript) :
    ∃ raised, charged.operationCount ≤ raised ∧ raised ≤ count + element.operationBound ∧
      chargeOperations element { state with operationCount := count } flags ctx =
        .ok { charged with operationCount := raised } := by
  have same := chargeOperations_ok charging
  unfold chargeOperations at charging ⊢
  split at charging
  · rename_i opcode
    split at charging
    · rename_i version
      cases charging
      exact ⟨count, higher, by omega, by simp [version]⟩
    · rename_i version
      have fits : count + (ScriptElement.op opcode).operationBound ≤ maxOpsPerScript := by
        simpa [version] using fits
      cases counted : chargedOperationCount opcode state flags with
      | error => rw [counted] at charging; cases charging
      | ok total =>
          rw [counted] at charging; cases charging
          obtain ⟨keys, decoded, rfl, bounded⟩ := chargedOperationCount_ok counted
          have keyBound := opcodeKeyCount_le decoded
          refine ⟨count + 1 + keys, by simp only; omega, by omega, ?_⟩
          rw [if_neg version, chargedOperationCount_of_keys
            (state := { state with operationCount := count }) decoded (by simp only; omega)]
          rfl
  · split at charging
    · rename_i version
      cases charging
      exact ⟨count, higher, by omega, by simp [version]⟩
    · rename_i version
      have tap : ctx.sigVersion ≠ .tapscript := fun same => version (Or.inl same)
      have fits : count + 1 ≤ maxOpsPerScript := by
        simpa [tap, ScriptElement.operationBound] using fits
      split at charging
      · cases charging
      · cases charging
        refine ⟨count + 1, by simp only; omega, by simp [ScriptElement.operationBound], ?_⟩
        simp [version, show ¬ count + 1 > maxOpsPerScript by omega]
  · split at charging
    · rename_i tap
      cases charging
      exact ⟨count, higher, by omega, by simp [tap]⟩
    · rename_i tap
      have fits : count + 1 ≤ maxOpsPerScript := by
        simpa [tap, ScriptElement.operationBound] using fits
      split at charging
      · cases charging
      · cases charging
        refine ⟨count + 1, by simp only; omega, by simp [ScriptElement.operationBound], ?_⟩
        simp [tap, show ¬ count + 1 > maxOpsPerScript by omega]
  · cases charging
    exact ⟨count, higher, by omega, rfl⟩

/-- A step whose key count decodes charges within the element's source bound. -/
theorem chargeOperations_of_keys {element : ScriptElement} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (keys : ctx.sigVersion ≠ .tapscript → ∀ opcode, element = .op opcode → ∃ keys,
      opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok keys)
    (fits : ctx.sigVersion = .tapscript ∨
      state.operationCount + element.operationBound ≤ maxOpsPerScript) :
    ∃ count, state.operationCount ≤ count ∧
      count ≤ state.operationCount + element.operationBound ∧
      chargeOperations element state flags ctx = .ok { state with operationCount := count } := by
  cases element with
  | pushData | pushNum | nonminimalPush | truncatedPush =>
      exact ⟨state.operationCount, by omega, by omega, rfl⟩
  | badOpcode opcode =>
      by_cases skip : ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60
      · refine ⟨state.operationCount, by omega, by omega, ?_⟩
        simp only [chargeOperations]
        rw [if_pos skip]
      · have tap : ctx.sigVersion ≠ .tapscript := fun same => skip (Or.inl same)
        have fits : state.operationCount + 1 ≤ maxOpsPerScript := by
          simpa [tap, ScriptElement.operationBound] using fits
        refine ⟨state.operationCount + 1, by omega, by simp [ScriptElement.operationBound], ?_⟩
        simp only [chargeOperations]
        rw [if_neg skip, if_neg (by omega)]
  | illegalOpcode opcode =>
      by_cases tap : ctx.sigVersion = .tapscript
      · refine ⟨state.operationCount, by omega, by omega, ?_⟩
        simp only [chargeOperations]
        rw [if_pos tap]
      · have fits : state.operationCount + 1 ≤ maxOpsPerScript := by
          simpa [tap, ScriptElement.operationBound] using fits
        refine ⟨state.operationCount + 1, by omega, by simp [ScriptElement.operationBound], ?_⟩
        simp only [chargeOperations]
        rw [if_neg tap, if_neg (by omega)]
  | op opcode =>
      by_cases version : ctx.sigVersion = .tapscript
      · exact ⟨state.operationCount, by omega, by omega, by simp [chargeOperations, version]⟩
      · have fits : state.operationCount + (ScriptElement.op opcode).operationBound ≤
            maxOpsPerScript := by simpa [version] using fits
        obtain ⟨keys, decoded⟩ := keys version opcode rfl
        have keyBound := opcodeKeyCount_le decoded
        refine ⟨state.operationCount + 1 + keys, by omega, by omega, ?_⟩
        simp only [chargeOperations, version, ↓reduceIte,
          chargedOperationCount_of_keys decoded (by omega)]
        rfl

/-- An opcode without a key charge adds one operation, active or not. -/
theorem chargeOperations_quiet {element : ScriptElement} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (quiet : ∀ opcode, element = .op opcode →
      opcodeKeyCount opcode flags (state.conditions.all id) state.stack = .ok 0)
    (fits : ctx.sigVersion = .tapscript ∨
      state.operationCount + element.operationBound ≤ maxOpsPerScript) :
    ∃ count, state.operationCount ≤ count ∧
      count ≤ state.operationCount + element.operationBound ∧
      chargeOperations element state flags ctx = .ok { state with operationCount := count } :=
  chargeOperations_of_keys (fun _ opcode same => ⟨0, quiet opcode same⟩) fits

/-- Inactive code charges only the opcode itself. -/
theorem chargeOperations_inactive {element : ScriptElement} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (inactive : state.conditions.all id = false)
    (fits : ctx.sigVersion = .tapscript ∨
      state.operationCount + element.operationBound ≤ maxOpsPerScript) :
    ∃ count, state.operationCount ≤ count ∧
      count ≤ state.operationCount + element.operationBound ∧
      chargeOperations element state flags ctx = .ok { state with operationCount := count } :=
  chargeOperations_quiet (fun opcode _ => by rw [inactive]; cases opcode <;> rfl) fits

theorem executeRuntimeElement_operationCount_eq {oracle : CryptoOracle} {element : ScriptElement}
    {state next : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    (executed : executeRuntimeElement oracle element state flags ctx = .ok next) :
    next.operationCount = state.operationCount := by
  have moved := executeRuntimeElement_operationCount oracle element state flags ctx
    state.operationCount
  rw [show ({ state with operationCount := state.operationCount } : RuntimeState) = state from rfl,
    executed] at moved
  simp only [Except.map] at moved
  injection moved with moved
  have counted := congrArg RuntimeState.operationCount moved
  exact counted

/-- Starting from a higher operation count keeps every successful result while
the source bound still fits. -/
theorem evaluateRuntime_raise {oracle : CryptoOracle} {script : Script}
    {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {stack alt : Stack} {weight count : Nat}
    (success : evaluateRuntime oracle script state flags ctx = .success stack alt weight)
    (higher : state.operationCount ≤ count)
    (fits : ctx.sigVersion = .tapscript ∨ count + staticOperationCount script ≤ maxOpsPerScript) :
    evaluateRuntime oracle script { state with operationCount := count } flags ctx =
      .success stack alt weight := by
  induction script generalizing state count with
  | nil => simpa [evaluateRuntime, finishRuntime] using success
  | cons element rest ih =>
      rw [staticOperationCount_cons] at fits
      simp only [evaluateRuntime] at success ⊢
      cases stepped : runtimeStep oracle element state flags ctx with
      | error error => simp [stepped] at success
      | ok next =>
          simp only [stepped] at success
          obtain ⟨charged, charging, instruction⟩ := runtimeStep_ok stepped
          obtain ⟨raised, above, below, charging'⟩ := chargeOperations_raise charging higher
            (by rcases fits with fits | fits; exact .inl fits; exact .inr (by omega))
          have moved := runtimeInstruction_operationCount oracle element
            { state with operationCount := charged } flags ctx raised
          rw [instruction] at moved
          have counted := runtimeInstruction_operationCount_eq instruction
          have next_step : runtimeStep oracle element { state with operationCount := count } flags ctx =
              .ok { next with operationCount := raised } := by
            simp only [runtimeStep_withoutScriptCode, charging', Except.bind]
            exact moved
          rw [next_step]
          exact ih success (by simp only at above counted; omega)
            (by rcases fits with fits | fits; exact .inl fits; exact .inr (by omega))


theorem evaluateRuntime_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {state : RuntimeState} {flags : ScriptFlags} {ctx : TxContext}
    {result : WeightedResult} (evaluated : RuntimeEval script state flags ctx result) :
    evaluateRuntime oracle script state flags ctx = result := by
  induction evaluated with
  | done => rfl
  | error failed => simp [evaluateRuntime, runtimeStep_eq_model agreement, failed]
  | step stepped tail ih => simp [evaluateRuntime, runtimeStep_eq_model agreement, stepped, ih]

theorem evaluateRuntime_sound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    RuntimeEval script state flags ctx (evaluateRuntime oracle script state flags ctx) := by
  induction script generalizing state with
  | nil => exact .done state flags ctx
  | cons element rest ih =>
      simp only [evaluateRuntime, runtimeStep_eq_model agreement]
      cases stepped : runtimeStep CryptoOracle.model element state flags ctx with
      | error error => exact .error stepped
      | ok next => exact .step stepped (ih next)

theorem runtime_model_iff {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {result : WeightedResult} :
    RuntimeEval script state flags ctx result ↔
      evaluateRuntime CryptoOracle.model script state flags ctx = result := by
  constructor
  · exact evaluateRuntime_eq_of_eval CryptoOracle.model_refines
  · intro computed
    rw [← computed]
    exact evaluateRuntime_sound CryptoOracle.model_refines script state flags ctx

theorem RuntimeEval.deterministic {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {first second : WeightedResult}
    (a : RuntimeEval script state flags ctx first) (b : RuntimeEval script state flags ctx second) :
    first = second := by
  exact (runtime_model_iff.mp a).symm.trans (runtime_model_iff.mp b)

/-- A bounded initial state and successful execution imply a bounded final
    state; `runtimeStep_stackBound` covers every intermediate transition. -/
theorem RuntimeEval.stackBound {script : Script} {state : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (evaluated : RuntimeEval script state flags ctx (.success stack alt weight))
    (initial : state.stack.length + state.altStack.length ≤ maxStackSize) :
    stack.length + alt.length ≤ maxStackSize := by
  generalize resultEq : WeightedResult.success stack alt weight = result at evaluated
  induction evaluated with
  | done state flags ctx =>
      unfold finishRuntime at resultEq
      split at resultEq
      · cases resultEq; exact initial
      · contradiction
  | error => cases resultEq
  | step stepped tail ih => exact ih (runtimeStep_stackBound stepped) resultEq


theorem evaluateWithRuntimeLimits_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      evaluateWithRuntimeLimits CryptoOracle.model script stack alt flags ctx weight := by
  exact evaluateRuntime_eq_of_eval agreement
    (evaluateRuntime_sound CryptoOracle.model_refines script _ flags ctx)

theorem evaluateWithRuntimeLimits_bounds
    {oracle : CryptoOracle}
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (initial : stack.length + alt.length ≤ maxStackSize)
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    finalStack.length + finalAlt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  exact evaluateRuntime_bounds script initial success

end LeanMiniscript.Script
