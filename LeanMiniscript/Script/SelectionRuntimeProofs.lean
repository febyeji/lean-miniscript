import LeanMiniscript.Script.RuntimeLimitsProofs

namespace LeanMiniscript.Script

/-- Numeric extrema and depth-indexed stack selection operations. -/
def Opcode.isSelection (opcode : Opcode) : Bool :=
  match opcode with
  | .OP_MIN | .OP_MAX | .OP_PICK | .OP_ROLL => true
  | _ => false

/-- Active MIN decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_min (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_MIN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := scriptNum (min b a) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_min, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_min, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_min, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_min (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_MIN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (min b a) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_min oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active MAX decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_max (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_MAX) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := scriptNum (max b a) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_max, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_max, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_max, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_max (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_MAX) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (max b a) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_max oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active PICK consumes the depth operand and preserves the remaining runtime fields. -/
theorem executeRuntimeElement_pick (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_PICK) state flags ctx =
      match state.stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .error error
          | .ok index => .ok { state with
              stack := (top :: rest)[index]?.getD ByteArray.empty :: (top :: rest) }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_pick, stackEq]; rfl }
  cases decoded : decodeStackIndex flags operand (rest.length + 1) <;>
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_pick, stackEq, decoded] <;> rfl

/-- PICK checks combined stack depth after successful selection. Arity, number,
    and index-range errors take precedence over the resource check. -/
theorem runtimeStep_pick (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_PICK) state flags ctx =
      match state.stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .error error
          | .ok index =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with
                stack := (top :: rest)[index]?.getD ByteArray.empty :: (top :: rest) }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_pick oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeStackIndex flags operand (rest.length + 1) with
  | error error => simp [decoded, bind, Except.bind]
  | ok index =>
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active ROLL consumes the depth operand and preserves the remaining runtime fields. -/
theorem executeRuntimeElement_roll (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_ROLL) state flags ctx =
      match state.stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .error error
          | .ok index => .ok { state with
              stack := (top :: rest)[index]?.getD ByteArray.empty :: (top :: rest).eraseIdx index }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_roll, stackEq]; rfl }
  cases decoded : decodeStackIndex flags operand (rest.length + 1) <;>
    simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
      active, prepareValidationWeight, evaluate_roll, stackEq, decoded] <;> rfl

/-- ROLL checks combined stack depth after successful selection. Arity, number,
    and index-range errors take precedence over the resource check. -/
theorem runtimeStep_roll (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_ROLL) state flags ctx =
      match state.stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .error error
          | .ok index =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with
                stack := (top :: rest)[index]?.getD ByteArray.empty :: (top :: rest).eraseIdx index }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_roll oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeStackIndex flags operand (rest.length + 1) with
  | error error => simp [decoded, bind, Except.bind]
  | ok index =>
      have valid : index < (top :: rest).length := decodeStackIndex_ok_lt decoded
      simp [decoded, bind, Except.bind, checkRuntimeStack,
        List.length_eraseIdx_of_lt valid]

/-- Inactive selection instructions retain the complete runtime state. -/
theorem executeRuntimeElement_selection_inactive (oracle : CryptoOracle)
    (opcode : Opcode) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (selection : opcode.isSelection = true)
    (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op opcode) state flags ctx = .ok state := by
  cases opcode <;> simp_all [Opcode.isSelection, executeRuntimeElement,
    ScriptElement.pushSize, maxScriptElementSize] <;> rfl

/-- Inactive selection instructions still check the combined stack limit. -/
theorem runtimeStep_selection_inactive (oracle : CryptoOracle)
    (opcode : Opcode) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (selection : opcode.isSelection = true)
    (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep,
    executeRuntimeElement_selection_inactive oracle opcode state flags ctx selection inactive]
  rfl

/-- Successful selection preserves the alternate stack, conditions, and weight.
    Active MIN, MAX, and ROLL remove one stack item; PICK retains the input count. -/
theorem executeRuntimeElement_selection_preserves (oracle : CryptoOracle)
    (opcode : Opcode) (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (selection : opcode.isSelection = true)
    (executed : executeRuntimeElement oracle (.op opcode) state flags ctx = .ok next) :
    next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight ∧
      next.stack.length +
        (if state.conditions.all id && decide (opcode ≠ .OP_PICK) then 1 else 0) =
        state.stack.length := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_selection_inactive oracle opcode state flags ctx
        selection active] at executed
      cases executed
      simp
  | true =>
      cases opcode <;> simp_all only [Opcode.isSelection, Bool.false_eq_true]
      case OP_MIN =>
        rw [executeRuntimeElement_min oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp
      case OP_MAX =>
        rw [executeRuntimeElement_max oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp
      case OP_PICK =>
        rw [executeRuntimeElement_pick oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeStackIndex flags operand (rest.length + 1) with
        | error error => simp [stackEq, decoded] at executed
        | ok index =>
            simp [stackEq, decoded] at executed
            cases executed
            simp
      case OP_ROLL =>
        rw [executeRuntimeElement_roll oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeStackIndex flags operand (rest.length + 1) with
        | error error => simp [stackEq, decoded] at executed
        | ok index =>
            simp [stackEq, decoded] at executed
            cases executed
            have valid : index < (top :: rest).length := decodeStackIndex_ok_lt decoded
            simp [List.length_eraseIdx_of_lt valid]

/-- Successful resource checks retain the selection stack-length and field invariants. -/
theorem runtimeStep_selection_preserves (oracle : CryptoOracle)
    (opcode : Opcode) (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (selection : opcode.isSelection = true)
    (stepped : runtimeStep oracle (.op opcode) state flags ctx = .ok next) :
    next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight ∧
      next.stack.length +
        (if state.conditions.all id && decide (opcode ≠ .OP_PICK) then 1 else 0) =
        state.stack.length := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op opcode) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_selection_preserves oracle opcode state middle flags ctx
        selection executed

end LeanMiniscript.Script
