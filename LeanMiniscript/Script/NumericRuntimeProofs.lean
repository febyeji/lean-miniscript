import LeanMiniscript.Script.RuntimeLimits

namespace LeanMiniscript.Script

/-- The four unary arithmetic and six binary arithmetic/comparison opcodes
    covered by the grouped runtime invariants below. -/
def Opcode.isNumericExtension (opcode : Opcode) : Bool :=
  match opcode with
  | .OP_1ADD | .OP_1SUB | .OP_NEGATE | .OP_ABS
  | .OP_SUB | .OP_NUMNOTEQUAL | .OP_LESSTHAN | .OP_GREATERTHAN
  | .OP_LESSTHANOREQUAL | .OP_GREATERTHANOREQUAL => true
  | _ => false

/-- Active 1ADD preserves the alternate stack, conditions and weight.
    Underflow and input decode errors precede the shared resource check. -/
theorem executeRuntimeElement_oneAdd (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_1ADD) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value => .ok { state with stack := scriptNum (value + 1) :: rest } := by
  cases stackEq : state.stack with
  | nil =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_oneAdd, stackEq]
      rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          active, prepareValidationWeight, evaluate_oneAdd, stackEq, decoded] <;> rfl

/-- The unary result is accepted exactly when the unchanged combined stack
    count fits. Numeric errors are returned before that count is checked. -/
theorem runtimeStep_oneAdd (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_1ADD) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (value + 1) :: rest } := by
  rw [runtimeStep, executeRuntimeElement_oneAdd oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active 1SUB preserves the alternate stack, conditions and weight.
    Underflow and input decode errors precede the shared resource check. -/
theorem executeRuntimeElement_oneSub (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_1SUB) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value => .ok { state with stack := scriptNum (value - 1) :: rest } := by
  cases stackEq : state.stack with
  | nil =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_oneSub, stackEq]
      rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          active, prepareValidationWeight, evaluate_oneSub, stackEq, decoded] <;> rfl

/-- The unary result is accepted exactly when the unchanged combined stack
    count fits. Numeric errors are returned before that count is checked. -/
theorem runtimeStep_oneSub (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_1SUB) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (value - 1) :: rest } := by
  rw [runtimeStep, executeRuntimeElement_oneSub oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active NEGATE preserves the alternate stack, conditions and weight.
    Underflow and input decode errors precede the shared resource check. -/
theorem executeRuntimeElement_negate (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_NEGATE) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value => .ok { state with stack := scriptNum (-value) :: rest } := by
  cases stackEq : state.stack with
  | nil =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_negate, stackEq]
      rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          active, prepareValidationWeight, evaluate_negate, stackEq, decoded] <;> rfl

/-- The unary result is accepted exactly when the unchanged combined stack
    count fits. Numeric errors are returned before that count is checked. -/
theorem runtimeStep_negate (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_NEGATE) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (-value) :: rest } := by
  rw [runtimeStep, executeRuntimeElement_negate oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active ABS preserves the alternate stack, conditions and weight.
    Underflow and input decode errors precede the shared resource check. -/
theorem executeRuntimeElement_abs (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_ABS) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value => .ok { state with stack := scriptNum (if value < 0 then -value else value) :: rest } := by
  cases stackEq : state.stack with
  | nil =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_abs, stackEq]
      rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
          active, prepareValidationWeight, evaluate_abs, stackEq, decoded] <;> rfl

/-- The unary result is accepted exactly when the unchanged combined stack
    count fits. Numeric errors are returned before that count is checked. -/
theorem runtimeStep_abs (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_ABS) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (if value < 0 then -value else value) :: rest } := by
  rw [runtimeStep, executeRuntimeElement_abs oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active SUB decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_sub (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_SUB) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := scriptNum (b - a) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_sub, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_sub, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_sub, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_sub (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_SUB) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := scriptNum (b - a) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_sub oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active NUMNOTEQUAL decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_numNotEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_NUMNOTEQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := boolToElement (decide (a ≠ b)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_numNotEqual, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_numNotEqual, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_numNotEqual, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_numNotEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_NUMNOTEQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (a ≠ b)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_numNotEqual oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active LESSTHAN decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_lessThan (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_LESSTHAN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := boolToElement (decide (b < a)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_lessThan, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_lessThan, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_lessThan, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_lessThan (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_LESSTHAN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (b < a)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_lessThan oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active GREATERTHAN decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_greaterThan (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_GREATERTHAN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := boolToElement (decide (b > a)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_greaterThan, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_greaterThan, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_greaterThan, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_greaterThan (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_GREATERTHAN) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (b > a)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_greaterThan oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active LESSTHANOREQUAL decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_lessThanOrEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_LESSTHANOREQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := boolToElement (decide (b ≤ a)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_lessThanOrEqual, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_lessThanOrEqual, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_lessThanOrEqual, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_lessThanOrEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_LESSTHANOREQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (b ≤ a)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_lessThanOrEqual oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Active GREATERTHANOREQUAL decodes below-top before top and replaces two inputs
    with one result, preserving the alternate stack, conditions and weight. -/
theorem executeRuntimeElement_greaterThanOrEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    executeRuntimeElement oracle (.op .OP_GREATERTHANOREQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) => .ok { state with stack := boolToElement (decide (b ≥ a)) :: rest }
      | _ => .error .stackUnderflow := by
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
    active, prepareValidationWeight, evaluate_greaterThanOrEqual, stackEq]; rfl }
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_greaterThanOrEqual, stackEq, decoded]
      rfl
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize,
        active, prepareValidationWeight, evaluate_greaterThanOrEqual, stackEq, decoded]
      rfl

/-- Binary arithmetic/comparison errors precede the resource check. A successful
    decode removes one main-stack item before checking combined stack depth. -/
theorem runtimeStep_greaterThanOrEqual (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_GREATERTHANOREQUAL) state flags ctx =
      match state.stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .error error
          | .ok (a, b) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (b ≥ a)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_greaterThanOrEqual oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try rfl
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨a, b⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- Inactive numeric opcodes preserve every field even with malformed operands. -/
theorem executeRuntimeElement_numericExtension_inactive (oracle : CryptoOracle)
    (opcode : Opcode) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (numeric : opcode.isNumericExtension = true)
    (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op opcode) state flags ctx = .ok state := by
  cases opcode <;> simp_all [Opcode.isNumericExtension, executeRuntimeElement,
    ScriptElement.pushSize, maxScriptElementSize] <;> rfl

/-- Inactive numeric instructions still visit the shared combined-stack check. -/
theorem runtimeStep_numericExtension_inactive (oracle : CryptoOracle)
    (opcode : Opcode) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (numeric : opcode.isNumericExtension = true)
    (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op opcode) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep,
    executeRuntimeElement_numericExtension_inactive oracle opcode state flags ctx numeric inactive]
  rfl

/-- Successful numeric execution preserves all fields outside the main stack.
    Its length is unchanged for unary or inactive instructions and decreases
    by one for active binary instructions. -/
theorem executeRuntimeElement_numericExtension_preserves (oracle : CryptoOracle)
    (opcode : Opcode) (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (numeric : opcode.isNumericExtension = true)
    (executed : executeRuntimeElement oracle (.op opcode) state flags ctx = .ok next) :
    next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight ∧
      next.stack.length +
        (if state.conditions.all id && !opcode.usesUnaryArithmetic then 1 else 0) =
        state.stack.length := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_numericExtension_inactive oracle opcode state flags ctx
        numeric active] at executed
      cases executed
      simp
  | true =>
      cases opcode <;> simp_all only [Opcode.isNumericExtension, Bool.false_eq_true]
      case OP_1ADD =>
        rw [executeRuntimeElement_oneAdd oracle state flags ctx active] at executed
        cases stackEq : state.stack with
        | nil => simp [stackEq] at executed
        | cons operand rest =>
            cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
              simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_1SUB =>
        rw [executeRuntimeElement_oneSub oracle state flags ctx active] at executed
        cases stackEq : state.stack with
        | nil => simp [stackEq] at executed
        | cons operand rest =>
            cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
              simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_NEGATE =>
        rw [executeRuntimeElement_negate oracle state flags ctx active] at executed
        cases stackEq : state.stack with
        | nil => simp [stackEq] at executed
        | cons operand rest =>
            cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
              simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_ABS =>
        rw [executeRuntimeElement_abs oracle state flags ctx active] at executed
        cases stackEq : state.stack with
        | nil => simp [stackEq] at executed
        | cons operand rest =>
            cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
              simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_SUB =>
        rw [executeRuntimeElement_sub oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_NUMNOTEQUAL =>
        rw [executeRuntimeElement_numNotEqual oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_LESSTHAN =>
        rw [executeRuntimeElement_lessThan oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_GREATERTHAN =>
        rw [executeRuntimeElement_greaterThan oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_LESSTHANOREQUAL =>
        rw [executeRuntimeElement_lessThanOrEqual oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]
      case OP_GREATERTHANOREQUAL =>
        rw [executeRuntimeElement_greaterThanOrEqual oracle state flags ctx active] at executed
        rcases stackEq : state.stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
        all_goals try { simp [stackEq] at executed }
        cases decoded : decodeBinaryScriptNums flags top belowTop with
        | error error => simp [stackEq, decoded] at executed
        | ok values =>
            rcases values with ⟨a, b⟩
            simp [stackEq, decoded] at executed
            cases executed
            simp [Opcode.usesUnaryArithmetic]

/-- The post-instruction resource check retains numeric stack-length and
    runtime-field invariants. -/
theorem runtimeStep_numericExtension_preserves (oracle : CryptoOracle)
    (opcode : Opcode) (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (numeric : opcode.isNumericExtension = true)
    (stepped : runtimeStep oracle (.op opcode) state flags ctx = .ok next) :
    next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight ∧
      next.stack.length +
        (if state.conditions.all id && !opcode.usesUnaryArithmetic then 1 else 0) =
        state.stack.length := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op opcode) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_numericExtension_preserves oracle opcode state middle flags ctx
        numeric executed

end LeanMiniscript.Script
