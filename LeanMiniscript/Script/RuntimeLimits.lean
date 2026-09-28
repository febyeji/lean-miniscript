import LeanMiniscript.Script.ValidationWeightCore

namespace LeanMiniscript.Script

/-!
Runtime limits for the modeled opcode subset. Instructions are visited in source
order, including inactive branches: oversized pushes fail when encountered,
while signature debits and ordinary opcode execution only occur in active code.
The branch-projection evaluator remains available for budget-only reasoning.
-/

/-- Runtime state; the condition list is innermost-first. -/
structure RuntimeState where
  stack : Stack
  altStack : Stack
  conditions : List Bool := []
  weight : Nat
  deriving Repr

/-- Numeric pushes use the same byte representation as canonical serialization. -/
def ScriptElement.pushSize : ScriptElement → Nat
  | .pushData bytes => bytes.size
  | .pushNum number => (scriptNum number).size
  | .op _ => 0

/-- Core checks combined main/alt-stack depth after each visited instruction. -/
def checkRuntimeStack (state : RuntimeState) : Except ScriptError RuntimeState :=
  if state.stack.length + state.altStack.length > maxStackSize then .error .stackSize
  else .ok state

theorem checkRuntimeStack_ok {before after : RuntimeState}
    (checked : checkRuntimeStack before = .ok after) :
    after = before ∧ after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold checkRuntimeStack at checked
  split at checked
  · contradiction
  · cases checked
    exact ⟨rfl, by omega⟩

/-- One source instruction, before the combined stack check. Push size precedes
    control handling and execution, including in an inactive branch. -/
def executeRuntimeElement (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  if element.pushSize > maxScriptElementSize then throw .pushSize
  let active := state.conditions.all id
  match element with
  | .op .OP_IF | .op .OP_NOTIF =>
      if active then
        match state.stack with
        | [] => throw .stackUnderflow
        | top :: rest =>
            if minimalIfSatisfied flags ctx.sigVersion top then
              return { state with
                stack := rest
                conditions := element.branchChoice top :: state.conditions }
            else throw (minimalIfError ctx.sigVersion)
      else return { state with conditions := false :: state.conditions }
  | .op .OP_ELSE =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | first :: rest => return { state with conditions := (!first) :: rest }
  | .op .OP_ENDIF =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | _ :: rest => return { state with conditions := rest }
  | _ =>
      if active then
        let weight ← prepareValidationWeight element state.stack flags ctx state.weight
        match evaluate oracle [element] state.stack state.altStack flags ctx with
        | .failure error => throw error
        | .success stack alt => return { state with stack := stack, altStack := alt, weight := weight }
      else return state

/-- Shared step boundary: opcode errors precede the post-instruction stack limit. -/
def runtimeStep (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  let next ← executeRuntimeElement oracle element state flags ctx
  checkRuntimeStack next

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
theorem runtimeStep_depth (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_DEPTH) state flags ctx =
      if state.stack.length + state.altStack.length < maxStackSize then
        .ok { state with stack := scriptNat state.stack.length :: state.stack }
      else .error .stackSize := by
  rw [runtimeStep, executeRuntimeElement_depth oracle state flags ctx active]
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

/-- Inactive NOT leaves the entire state unchanged, including malformed operands. -/
theorem executeRuntimeElement_not_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_NOT) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
  rfl

/-- Every successful NOT step before resource checking preserves stack count,
    alternate stack, conditions and signature budget, in active or inactive code. -/
theorem executeRuntimeElement_not_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (executed : executeRuntimeElement oracle (.op .OP_NOT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧ next.altStack = state.altStack ∧
      next.conditions = state.conditions ∧ next.weight = state.weight := by
  cases active : state.conditions.all id with
  | false =>
      rw [executeRuntimeElement_not_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_not (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_NOT) state flags ctx =
      match state.stack with
      | [] => .error .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .error error
          | .ok value =>
              if state.stack.length + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (value == 0) :: rest } := by
  rw [runtimeStep, executeRuntimeElement_not oracle state flags ctx active]
  cases stackEq : state.stack with
  | nil => rfl
  | cons operand rest =>
      cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes <;>
        simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- The post-instruction stack check preserves the same NOT state invariants. -/
theorem runtimeStep_not_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_NOT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧ next.altStack = state.altStack ∧
      next.conditions = state.conditions ∧ next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_NOT) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_not_preserves oracle state middle flags ctx executed

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

/-- Inactive WITHIN leaves the entire state unchanged, including malformed or
    missing operands. -/
theorem executeRuntimeElement_within_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_WITHIN) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_within_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_within (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_WITHIN) state flags ctx =
      match state.stack with
      | upperBytes :: lowerBytes :: valueBytes :: rest =>
          match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
          | .error error => .error error
          | .ok (upper, lower, value) =>
              if rest.length + 1 + state.altStack.length > maxStackSize then
                .error .stackSize
              else .ok { state with stack := boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_within oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨upperBytes, _ | ⟨lowerBytes, _ | ⟨valueBytes, rest⟩⟩⟩
  all_goals try rfl
  cases decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
  | error error => simp [decoded, bind, Except.bind]
  | ok values =>
      rcases values with ⟨upper, lower, value⟩
      simp [decoded, bind, Except.bind, checkRuntimeStack]

/-- An inactive WITHIN still performs the shared post-instruction stack check. -/
theorem runtimeStep_within_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_WITHIN) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_within_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction resource check retains WITHIN's state invariants. -/
theorem runtimeStep_within_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_WITHIN) state flags ctx = .ok next) :
    next.stack.length + (if state.conditions.all id then 2 else 0) = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_WITHIN) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_within_preserves oracle state middle flags ctx executed


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

/-- Inactive NIP leaves the entire runtime state unchanged, for every stack. -/
theorem executeRuntimeElement_nip_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_NIP) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_nip_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_nip (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_NIP) state flags ctx =
      match state.stack with
      | top :: _ :: rest =>
          if rest.length + 1 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_nip oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack]

/-- An inactive NIP still performs the shared combined-stack check. -/
theorem runtimeStep_nip_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_NIP) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_nip_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction stack check retains NIP's state invariants. -/
theorem runtimeStep_nip_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_NIP) state flags ctx = .ok next) :
    next.stack.length + (if state.conditions.all id then 1 else 0) = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_NIP) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_nip_preserves oracle state middle flags ctx executed

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

/-- Inactive 2DUP leaves the entire runtime state unchanged, for every stack. -/
theorem executeRuntimeElement_twoDup_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_2DUP) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_twoDup_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_twoDup (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_2DUP) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 4 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_twoDup oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- An inactive 2DUP still performs the shared combined-stack check. -/
theorem runtimeStep_twoDup_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_2DUP) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_twoDup_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction stack check retains 2DUP's state invariants. -/
theorem runtimeStep_twoDup_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_2DUP) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 2 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_2DUP) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_twoDup_preserves oracle state middle flags ctx executed

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

/-- Inactive OVER leaves the entire runtime state unchanged, for every stack. -/
theorem executeRuntimeElement_over_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_OVER) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_over_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_over (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_OVER) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := below :: top :: below :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_over oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- An inactive OVER still performs the shared combined-stack check. -/
theorem runtimeStep_over_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_OVER) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_over_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction stack check retains OVER's state invariants. -/
theorem runtimeStep_over_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_OVER) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 1 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_OVER) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_over_preserves oracle state middle flags ctx executed

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

/-- Inactive TUCK leaves the entire runtime state unchanged, for every stack. -/
theorem executeRuntimeElement_tuck_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_TUCK) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_tuck_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_tuck (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_TUCK) state flags ctx =
      match state.stack with
      | top :: below :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := top :: below :: top :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_tuck oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- An inactive TUCK still performs the shared combined-stack check. -/
theorem runtimeStep_tuck_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_TUCK) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_tuck_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction stack check retains TUCK's state invariants. -/
theorem runtimeStep_tuck_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_TUCK) state flags ctx = .ok next) :
    next.stack.length = state.stack.length + (if state.conditions.all id then 1 else 0) ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_TUCK) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_tuck_preserves oracle state middle flags ctx executed

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

/-- Inactive ROT leaves the entire runtime state unchanged, for every stack. -/
theorem executeRuntimeElement_rot_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    executeRuntimeElement oracle (.op .OP_ROT) state flags ctx = .ok state := by
  simp [executeRuntimeElement, ScriptElement.pushSize, maxScriptElementSize, inactive]
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
      rw [executeRuntimeElement_rot_inactive oracle state flags ctx active] at executed
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
theorem runtimeStep_rot (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (active : state.conditions.all id = true) :
    runtimeStep oracle (.op .OP_ROT) state flags ctx =
      match state.stack with
      | top :: second :: third :: rest =>
          if rest.length + 3 + state.altStack.length > maxStackSize then
            .error .stackSize
          else .ok { state with stack := third :: top :: second :: rest }
      | _ => .error .stackUnderflow := by
  rw [runtimeStep, executeRuntimeElement_rot oracle state flags ctx active]
  rcases stackEq : state.stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp [bind, Except.bind, checkRuntimeStack, Nat.add_assoc]

/-- An inactive ROT still performs the shared combined-stack check. -/
theorem runtimeStep_rot_inactive (oracle : CryptoOracle) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) (inactive : state.conditions.all id = false) :
    runtimeStep oracle (.op .OP_ROT) state flags ctx = checkRuntimeStack state := by
  rw [runtimeStep, executeRuntimeElement_rot_inactive oracle state flags ctx inactive]
  rfl

/-- The post-instruction stack check retains ROT's state invariants. -/
theorem runtimeStep_rot_preserves (oracle : CryptoOracle)
    (state next : RuntimeState) (flags : ScriptFlags) (ctx : TxContext)
    (stepped : runtimeStep oracle (.op .OP_ROT) state flags ctx = .ok next) :
    next.stack.length = state.stack.length ∧
      next.altStack = state.altStack ∧ next.conditions = state.conditions ∧
      next.weight = state.weight := by
  unfold runtimeStep at stepped
  cases executed : executeRuntimeElement oracle (.op .OP_ROT) state flags ctx with
  | error error => simp [executed, bind, Except.bind] at stepped
  | ok middle =>
      simp only [executed, bind, Except.bind] at stepped
      have same := (checkRuntimeStack_ok stepped).1
      subst next
      exact executeRuntimeElement_rot_preserves oracle state middle flags ctx executed

theorem runtimeStep_stackBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    after.stack.length + after.altStack.length ≤ maxStackSize := by
  unfold runtimeStep at stepped
  cases computed : executeRuntimeElement oracle element before flags ctx with
  | error error => simp [computed, bind, Except.bind] at stepped
  | ok next =>
      simp only [computed, bind, Except.bind] at stepped
      exact (checkRuntimeStack_ok stepped).2

/-- Every visited instruction, active or skipped, passes the push-size bound. -/
theorem runtimeStep_pushBound
    {oracle : CryptoOracle} {element : ScriptElement} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (stepped : runtimeStep oracle element before flags ctx = .ok after) :
    element.pushSize ≤ maxScriptElementSize := by
  by_cases exceeded : element.pushSize > maxScriptElementSize
  · simp [runtimeStep, executeRuntimeElement, exceeded, bind, Except.bind] at stepped
  · exact Nat.le_of_not_gt exceeded

/-- Resource and control checks do not weaken the existing crypto boundary. -/
theorem runtimeStep_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle element state flags ctx =
      runtimeStep CryptoOracle.model element state flags ctx := by
  have opcode := evaluate_eq_of_eval agreement
    (evaluate_sound CryptoOracle.model_refines [element] state.stack state.altStack flags ctx)
  simp only [runtimeStep, executeRuntimeElement, opcode]

/-- EOF reports an unclosed conditional only after earlier runtime checks pass. -/
def finishRuntime (state : RuntimeState) : WeightedResult :=
  if state.conditions.isEmpty then .success state.stack state.altStack state.weight
  else .failure .unbalancedConditional

/-- Structural recursion over literal source order retains inactive push checks. -/
def evaluateRuntime (oracle : CryptoOracle) : Script → RuntimeState →
    ScriptFlags → TxContext → WeightedResult
  | [], state, _, _ => finishRuntime state
  | element :: rest, state, flags, ctx =>
      match runtimeStep oracle element state flags ctx with
      | .error error => .failure error
      | .ok next => evaluateRuntime oracle rest next flags ctx

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

/-- The modeled relation composes source-order steps and final condition checks.
    Its step function uses the abstract crypto oracle, whose active opcode
    behavior is supplied by the existing evaluator/`Eval` refinement theorem. -/
inductive RuntimeEval : Script → RuntimeState → ScriptFlags → TxContext → WeightedResult → Prop where
  | done (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
      RuntimeEval [] state flags ctx (finishRuntime state)
  | error {element : ScriptElement} {rest : Script} {state : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
      (failed : runtimeStep CryptoOracle.model element state flags ctx = .error error) :
      RuntimeEval (element :: rest) state flags ctx (.failure error)
  | step {element : ScriptElement} {rest : Script} {state next : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {result : WeightedResult}
      (stepped : runtimeStep CryptoOracle.model element state flags ctx = .ok next)
      (tail : RuntimeEval rest next flags ctx result) :
      RuntimeEval (element :: rest) state flags ctx result

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

/-- Runtime-limited execution starts with no open conditional. The caller
    checks initial witness bounds; the full-witness entry does so explicitly. -/
def evaluateWithRuntimeLimits (oracle : CryptoOracle) (script : Script)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) : WeightedResult :=
  evaluateRuntime oracle script { stack := stack, altStack := alt, weight := weight } flags ctx

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
