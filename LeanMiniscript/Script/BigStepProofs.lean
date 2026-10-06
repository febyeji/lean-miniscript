import LeanMiniscript.Script.BigStep

/-! Composition, determinism, totality and opcode results for big-step execution. -/

namespace LeanMiniscript.Script

/-- Evaluation composes over script concatenation. Keeping sequencing as a
    theorem avoids adding a non-opcode case to every induction over `Eval`. -/
theorem Eval.append
    {left right : Script} {stack midStack altStack midAltStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (leftEval : Eval left stack altStack flags ctx (.success midStack midAltStack))
    (rightEval : Eval right midStack midAltStack flags ctx result) :
    Eval (left ++ right) stack altStack flags ctx result := by
  generalize resultEq : ExecResult.success midStack midAltStack = leftResult at leftEval
  induction leftEval generalizing right result
  case if_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  case notif_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  all_goals cases resultEq <;>
    simp_all <;>
    try grind [Eval]
  case within.refl =>
    rename_i upperBytes lowerBytes valueBytes upper lower value rest alt script flags ctx decoded _ ih
    apply Eval.within upperBytes lowerBytes valueBytes upper lower value rest alt
      (script ++ right) flags ctx result decoded
    simpa using ih rightEval
  case if_execute.refl =>
    rename_i top rest altStack script frame flags ctx split minimal _ ih
    have splitAppended := splitConditional_append_of_some
      (suffix := right) split
    apply Eval.if_execute top rest altStack (script ++ right)
      { frame with after := frame.after ++ right }
      flags ctx result splitAppended minimal
    rw [ConditionalFrame.select_append]
    exact ih rightEval
  case notif_execute.refl =>
    rename_i top rest altStack script frame flags ctx split minimal _ ih
    have splitAppended := splitConditional_append_of_some
      (suffix := right) split
    apply Eval.notif_execute top rest altStack (script ++ right)
      { frame with after := frame.after ++ right }
      flags ctx result splitAppended minimal
    rw [ConditionalFrame.select_append]
    exact ih rightEval

/-! ## Proof-facing execution API

These lemmas keep unchanged scripts, stacks, flags, contexts, and results
implicit. Soundness proofs can compose execution steps without repeating the
full constructor argument list.
-/

/-- A fixed-arity opcode fails immediately when its main stack is too short. -/
theorem Eval.fixedArityStackUnderflow
    {opcode : Opcode} {required : Nat} {script : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some required)
    (underflow : stack.length < required) :
    Eval (.op opcode :: script) stack altStack flags ctx
      (.failure .stackUnderflow) :=
  .stack_underflow opcode required script stack altStack flags ctx arity underflow

/-- `OP_FROMALTSTACK` fails immediately when its alternate stack is empty. -/
theorem Eval.fromAltStackUnderflow
    {script : Script} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext} :
    Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx
      (.failure .altStackUnderflow) :=
  .fromaltstack_underflow script stack flags ctx

/-- A malformed operand terminates any ordinary binary numeric opcode before
    the remaining script executes. -/
theorem Eval.binaryScriptNumFailure
    {opcode : Opcode} {top belowTop : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError}
    (usesNumbers : opcode.usesBinaryScriptNums = true)
    (decoded : decodeBinaryScriptNums flags top belowTop = .error error) :
    Eval (.op opcode :: script) (top :: belowTop :: rest) altStack flags ctx
      (.failure error) :=
  .binary_scriptnum_failure opcode top belowTop rest script altStack flags ctx
    error usesNumbers decoded

/-- A malformed operand terminates unary arithmetic before the suffix executes. -/
theorem Eval.unaryArithmeticScriptNumFailure
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError}
    (usesNumber : opcode.usesUnaryArithmetic = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .error error) :
    Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
      (.failure error) :=
  .unaryArithmetic_scriptnum_failure opcode operand rest script altStack flags ctx
    error usesNumber decoded

/-- A malformed CLTV/CSV operand terminates evaluation before the timelock
    predicate is consulted. -/
theorem Eval.timelockScriptNumFailure
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .error error) :
    Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
      (.failure error) :=
  .timelock_scriptnum_failure opcode operand rest script altStack flags ctx
    error usesNumber decoded

/-- A malformed or incomplete legacy multisignature frame terminates before
    signature matching or NULLDUMMY validation. -/
theorem Eval.checkMultiSigOperandFailure
    {stack : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .error error) :
    Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      (.failure error) :=
  .checkmultisig_operand_failure stack script altStack flags ctx error decoded

/-- Main-stack underflow cannot overlap a normal fixed-arity opcode rule. -/
theorem Eval.fixedArityStackUnderflow_result
    {opcode : Opcode} {required : Nat} {script : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some required)
    (underflow : stack.length < required)
    (evaluated : Eval (.op opcode :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow := by
  cases opcode <;> cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- Empty-alt-stack failure cannot overlap normal `OP_FROMALTSTACK` execution. -/
theorem Eval.fromAltStack_empty_result
    {script : Script} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (evaluated : Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx result) :
    result = .failure .altStackUnderflow := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A structurally unclosed IF evaluates its active segments before converting
    a successful EOF into `unbalancedConditional`. -/
theorem Eval.ifUnbalanced_result
    {top : StackElement} {rest altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (split : splitConditional script = none)
    (minimal : minimalIfSatisfied flags ctx.sigVersion top)
    (evaluated : Eval (.op .OP_IF :: script) (top :: rest) altStack flags ctx
      result) :
    ∃ selectedResult,
      Eval (selectUnclosedConditional script (castToBool top)) rest altStack
        flags ctx selectedResult ∧
      result = finishUnclosedConditional selectedResult := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum, minimalIfSatisfied] <;>
    try omega
  case if_unbalanced => exact ⟨_, by assumption, rfl⟩

/-- The corresponding NOTIF rule evaluates the opposite active segments. -/
theorem Eval.notifUnbalanced_result
    {top : StackElement} {rest altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (split : splitConditional script = none)
    (minimal : minimalIfSatisfied flags ctx.sigVersion top)
    (evaluated : Eval (.op .OP_NOTIF :: script) (top :: rest) altStack flags ctx
      result) :
    ∃ selectedResult,
      Eval (selectUnclosedConditional script (!castToBool top)) rest altStack
        flags ctx selectedResult ∧
      result = finishUnclosedConditional selectedResult := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum, minimalIfSatisfied] <;>
    try omega
  case notif_unbalanced => exact ⟨_, by assumption, rfl⟩

/-- ELSE at top level cannot overlap a normal execution rule. -/
theorem Eval.elseUnbalanced_result
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (evaluated : Eval (.op .OP_ELSE :: script) stack altStack flags ctx result) :
    result = .failure .unbalancedConditional := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- ENDIF at top level cannot overlap a normal execution rule. -/
theorem Eval.endifUnbalanced_result
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (evaluated : Eval (.op .OP_ENDIF :: script) stack altStack flags ctx result) :
    result = .failure .unbalancedConditional := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A decoder error cannot overlap a normal binary numeric execution rule. -/
theorem Eval.binaryScriptNumFailure_result
    {opcode : Opcode} {top belowTop : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesNumbers : opcode.usesBinaryScriptNums = true)
    (decoded : decodeBinaryScriptNums flags top belowTop = .error error)
    (evaluated : Eval (.op opcode :: script) (top :: belowTop :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases opcode <;> simp_all [Opcode.usesBinaryScriptNums]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A decoder error cannot overlap normal `OP_0NOTEQUAL` execution. -/
theorem Eval.unaryScriptNumFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .error error)
    (evaluated : Eval (.op .OP_0NOTEQUAL :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A malformed CHECKSIGADD count fails before signature evaluation. -/
theorem Eval.checksigaddScriptNumFailure_result
    {pubkey countBytes sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (available : ctx.sigVersion = .tapscript)
    (decoded : decodeCheckSigAddCount flags ctx countBytes = .error error)
    (evaluated : Eval (.op .OP_CHECKSIGADD :: script)
      (pubkey :: countBytes :: sig :: rest) altStack flags ctx result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum, decodeCheckSigAddCount] <;>
    omega

/-- A legacy multisignature operand-decoder error cannot overlap a normal
    CHECKMULTISIG execution or NULLDUMMY failure. -/
theorem Eval.checkMultiSigOperandFailure_result
    {stack : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
    {result : ExecResult}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .error error)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A non-null dummy fails only after successful matching, or after rejected
    matching has passed NULLFAIL. Encoding failures take precedence. -/
theorem Eval.checkMultiSigNullDummyFailure_result
    {stack : Stack} {operands : CheckMultiSigOperands} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext} {checked : Bool}
    {result : ExecResult}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands)
    (verified : checkMultiSigFor checkSig flags ctx
      operands.signatures operands.pubkeys = .ok checked)
    (allowed : checked = true ∨ nullFailSatisfied flags operands.signatures)
    (invalidDummy : checkMultiSigDummy flags operands.dummy = .error .nullDummy)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      result) :
    result = .failure .nullDummy := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    try omega <;> grind

/-- A decoder error cannot overlap normal CLTV/CSV execution or the separate
    negative-locktime failure. -/
theorem Eval.timelockScriptNumFailure_result
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .error error)
    (evaluated : Eval (.op opcode :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases opcode <;> simp_all [Opcode.usesTimelockScriptNum]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A decoded negative timelock operand fails before either opcode consults
    its transaction-context predicate. -/
theorem Eval.timelockNegativeFailure_result
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {value : Int} {result : ExecResult}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (negative : value < 0)
    (evaluated : Eval (.op opcode :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure .negativeLocktime := by
  cases opcode <;> simp_all [Opcode.usesTimelockScriptNum]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A nonnegative CSV operand that fails the BIP 68/112 context conditions
    cannot overlap CSV success or an earlier numeric failure. -/
theorem Eval.checkSequenceVerifyFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {value : Int} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (nonnegative : 0 ≤ value)
    (unsatisfied : ¬ sequenceSatisfied value.toNat ctx)
    (evaluated : Eval (.op .OP_CHECKSEQUENCEVERIFY :: script)
      (operand :: rest) altStack flags ctx result) :
    result = .failure .checkSequenceVerify := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A nonnegative CLTV operand that fails the BIP 65 context conditions cannot
    overlap CLTV success or an earlier numeric failure. -/
theorem Eval.checkLockTimeVerifyFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {value : Int} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (nonnegative : 0 ≤ value)
    (unsatisfied : ¬ locktimeSatisfied value.toNat ctx)
    (evaluated : Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script)
      (operand :: rest) altStack flags ctx result) :
    result = .failure .checkLockTimeVerify := by
  cases evaluated <;>
    simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum] <;>
    omega

set_option maxHeartbeats 400000 in
/-- Big-step evaluation has at most one result for fixed script, stacks, flags,
    and transaction context. -/
theorem Eval.result_unique
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {firstResult secondResult : ExecResult}
    (first : Eval script stack altStack flags ctx firstResult)
    (second : Eval script stack altStack flags ctx secondResult) :
    firstResult = secondResult := by
  -- Exhaustive constructor comparison is intentional: adding an execution
  -- rule must reopen the corresponding determinism obligations.
  induction first generalizing secondResult <;> cases second
  all_goals
    try simp_all [Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums, Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.isUpgradeableNop,
      Opcode.usesTimelockScriptNum, minimalIfSatisfied, decodeCheckSigAddCount]
    try omega
    try solve_by_elim
    try grind

/-- Index decoding and range errors terminate either indexed stack operation. -/
theorem Eval.stackIndexFailure
    (opcode : Opcode) (operand top : StackElement) (rest : Stack)
    (script : Script) (altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (error : ScriptError) (usesIndex : opcode.usesStackIndex = true)
    (decoded : decodeStackIndex flags operand (top :: rest).length = .error error) :
    Eval (.op opcode :: script) (operand :: top :: rest) altStack flags ctx
      (.failure error) :=
  .stackindex_failure opcode operand top rest script altStack flags ctx error
    usesIndex decoded

/-- An indexed stack operation's decoder error determines its terminal result. -/
theorem Eval.stackIndexFailure_result
    {opcode : Opcode} {operand top : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesIndex : opcode.usesStackIndex = true)
    (decoded : decodeStackIndex flags operand (top :: rest).length = .error error)
    (evaluated : Eval (.op opcode :: script) (operand :: top :: rest)
      altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.stackindex_failure opcode operand top rest script altStack flags ctx
      error usesIndex decoded)

/-- A unary arithmetic decoder error determines the unique terminal result. -/
theorem Eval.unaryArithmeticScriptNumFailure_result
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesNumber : opcode.usesUnaryArithmetic = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .error error)
    (evaluated : Eval (.op opcode :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.unaryArithmetic_scriptnum_failure opcode operand rest script altStack flags ctx
      error usesNumber decoded)

/-- A checked CHECKSIG error is its unique terminal result. -/
theorem Eval.checksigEncodingFailure_result
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error error)
    (evaluated : Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest)
      altStack flags ctx result) :
    result = .failure error :=
  Eval.result_unique evaluated
    (.checksig_encoding_failure pubkey sig rest script altStack flags ctx error checked)

/-- CHECKMULTISIG matching reports a unique terminal encoding error. -/
theorem Eval.checkMultiSigEncodingFailure_result
    {stack : Stack} {operands : CheckMultiSigOperands} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands)
    (encoded : checkMultiSigFor checkSig flags ctx
      operands.signatures operands.pubkeys = .error error)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx result) :
    result = .failure error :=
  Eval.result_unique evaluated
    (.checkmultisig_encoding_failure stack operands script altStack flags ctx error
      decoded encoded)

/-- A decoded CHECKMULTISIG frame with rejected nonempty signatures has only
    the NULLFAIL result. -/
theorem Eval.checkMultiSigNullFailFailure_result
    {stack : Stack} {operands : CheckMultiSigOperands} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands)
    (checked : checkMultiSigFor checkSig flags ctx
      operands.signatures operands.pubkeys = .ok false)
    (nullFail : ¬ nullFailSatisfied flags operands.signatures)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      result) :
    result = .failure .sigNullFail :=
  Eval.result_unique evaluated
    (.checkmultisig_nullfail_failure stack operands script altStack flags ctx
      decoded checked nullFail)

/-- Every script in the modeled opcode subset has an evaluation result.

    Strong induction is needed because a conditional continues with the
    selected branch segments and suffix rather than the literal list tail. -/
theorem Eval.exists_result
    (script : Script) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    ∃ result, Eval script stack altStack flags ctx result := by
  induction hLength : script.length using Nat.strongRecOn
      generalizing script stack altStack with
  | ind length ih =>
      cases script with
      | nil =>
          exact ⟨.success stack altStack, .empty stack altStack flags ctx⟩
      | cons element rest =>
          have restShort : rest.length < length := by
            calc
              rest.length < rest.length + 1 := Nat.lt_succ_self _
              _ = length := hLength
          have next (nextStack nextAltStack : Stack) :
              ∃ result, Eval rest nextStack nextAltStack flags ctx result :=
            ih rest.length restShort rest nextStack nextAltStack rfl
          cases element with
          | pushData data =>
              rcases next (data :: stack) altStack with ⟨result, evaluated⟩
              exact ⟨result, .pushData data rest stack altStack flags ctx result
                evaluated⟩
          | pushNum value =>
              rcases next (scriptNum value :: stack) altStack with
                ⟨result, evaluated⟩
              exact ⟨result, .pushNum value rest stack altStack flags ctx result
                evaluated⟩
          | op opcode =>
              cases opcode with
              | OP_NOP =>
                  rcases next stack altStack with ⟨result, evaluated⟩
                  exact ⟨result, .nop rest stack altStack flags ctx result
                    evaluated⟩
              | OP_NOP1 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP1 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP1 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP4 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP4 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP4 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP5 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP5 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP5 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP6 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP6 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP6 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP7 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP7 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP7 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP8 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP8 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP8 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP9 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP9 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP9 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_NOP10 =>
                  cases discouraged : flags.discourageUpgradableNops with
                  | false =>
                      rcases next stack altStack with ⟨result, evaluated⟩
                      exact ⟨result, .upgradeableNop .OP_NOP10 rest stack altStack
                        flags ctx result rfl discouraged evaluated⟩
                  | true =>
                      exact ⟨.failure .discourageUpgradableNops,
                        .upgradeableNop_discouraged .OP_NOP10 rest stack altStack
                          flags ctx rfl discouraged⟩
              | OP_RETURN =>
                  exact ⟨.failure .opReturn, .opReturn rest stack altStack flags ctx⟩
              | OP_IF =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_IF 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      by_cases minimal : minimalIfSatisfied flags ctx.sigVersion top
                      · cases hSplit : splitConditional rest with
                        | none =>
                            have selectedShort :
                                (selectUnclosedConditional rest
                                  (castToBool top)).length < length := by
                              have smaller := selectUnclosedConditional_length_le
                                rest (castToBool top)
                              omega
                            rcases ih _ selectedShort _ stackRest altStack rfl with
                              ⟨selectedResult, evaluated⟩
                            exact ⟨finishUnclosedConditional selectedResult,
                              .if_unbalanced top stackRest altStack rest flags ctx
                                selectedResult hSplit minimal evaluated⟩
                        | some frame =>
                            have selectedShort :
                                (frame.select (castToBool top)).length < length := by
                              have smaller := frame.select_length_lt hSplit
                                (castToBool top)
                              omega
                            rcases ih _ selectedShort _ stackRest altStack rfl with
                              ⟨result, evaluated⟩
                            exact ⟨result, .if_execute top stackRest altStack rest
                              frame flags ctx result hSplit minimal evaluated⟩
                      · exact ⟨.failure (minimalIfError ctx.sigVersion),
                          .if_minimalif_failure top stackRest altStack rest flags ctx
                            minimal⟩
              | OP_NOTIF =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NOTIF 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      by_cases minimal : minimalIfSatisfied flags ctx.sigVersion top
                      · cases hSplit : splitConditional rest with
                        | none =>
                            have selectedShort :
                                (selectUnclosedConditional rest
                                  (!castToBool top)).length < length := by
                              have smaller := selectUnclosedConditional_length_le
                                rest (!castToBool top)
                              omega
                            rcases ih _ selectedShort _ stackRest altStack rfl with
                              ⟨selectedResult, evaluated⟩
                            exact ⟨finishUnclosedConditional selectedResult,
                              .notif_unbalanced top stackRest altStack rest flags ctx
                                selectedResult hSplit minimal evaluated⟩
                        | some frame =>
                            have selectedShort :
                                (frame.select (!castToBool top)).length < length := by
                              have smaller := frame.select_length_lt hSplit
                                (!castToBool top)
                              omega
                            rcases ih _ selectedShort _ stackRest altStack rfl with
                              ⟨result, evaluated⟩
                            exact ⟨result, .notif_execute top stackRest altStack rest
                              frame flags ctx result hSplit minimal evaluated⟩
                      · exact ⟨.failure (minimalIfError ctx.sigVersion),
                          .notif_minimalif_failure top stackRest altStack rest flags ctx
                            minimal⟩
              | OP_ELSE =>
                  exact ⟨.failure .unbalancedConditional,
                    .else_unbalanced rest stack altStack flags ctx⟩
              | OP_ENDIF =>
                  exact ⟨.failure .unbalancedConditional,
                    .endif_unbalanced rest stack altStack flags ctx⟩
              | OP_IFDUP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_IFDUP 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      cases hTruthy : castToBool top with
                      | false =>
                          rcases next (top :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .ifdup_false top stackRest altStack rest
                            flags ctx result hTruthy evaluated⟩
                      | true =>
                          rcases next (top :: top :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .ifdup_true top stackRest altStack rest
                            flags ctx result hTruthy evaluated⟩
              | OP_DEPTH =>
                  rcases next (scriptNat stack.length :: stack) altStack with
                    ⟨result, evaluated⟩
                  exact ⟨result, .depth stack altStack rest flags ctx result evaluated⟩
              | OP_DROP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_DROP 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next stackRest altStack with ⟨result, evaluated⟩
                      exact ⟨result, .drop top stackRest rest altStack flags ctx result
                        evaluated⟩
              | OP_DUP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_DUP 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (top :: top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .dup top stackRest rest altStack flags ctx result
                        evaluated⟩
              | OP_NIP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NIP 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_NIP 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons discarded stackRest =>
                          rcases next (top :: stackRest) altStack with ⟨result, evaluated⟩
                          exact ⟨result, .nip top discarded stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_2DROP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_2DROP 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_2DROP 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons discarded stackRest =>
                          rcases next stackRest altStack with ⟨result, evaluated⟩
                          exact ⟨result, .twoDrop top discarded stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_2DUP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_2DUP 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_2DUP 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons below stackRest =>
                          rcases next (top :: below :: top :: below :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .twoDup top below stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_3DUP =>
                  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, stackRest⟩⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_3DUP 3 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_3DUP 3 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_3DUP 3 rest _ altStack flags ctx rfl (by simp)⟩
                  · rcases next (top :: second :: third :: top :: second :: third :: stackRest)
                      altStack with ⟨result, evaluated⟩
                    exact ⟨result, .threeDup top second third stackRest altStack
                      rest flags ctx result evaluated⟩
              | OP_2OVER =>
                  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ |
                    ⟨fourth, stackRest⟩⟩⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2OVER 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2OVER 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2OVER 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2OVER 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · rcases next (third :: fourth :: top :: second :: third :: fourth :: stackRest)
                      altStack with ⟨result, evaluated⟩
                    exact ⟨result, .twoOver top second third fourth stackRest altStack
                      rest flags ctx result evaluated⟩
              | OP_OVER =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_OVER 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_OVER 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons below stackRest =>
                          rcases next (below :: top :: below :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .over top below stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_PICK =>
                  rcases stack with _ | ⟨operand, _ | ⟨top, stackRest⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_PICK 2 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_PICK 2 rest _ altStack flags ctx rfl (by simp)⟩
                  · cases decoded : decodeStackIndex flags operand (top :: stackRest).length with
                    | error error =>
                        exact ⟨.failure error,
                          .stackindex_failure .OP_PICK operand top stackRest rest altStack
                            flags ctx error rfl decoded⟩
                    | ok index =>
                        rcases next ((top :: stackRest)[index]?.getD ByteArray.empty ::
                            (top :: stackRest)) altStack with ⟨result, evaluated⟩
                        exact ⟨result, .pick operand top index stackRest altStack rest
                          flags ctx result decoded evaluated⟩
              | OP_ROLL =>
                  rcases stack with _ | ⟨operand, _ | ⟨top, stackRest⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_ROLL 2 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_ROLL 2 rest _ altStack flags ctx rfl (by simp)⟩
                  · cases decoded : decodeStackIndex flags operand (top :: stackRest).length with
                    | error error =>
                        exact ⟨.failure error,
                          .stackindex_failure .OP_ROLL operand top stackRest rest altStack
                            flags ctx error rfl decoded⟩
                    | ok index =>
                        rcases next ((top :: stackRest)[index]?.getD ByteArray.empty ::
                            (top :: stackRest).eraseIdx index) altStack with ⟨result, evaluated⟩
                        exact ⟨result, .roll operand top index stackRest altStack rest
                          flags ctx result decoded evaluated⟩
              | OP_TUCK =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_TUCK 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_TUCK 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons below stackRest =>
                          rcases next (top :: below :: top :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .tuck top below stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_ROT =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_ROT 3 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_ROT 3 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons second stackTail =>
                          cases stackTail with
                          | nil =>
                              exact ⟨.failure .stackUnderflow,
                                .stack_underflow .OP_ROT 3 rest [top, second] altStack
                                  flags ctx rfl (by simp)⟩
                          | cons third stackRest =>
                              rcases next (third :: top :: second :: stackRest) altStack with
                                ⟨result, evaluated⟩
                              exact ⟨result, .rot top second third stackRest altStack rest
                                flags ctx result evaluated⟩
              | OP_2ROT =>
                  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ |
                    ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, stackRest⟩⟩⟩⟩⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2ROT 6 rest _ altStack flags ctx rfl (by simp)⟩
                  · rcases next (fifth :: sixth :: top :: second :: third :: fourth :: stackRest)
                      altStack with ⟨result, evaluated⟩
                    exact ⟨result, .twoRot top second third fourth fifth sixth stackRest altStack
                      rest flags ctx result evaluated⟩
              | OP_2SWAP =>
                  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ |
                    ⟨fourth, stackRest⟩⟩⟩⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2SWAP 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2SWAP 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2SWAP 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · exact ⟨.failure .stackUnderflow,
                      .stack_underflow .OP_2SWAP 4 rest _ altStack flags ctx rfl (by simp)⟩
                  · rcases next (third :: fourth :: top :: second :: stackRest)
                      altStack with ⟨result, evaluated⟩
                    exact ⟨result, .twoSwap top second third fourth stackRest altStack
                      rest flags ctx result evaluated⟩
              | OP_SWAP =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_SWAP 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_SWAP 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          rcases next (belowTop :: top :: stackRest) altStack with
                            ⟨result, evaluated⟩
                          exact ⟨result, .swap top belowTop stackRest altStack rest
                            flags ctx result evaluated⟩
              | OP_TOALTSTACK =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_TOALTSTACK 1 rest [] altStack flags ctx
                          rfl (by simp)⟩
                  | cons top stackRest =>
                      rcases next stackRest (top :: altStack) with
                        ⟨result, evaluated⟩
                      exact ⟨result, .toAltStack top stackRest altStack rest flags ctx
                        result evaluated⟩
              | OP_FROMALTSTACK =>
                  cases altStack with
                  | nil =>
                      exact ⟨.failure .altStackUnderflow,
                        .fromaltstack_underflow rest stack flags ctx⟩
                  | cons top altRest =>
                      rcases next (top :: stack) altRest with ⟨result, evaluated⟩
                      exact ⟨result, .fromAltStack top stack altRest rest flags ctx
                        result evaluated⟩
              | OP_1ADD =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_1ADD 1 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases decoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .unaryArithmetic_scriptnum_failure .OP_1ADD
                            operand stackRest rest altStack flags ctx error rfl decoded⟩
                      | ok value =>
                          rcases next (scriptNum (value + 1) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .oneAdd operand value stackRest altStack
                            rest flags ctx result decoded evaluated⟩
              | OP_1SUB =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_1SUB 1 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases decoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .unaryArithmetic_scriptnum_failure .OP_1SUB
                            operand stackRest rest altStack flags ctx error rfl decoded⟩
                      | ok value =>
                          rcases next (scriptNum (value - 1) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .oneSub operand value stackRest altStack
                            rest flags ctx result decoded evaluated⟩
              | OP_NEGATE =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NEGATE 1 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases decoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .unaryArithmetic_scriptnum_failure .OP_NEGATE
                            operand stackRest rest altStack flags ctx error rfl decoded⟩
                      | ok value =>
                          rcases next (scriptNum (-value) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .negate operand value stackRest altStack
                            rest flags ctx result decoded evaluated⟩
              | OP_ABS =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_ABS 1 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases decoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .unaryArithmetic_scriptnum_failure .OP_ABS
                            operand stackRest rest altStack flags ctx error rfl decoded⟩
                      | ok value =>
                          rcases next (scriptNum (if value < 0 then -value else value) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .abs operand value stackRest altStack
                            rest flags ctx result decoded evaluated⟩
              | OP_SUB =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_SUB 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_SUB 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_SUB top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (scriptNum (b - a) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .sub top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_MIN =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_MIN 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_MIN 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_MIN top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (scriptNum (Min.min b a) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .min top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_MAX =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_MAX 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_MAX 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_MAX top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (scriptNum (Max.max b a) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .max top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_NUMNOTEQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NUMNOTEQUAL 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_NUMNOTEQUAL 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_NUMNOTEQUAL top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (decide (a ≠ b)) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .numNotEqual top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_LESSTHAN =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_LESSTHAN 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_LESSTHAN 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_LESSTHAN top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (decide (b < a)) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .lessThan top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_GREATERTHAN =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_GREATERTHAN 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_GREATERTHAN 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_GREATERTHAN top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (decide (b > a)) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .greaterThan top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_LESSTHANOREQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_LESSTHANOREQUAL 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_LESSTHANOREQUAL 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_LESSTHANOREQUAL top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (decide (b ≤ a)) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .lessThanOrEqual top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_GREATERTHANOREQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_GREATERTHANOREQUAL 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_GREATERTHANOREQUAL 2 rest [top] altStack flags ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases decoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_GREATERTHANOREQUAL top belowTop stackRest
                                  rest altStack flags ctx error rfl decoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (decide (b ≥ a)) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .greaterThanOrEqual top belowTop a b stackRest rest altStack
                                flags ctx result decoded evaluated⟩
              | OP_ADD =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_ADD 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_ADD 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases hDecoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_ADD top belowTop stackRest
                                  rest altStack flags ctx error rfl hDecoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (scriptNum (a + b) :: stackRest) altStack with
                                ⟨result, evaluated⟩
                              exact ⟨result, .add top belowTop a b stackRest rest altStack
                                flags ctx result hDecoded evaluated⟩
              | OP_BOOLAND =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_BOOLAND 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_BOOLAND 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases hDecoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_BOOLAND top belowTop
                                  stackRest rest altStack flags ctx error rfl hDecoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next
                                  (boolToElement ((a != 0) && (b != 0)) :: stackRest)
                                  altStack with ⟨result, evaluated⟩
                              exact ⟨result, .booland top belowTop a b stackRest rest
                                altStack flags ctx result hDecoded evaluated⟩
              | OP_BOOLOR =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_BOOLOR 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_BOOLOR 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases hDecoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_BOOLOR top belowTop
                                  stackRest rest altStack flags ctx error rfl hDecoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next
                                  (boolToElement ((a != 0) || (b != 0)) :: stackRest)
                                  altStack with ⟨result, evaluated⟩
                              exact ⟨result, .boolor top belowTop a b stackRest rest
                                altStack flags ctx result hDecoded evaluated⟩
              | OP_WITHIN =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_WITHIN 3 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons upperBytes tail =>
                      cases tail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_WITHIN 3 rest [upperBytes] altStack flags ctx
                              rfl (by simp)⟩
                      | cons lowerBytes tail =>
                          cases tail with
                          | nil =>
                              exact ⟨.failure .stackUnderflow,
                                .stack_underflow .OP_WITHIN 3 rest [upperBytes, lowerBytes]
                                  altStack flags ctx rfl (by simp)⟩
                          | cons valueBytes stackRest =>
                              cases decoded : decodeWithinScriptNums flags
                                  upperBytes lowerBytes valueBytes with
                              | error error =>
                                  exact ⟨.failure error, .within_scriptnum_failure
                                    upperBytes lowerBytes valueBytes stackRest rest altStack
                                    flags ctx error decoded⟩
                              | ok values =>
                                  rcases values with ⟨upper, lower, value⟩
                                  rcases next
                                      (boolToElement (decide (lower ≤ value ∧ value < upper)) ::
                                        stackRest) altStack with ⟨result, evaluated⟩
                                  exact ⟨result, .within upperBytes lowerBytes valueBytes
                                    upper lower value stackRest altStack rest flags ctx result
                                    decoded evaluated⟩
              | OP_NOT =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NOT 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons operand stackRest =>
                      cases hDecoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .not_scriptnum_failure operand
                            stackRest rest altStack flags ctx error hDecoded⟩
                      | ok value =>
                          rcases next (boolToElement (value == 0) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .op_not operand value stackRest altStack
                            rest flags ctx result hDecoded evaluated⟩
              | OP_0NOTEQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_0NOTEQUAL 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons operand stackRest =>
                      cases hDecoded : decodeScriptNum operand flags.minimalData
                          maxArithmeticScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .unary_scriptnum_failure operand
                            stackRest rest altStack flags ctx error hDecoded⟩
                      | ok value =>
                          rcases next (boolToElement (value != 0) :: stackRest) altStack
                            with ⟨result, evaluated⟩
                          exact ⟨result, .zeroNotEqual operand value stackRest altStack
                            rest flags ctx result hDecoded evaluated⟩
              | OP_EQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_EQUAL 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_EQUAL 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          by_cases equal : top = belowTop
                          · rcases next (trueElement :: stackRest) altStack with
                              ⟨result, evaluated⟩
                            exact ⟨result, .equal_true top belowTop stackRest rest altStack
                              flags ctx result equal evaluated⟩
                          · rcases next (falseElement :: stackRest) altStack with
                              ⟨result, evaluated⟩
                            exact ⟨result, .equal_false top belowTop stackRest rest
                              altStack flags ctx result equal evaluated⟩
              | OP_EQUALVERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_EQUALVERIFY 2 rest [] altStack flags ctx
                          rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_EQUALVERIFY 2 rest [top] altStack flags
                              ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          by_cases equal : top = belowTop
                          · rcases next stackRest altStack with ⟨result, evaluated⟩
                            exact ⟨result, .equalverify_success top belowTop stackRest
                              rest altStack flags ctx result equal evaluated⟩
                          · exact ⟨.failure .equalVerify,
                              .equalverify_failure top belowTop stackRest rest altStack
                                flags ctx equal⟩
              | OP_NUMEQUAL =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NUMEQUAL 2 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_NUMEQUAL 2 rest [top] altStack flags ctx
                              rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases hDecoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_NUMEQUAL top belowTop
                                  stackRest rest altStack flags ctx error rfl hDecoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              rcases next (boolToElement (a == b) :: stackRest) altStack
                                with ⟨result, evaluated⟩
                              exact ⟨result, .numequal top belowTop a b stackRest rest
                                altStack flags ctx result hDecoded evaluated⟩
              | OP_NUMEQUALVERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_NUMEQUALVERIFY 2 rest [] altStack flags ctx
                          rfl (by simp)⟩
                  | cons top stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_NUMEQUALVERIFY 2 rest [top] altStack flags
                              ctx rfl (by simp)⟩
                      | cons belowTop stackRest =>
                          cases hDecoded : decodeBinaryScriptNums flags top belowTop with
                          | error error =>
                              exact ⟨.failure error,
                                .binary_scriptnum_failure .OP_NUMEQUALVERIFY top belowTop
                                  stackRest rest altStack flags ctx error rfl hDecoded⟩
                          | ok pair =>
                              rcases pair with ⟨a, b⟩
                              by_cases equal : a = b
                              · rcases next stackRest altStack with ⟨result, evaluated⟩
                                exact ⟨result, .numequalverify_success top belowTop a b
                                  stackRest rest altStack flags ctx result hDecoded equal
                                  evaluated⟩
                              · exact ⟨.failure .numEqualVerify,
                                  .numequalverify_failure top belowTop a b stackRest rest
                                    altStack flags ctx hDecoded equal⟩
              | OP_SHA256 =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_SHA256 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (sha256 top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .op_sha256 top stackRest rest altStack flags ctx
                        result evaluated⟩
              | OP_HASH256 =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_HASH256 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (hash256 top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .op_hash256 top stackRest rest altStack flags ctx
                        result evaluated⟩
              | OP_RIPEMD160 =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_RIPEMD160 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (ripemd160 top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .op_ripemd160 top stackRest rest altStack flags ctx
                        result evaluated⟩
              | OP_HASH160 =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_HASH160 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (hash160 top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .op_hash160 top stackRest rest altStack flags ctx
                        result evaluated⟩
              | OP_CHECKSIG =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_CHECKSIG 2 rest [] altStack flags ctx rfl (by simp)⟩
                  | cons pubkey stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_CHECKSIG 2 rest [pubkey] altStack flags ctx rfl (by simp)⟩
                      | cons sig stackRest =>
                          cases hChecked : checkSigWithEncoding checkSig checkSchnorrSig
                              flags ctx sig pubkey with
                          | error error =>
                              exact ⟨.failure error, .checksig_encoding_failure pubkey
                                sig stackRest rest altStack flags ctx error hChecked⟩
                          | ok checked =>
                              cases checked with
                              | false =>
                                  rcases next (falseElement :: stackRest) altStack with ⟨result, evaluated⟩
                                  exact ⟨result, .checksig_failure pubkey sig stackRest rest
                                    altStack flags ctx result hChecked evaluated⟩
                              | true =>
                                  rcases next (trueElement :: stackRest) altStack with ⟨result, evaluated⟩
                                  exact ⟨result, .checksig_success pubkey sig stackRest rest
                                    altStack flags ctx result hChecked evaluated⟩
              | OP_CHECKSIGVERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_CHECKSIGVERIFY 2 rest [] altStack flags ctx
                          rfl (by simp)⟩
                  | cons pubkey stackTail =>
                      cases stackTail with
                      | nil =>
                          exact ⟨.failure .stackUnderflow,
                            .stack_underflow .OP_CHECKSIGVERIFY 2 rest [pubkey] altStack
                              flags ctx rfl (by simp)⟩
                      | cons sig stackRest =>
                          cases hChecked : checkSigWithEncoding checkSig checkSchnorrSig
                              flags ctx sig pubkey with
                          | error error =>
                              exact ⟨.failure error,
                                .checksigverify_encoding_failure pubkey sig stackRest rest
                                  altStack flags ctx error hChecked⟩
                          | ok checked =>
                              cases checked with
                              | false =>
                                  exact ⟨.failure .checkSigVerify,
                                    .checksigverify_failure pubkey sig stackRest rest
                                      altStack flags ctx hChecked⟩
                              | true =>
                                  rcases next stackRest altStack with ⟨result, evaluated⟩
                                  exact ⟨result, .checksigverify_success pubkey sig stackRest
                                    rest altStack flags ctx result hChecked evaluated⟩
              | OP_CHECKSIGADD =>
                  by_cases available : ctx.sigVersion = .tapscript
                  · have arity : Opcode.activeFixedMainStackInputs? .OP_CHECKSIGADD
                        ctx.sigVersion = some 3 := by simp [Opcode.activeFixedMainStackInputs?, available]
                    cases stack with
                    | nil =>
                        exact ⟨.failure .stackUnderflow,
                          .stack_underflow .OP_CHECKSIGADD 3 rest [] altStack flags ctx arity (by simp)⟩
                    | cons pubkey stackTail =>
                        cases stackTail with
                        | nil =>
                            exact ⟨.failure .stackUnderflow,
                              .stack_underflow .OP_CHECKSIGADD 3 rest [pubkey] altStack flags ctx arity (by simp)⟩
                        | cons countBytes stackTail' =>
                            cases stackTail' with
                            | nil =>
                                exact ⟨.failure .stackUnderflow,
                                  .stack_underflow .OP_CHECKSIGADD 3 rest [pubkey, countBytes]
                                    altStack flags ctx arity (by simp)⟩
                            | cons sig stackRest =>
                                cases hDecoded : decodeCheckSigAddCount flags ctx countBytes with
                                | error error =>
                                    exact ⟨.failure error, .checksigadd_scriptnum_failure pubkey
                                      countBytes sig stackRest rest altStack flags ctx error available hDecoded⟩
                                | ok count =>
                                    cases hChecked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey with
                                    | error error =>
                                        exact ⟨.failure error, .checksigadd_encoding_failure pubkey
                                          countBytes sig count stackRest rest altStack flags ctx error hDecoded hChecked⟩
                                    | ok checked =>
                                        cases checked with
                                        | false =>
                                            rcases next (scriptNum count :: stackRest) altStack with ⟨result, evaluated⟩
                                            exact ⟨result, .checksigadd_failure pubkey countBytes sig count
                                              stackRest rest altStack flags ctx result hDecoded hChecked evaluated⟩
                                        | true =>
                                            rcases next (scriptNum (count + 1) :: stackRest) altStack with ⟨result, evaluated⟩
                                            exact ⟨result, .checksigadd_success pubkey countBytes sig count
                                              stackRest rest altStack flags ctx result hDecoded hChecked evaluated⟩
                  · exact ⟨.failure .badOpcode, .checksigadd_unavailable stack rest altStack flags ctx available⟩
              | OP_CHECKMULTISIG =>
                  cases hDecoded : decodeCheckMultiSigOperandsFor flags ctx stack with
                  | error error =>
                      exact ⟨.failure error, .checkmultisig_operand_failure stack rest
                        altStack flags ctx error hDecoded⟩
                  | ok operands =>
                      cases hChecked : checkMultiSigFor checkSig flags
                          ctx operands.signatures operands.pubkeys with
                      | error error =>
                          exact ⟨.failure error, .checkmultisig_encoding_failure stack
                            operands rest altStack flags ctx error hDecoded hChecked⟩
                      | ok checked =>
                          cases checked with
                          | false =>
                              by_cases nullFail : nullFailSatisfied flags operands.signatures
                              · cases hDummy : checkMultiSigDummy flags operands.dummy with
                                | error error =>
                                    exact ⟨.failure error,
                                      .checkmultisig_dummy_failure stack operands rest
                                        altStack flags ctx false error hDecoded hChecked
                                        (Or.inr nullFail) hDummy⟩
                                | ok value =>
                                    cases value
                                    rcases next (falseElement :: operands.rest) altStack with
                                      ⟨result, evaluated⟩
                                    exact ⟨result, .checkmultisig_failure stack operands rest
                                      altStack flags ctx result hDecoded hChecked nullFail hDummy
                                      evaluated⟩
                              · exact ⟨.failure .sigNullFail,
                                  .checkmultisig_nullfail_failure stack operands rest altStack
                                    flags ctx hDecoded hChecked nullFail⟩
                          | true =>
                              cases hDummy : checkMultiSigDummy flags operands.dummy with
                              | error error =>
                                  exact ⟨.failure error,
                                    .checkmultisig_dummy_failure stack operands rest altStack
                                      flags ctx true error hDecoded hChecked (Or.inl rfl) hDummy⟩
                              | ok value =>
                                  cases value
                                  rcases next (trueElement :: operands.rest) altStack with
                                    ⟨result, evaluated⟩
                                  exact ⟨result, .checkmultisig_success stack operands rest
                                    altStack flags ctx result hDecoded hChecked hDummy evaluated⟩
              | OP_CHECKMULTISIGVERIFY =>
                  cases hDecoded : decodeCheckMultiSigOperandsFor flags ctx stack with
                  | error error =>
                      exact ⟨.failure error,
                        .checkmultisigverify_operand_failure stack rest altStack flags ctx
                          error hDecoded⟩
                  | ok operands =>
                      cases hChecked : checkMultiSigFor checkSig flags
                          ctx operands.signatures operands.pubkeys with
                      | error error =>
                          exact ⟨.failure error,
                            .checkmultisigverify_encoding_failure stack operands rest altStack
                              flags ctx error hDecoded hChecked⟩
                      | ok checked =>
                          cases checked with
                          | false =>
                              by_cases nullFail : nullFailSatisfied flags operands.signatures
                              · cases hDummy : checkMultiSigDummy flags operands.dummy with
                                | error error =>
                                    exact ⟨.failure error,
                                      .checkmultisigverify_dummy_failure stack operands rest
                                        altStack flags ctx false error hDecoded hChecked
                                        (Or.inr nullFail) hDummy⟩
                                | ok value =>
                                    cases value
                                    exact ⟨.failure .checkMultiSigVerify,
                                      .checkmultisigverify_failure stack operands rest
                                        altStack flags ctx hDecoded hChecked nullFail hDummy⟩
                              · exact ⟨.failure .sigNullFail,
                                  .checkmultisigverify_nullfail_failure stack operands rest
                                    altStack flags ctx hDecoded hChecked nullFail⟩
                          | true =>
                              cases hDummy : checkMultiSigDummy flags operands.dummy with
                              | error error =>
                                  exact ⟨.failure error,
                                    .checkmultisigverify_dummy_failure stack operands rest
                                      altStack flags ctx true error hDecoded hChecked
                                      (Or.inl rfl) hDummy⟩
                              | ok value =>
                                  cases value
                                  rcases next operands.rest altStack with
                                    ⟨result, evaluated⟩
                                  exact ⟨result, .checkmultisigverify_success stack operands
                                    rest altStack flags ctx result hDecoded hChecked hDummy
                                    evaluated⟩
              | OP_CHECKSEQUENCEVERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_CHECKSEQUENCEVERIFY 1 rest [] altStack flags
                          ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases hDecoded : decodeScriptNum operand flags.minimalData
                          maxTimelockScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .timelock_scriptnum_failure
                            .OP_CHECKSEQUENCEVERIFY operand stackRest rest altStack flags
                            ctx error rfl hDecoded⟩
                      | ok value =>
                          by_cases negative : value < 0
                          · exact ⟨.failure .negativeLocktime,
                              .timelock_negative_failure .OP_CHECKSEQUENCEVERIFY operand
                                value stackRest rest altStack flags ctx rfl hDecoded
                                negative⟩
                          · have nonnegative : 0 ≤ value := by omega
                            by_cases satisfied : sequenceSatisfied value.toNat ctx
                            · rcases next (operand :: stackRest) altStack with
                                ⟨result, evaluated⟩
                              exact ⟨result, .checksequenceverify_success operand value
                                stackRest rest altStack flags ctx result hDecoded
                                nonnegative satisfied evaluated⟩
                            · exact ⟨.failure .checkSequenceVerify,
                                .checksequenceverify_failure operand value stackRest rest
                                  altStack flags ctx hDecoded nonnegative satisfied⟩
              | OP_CHECKLOCKTIMEVERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_CHECKLOCKTIMEVERIFY 1 rest [] altStack flags
                          ctx rfl (by simp)⟩
                  | cons operand stackRest =>
                      cases hDecoded : decodeScriptNum operand flags.minimalData
                          maxTimelockScriptNumBytes with
                      | error error =>
                          exact ⟨.failure error, .timelock_scriptnum_failure
                            .OP_CHECKLOCKTIMEVERIFY operand stackRest rest altStack flags
                            ctx error rfl hDecoded⟩
                      | ok value =>
                          by_cases negative : value < 0
                          · exact ⟨.failure .negativeLocktime,
                              .timelock_negative_failure .OP_CHECKLOCKTIMEVERIFY operand
                                value stackRest rest altStack flags ctx rfl hDecoded
                                negative⟩
                          · have nonnegative : 0 ≤ value := by omega
                            by_cases satisfied : locktimeSatisfied value.toNat ctx
                            · rcases next (operand :: stackRest) altStack with
                                ⟨result, evaluated⟩
                              exact ⟨result, .checklocktimeverify_success operand value
                                stackRest rest altStack flags ctx result hDecoded
                                nonnegative satisfied evaluated⟩
                            · exact ⟨.failure .checkLockTimeVerify,
                                .checklocktimeverify_failure operand value stackRest rest
                                  altStack flags ctx hDecoded nonnegative satisfied⟩
              | OP_VERIFY =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_VERIFY 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      cases hTruthy : castToBool top with
                      | false =>
                          exact ⟨.failure .verify,
                            .verify_failure top stackRest rest altStack flags ctx hTruthy⟩
                      | true =>
                          rcases next stackRest altStack with ⟨result, evaluated⟩
                          exact ⟨result, .verify_success top stackRest rest altStack flags
                            ctx result hTruthy evaluated⟩
              | OP_SIZE =>
                  cases stack with
                  | nil =>
                      exact ⟨.failure .stackUnderflow,
                        .stack_underflow .OP_SIZE 1 rest [] altStack flags ctx rfl
                          (by simp)⟩
                  | cons top stackRest =>
                      rcases next (scriptNat top.size :: top :: stackRest) altStack with
                        ⟨result, evaluated⟩
                      exact ⟨result, .size top stackRest altStack rest flags ctx result
                        evaluated⟩

/-- Big-step evaluation has exactly one result for every modeled initial
    state. -/
theorem Eval.existsUnique_result
    (script : Script) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    ∃ result, Eval script stack altStack flags ctx result ∧
      ∀ other, Eval script stack altStack flags ctx other → other = result := by
  rcases Eval.exists_result script stack altStack flags ctx with
    ⟨result, evaluated⟩
  exact ⟨result, evaluated, fun other otherEval =>
    Eval.result_unique otherEval evaluated⟩

theorem Eval.done {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext} :
    Eval [] stack altStack flags ctx (.success stack altStack) :=
  .empty stack altStack flags ctx

/-- NIP removes precisely the second item for every pair of byte vectors. -/
theorem Eval.nip_result (top discarded : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_NIP] (top :: discarded :: stack) altStack flags ctx result ↔
      result = .success (top :: stack) altStack := by
  have canonical : Eval [.op .OP_NIP] (top :: discarded :: stack) altStack flags ctx
      (.success (top :: stack) altStack) :=
    .nip top discarded stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, NIP terminates before any suffix. -/
theorem Eval.nip_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_NIP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_NIP 2 script stack altStack flags ctx rfl short)

/-- 2DROP removes precisely the top two items for every pair of byte vectors. -/
theorem Eval.twoDrop_result (top discarded : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2DROP] (top :: discarded :: stack) altStack flags ctx result ↔
      result = .success stack altStack := by
  have canonical : Eval [.op .OP_2DROP] (top :: discarded :: stack) altStack flags ctx
      (.success stack altStack) :=
    .twoDrop top discarded stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, 2DROP terminates before any suffix. -/
theorem Eval.twoDrop_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_2DROP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2DROP 2 script stack altStack flags ctx rfl short)

/-- 2DUP copies the top pair in order above the unchanged original stack. -/
theorem Eval.twoDup_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2DUP] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (top :: below :: top :: below :: stack) altStack := by
  have canonical : Eval [.op .OP_2DUP] (top :: below :: stack) altStack flags ctx
      (.success (top :: below :: top :: below :: stack) altStack) :=
    .twoDup top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, 2DUP terminates before any suffix. -/
theorem Eval.twoDup_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_2DUP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2DUP 2 script stack altStack flags ctx rfl short)

/-- 3DUP copies the top three items in order above the unchanged original stack. -/
theorem Eval.threeDup_result (top second third : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_3DUP] (top :: second :: third :: stack) altStack flags ctx result ↔
      result = .success (top :: second :: third :: top :: second :: third :: stack) altStack := by
  have canonical : Eval [.op .OP_3DUP] (top :: second :: third :: stack) altStack flags ctx
      (.success (top :: second :: third :: top :: second :: third :: stack) altStack) :=
    .threeDup top second third stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than three main-stack items, 3DUP terminates before any suffix. -/
theorem Eval.threeDup_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 3)
    (evaluated : Eval (.op .OP_3DUP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_3DUP 3 script stack altStack flags ctx rfl short)

/-- 2OVER copies the third and fourth items above the unchanged original stack. -/
theorem Eval.twoOver_result (top second third fourth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2OVER] (top :: second :: third :: fourth :: stack) altStack flags ctx result ↔
      result = .success (third :: fourth :: top :: second :: third :: fourth :: stack) altStack := by
  have canonical : Eval [.op .OP_2OVER] (top :: second :: third :: fourth :: stack) altStack flags ctx
      (.success (third :: fourth :: top :: second :: third :: fourth :: stack) altStack) :=
    .twoOver top second third fourth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than four main-stack items, 2OVER terminates before any suffix. -/
theorem Eval.twoOver_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 4)
    (evaluated : Eval (.op .OP_2OVER :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2OVER 4 script stack altStack flags ctx rfl short)

/-- OVER copies precisely the second item above the unchanged original stack. -/
theorem Eval.over_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_OVER] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (below :: top :: below :: stack) altStack := by
  have canonical : Eval [.op .OP_OVER] (top :: below :: stack) altStack flags ctx
      (.success (below :: top :: below :: stack) altStack) :=
    .over top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, OVER terminates before any suffix. -/
theorem Eval.over_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_OVER :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_OVER 2 script stack altStack flags ctx rfl short)

/-- TUCK inserts an exact copy of the top item beneath the original top two. -/
theorem Eval.tuck_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_TUCK] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (top :: below :: top :: stack) altStack := by
  have canonical : Eval [.op .OP_TUCK] (top :: below :: stack) altStack flags ctx
      (.success (top :: below :: top :: stack) altStack) :=
    .tuck top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, TUCK terminates before any suffix. -/
theorem Eval.tuck_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_TUCK :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_TUCK 2 script stack altStack flags ctx rfl short)

/-- ROT moves the third item to the top, preserving the lower stack and raw bytes. -/
theorem Eval.rot_result (top second third : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_ROT] (top :: second :: third :: stack) altStack flags ctx result ↔
      result = .success (third :: top :: second :: stack) altStack := by
  have canonical : Eval [.op .OP_ROT] (top :: second :: third :: stack) altStack flags ctx
      (.success (third :: top :: second :: stack) altStack) :=
    .rot top second third stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than three main-stack items, ROT terminates before any suffix. -/
theorem Eval.rot_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 3)
    (evaluated : Eval (.op .OP_ROT :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_ROT 3 script stack altStack flags ctx rfl short)

/-- 2ROT moves the fifth and sixth items to the top, preserving the lower stack and raw bytes. -/
theorem Eval.twoRot_result (top second third fourth fifth sixth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2ROT] (top :: second :: third :: fourth :: fifth :: sixth :: stack) altStack flags ctx result ↔
      result = .success (fifth :: sixth :: top :: second :: third :: fourth :: stack) altStack := by
  have canonical : Eval [.op .OP_2ROT] (top :: second :: third :: fourth :: fifth :: sixth :: stack) altStack flags ctx
      (.success (fifth :: sixth :: top :: second :: third :: fourth :: stack) altStack) :=
    .twoRot top second third fourth fifth sixth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than six main-stack items, 2ROT terminates before any suffix. -/
theorem Eval.twoRot_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 6)
    (evaluated : Eval (.op .OP_2ROT :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2ROT 6 script stack altStack flags ctx rfl short)

/-- 2SWAP exchanges the top two pairs, preserving the lower stack and raw bytes. -/
theorem Eval.twoSwap_result (top second third fourth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2SWAP] (top :: second :: third :: fourth :: stack) altStack flags ctx result ↔
      result = .success (third :: fourth :: top :: second :: stack) altStack := by
  have canonical : Eval [.op .OP_2SWAP] (top :: second :: third :: fourth :: stack) altStack flags ctx
      (.success (third :: fourth :: top :: second :: stack) altStack) :=
    .twoSwap top second third fourth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than four main-stack items, 2SWAP terminates before any suffix. -/
theorem Eval.twoSwap_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 4)
    (evaluated : Eval (.op .OP_2SWAP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2SWAP 4 script stack altStack flags ctx rfl short)

/-- An allowed upgradeable NOP preserves the suffix relation and both stacks. -/
theorem Eval.upgradeableNop_cons (opcode : Opcode) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) (result : ExecResult) :
    Eval (.op opcode :: script) stack altStack flags ctx result ↔
      Eval script stack altStack flags ctx result := by
  constructor
  · intro evaluated
    rcases Eval.exists_result script stack altStack flags ctx with ⟨nextResult, next⟩
    have same := evaluated.result_unique
      (.upgradeableNop opcode script stack altStack flags ctx nextResult
        upgradeable allowed next)
    cases same
    exact next
  · exact .upgradeableNop opcode script stack altStack flags ctx result upgradeable allowed

/-- An allowed upgradeable NOP has the exact unchanged-stack result. -/
theorem Eval.upgradeableNop_result (opcode : Opcode)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) (result : ExecResult) :
    Eval [.op opcode] stack altStack flags ctx result ↔
      result = .success stack altStack := by
  have canonical : Eval [.op opcode] stack altStack flags ctx (.success stack altStack) :=
    .upgradeableNop opcode [] stack altStack flags ctx _ upgradeable allowed .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A discouraged upgradeable NOP terminates before its suffix. -/
theorem Eval.upgradeableNop_failure_result (opcode : Opcode) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (discouraged : flags.discourageUpgradableNops = true) (result : ExecResult) :
    Eval (.op opcode :: script) stack altStack flags ctx result ↔
      result = .failure .discourageUpgradableNops := by
  have canonical : Eval (.op opcode :: script) stack altStack flags ctx
      (.failure .discourageUpgradableNops) :=
    .upgradeableNop_discouraged opcode script stack altStack flags ctx upgradeable discouraged
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Active RETURN determines the terminal result for every stack and suffix. -/
theorem Eval.opReturn_result (script : Script) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval (.op .OP_RETURN :: script) stack altStack flags ctx result ↔
      result = .failure .opReturn := by
  have canonical : Eval (.op .OP_RETURN :: script) stack altStack flags ctx
      (.failure .opReturn) := .opReturn script stack altStack flags ctx
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A decoded in-range index determines the exact OP_PICK result. -/
theorem Eval.pick_result (operand top : StackElement) (index : Nat)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeStackIndex flags operand (top :: stack).length = .ok index)
    (result : ExecResult) :
    Eval [.op .OP_PICK] (operand :: top :: stack) altStack flags ctx result ↔
      result = .success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack)) altStack := by
  have canonical : Eval [.op .OP_PICK] (operand :: top :: stack) altStack flags ctx
      (.success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack)) altStack) :=
    .pick operand top index stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A decoded in-range index determines the exact OP_ROLL result. -/
theorem Eval.roll_result (operand top : StackElement) (index : Nat)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeStackIndex flags operand (top :: stack).length = .ok index)
    (result : ExecResult) :
    Eval [.op .OP_ROLL] (operand :: top :: stack) altStack flags ctx result ↔
      result = .success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack).eraseIdx index) altStack := by
  have canonical : Eval [.op .OP_ROLL] (operand :: top :: stack) altStack flags ctx
      (.success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack).eraseIdx index) altStack) :=
    .roll operand top index stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- DEPTH has this exact relational result for every main/alternate stack. -/
theorem Eval.depth_result (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_DEPTH] stack altStack flags ctx result ↔
      result = .success (scriptNat stack.length :: stack) altStack := by
  have canonical : Eval [.op .OP_DEPTH] stack altStack flags ctx
      (.success (scriptNat stack.length :: stack) altStack) :=
    .depth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_1ADD decoding determines its exact relational result. -/
theorem Eval.oneAdd_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_1ADD] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (value + 1) :: stack) altStack := by
  have canonical : Eval [.op .OP_1ADD] (operand :: stack) altStack flags ctx
      (.success (scriptNum (value + 1) :: stack) altStack) :=
    .oneAdd operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_1SUB decoding determines its exact relational result. -/
theorem Eval.oneSub_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_1SUB] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (value - 1) :: stack) altStack := by
  have canonical : Eval [.op .OP_1SUB] (operand :: stack) altStack flags ctx
      (.success (scriptNum (value - 1) :: stack) altStack) :=
    .oneSub operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_NEGATE decoding determines its exact relational result. -/
theorem Eval.negate_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_NEGATE] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (-value) :: stack) altStack := by
  have canonical : Eval [.op .OP_NEGATE] (operand :: stack) altStack flags ctx
      (.success (scriptNum (-value) :: stack) altStack) :=
    .negate operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_ABS decoding determines its exact relational result. -/
theorem Eval.abs_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_ABS] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (if value < 0 then -value else value) :: stack) altStack := by
  have canonical : Eval [.op .OP_ABS] (operand :: stack) altStack flags ctx
      (.success (scriptNum (if value < 0 then -value else value) :: stack) altStack) :=
    .abs operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_SUB operands determine its exact relational result. -/
theorem Eval.sub_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_SUB] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (b - a) :: stack) altStack := by
  have canonical : Eval [.op .OP_SUB] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (b - a) :: stack) altStack) :=
    .sub aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_MIN operands determine its exact relational result. -/
theorem Eval.min_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_MIN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (Min.min b a) :: stack) altStack := by
  have canonical : Eval [.op .OP_MIN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (Min.min b a) :: stack) altStack) :=
    .min aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_MAX operands determine its exact relational result. -/
theorem Eval.max_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_MAX] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (Max.max b a) :: stack) altStack := by
  have canonical : Eval [.op .OP_MAX] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (Max.max b a) :: stack) altStack) :=
    .max aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_NUMNOTEQUAL operands determine its exact relational result. -/
theorem Eval.numNotEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_NUMNOTEQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (a ≠ b)) :: stack) altStack := by
  have canonical : Eval [.op .OP_NUMNOTEQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (a ≠ b)) :: stack) altStack) :=
    .numNotEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_LESSTHAN operands determine its exact relational result. -/
theorem Eval.lessThan_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_LESSTHAN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b < a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_LESSTHAN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b < a)) :: stack) altStack) :=
    .lessThan aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_GREATERTHAN operands determine its exact relational result. -/
theorem Eval.greaterThan_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_GREATERTHAN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b > a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_GREATERTHAN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b > a)) :: stack) altStack) :=
    .greaterThan aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_LESSTHANOREQUAL operands determine its exact relational result. -/
theorem Eval.lessThanOrEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_LESSTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b ≤ a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_LESSTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b ≤ a)) :: stack) altStack) :=
    .lessThanOrEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_GREATERTHANOREQUAL operands determine its exact relational result. -/
theorem Eval.greaterThanOrEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_GREATERTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b ≥ a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_GREATERTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b ≥ a)) :: stack) altStack) :=
    .greaterThanOrEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful NOT decoding determines its exact relational result. -/
theorem Eval.not_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_NOT] (operand :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (value == 0) :: stack) altStack := by
  have canonical : Eval [.op .OP_NOT] (operand :: stack) altStack flags ctx
      (.success (boolToElement (value == 0) :: stack) altStack) :=
    .op_not operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Any relational execution after a NOT decoder error has that exact failure. -/
theorem Eval.notScriptNumFailure_result
    {operand : StackElement} {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .error error)
    (evaluated : Eval (.op .OP_NOT :: script) (operand :: stack) altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.not_scriptnum_failure operand stack script altStack flags ctx error decoded)

/-- Decoded WITHIN operands determine the exact relational stack result. -/
theorem Eval.within_result (upperBytes lowerBytes valueBytes : StackElement)
    (upper lower value : Int) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .ok (upper, lower, value))
    (result : ExecResult) :
    Eval [.op .OP_WITHIN] (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack) altStack := by
  have canonical : Eval [.op .OP_WITHIN] (upperBytes :: lowerBytes :: valueBytes :: stack)
      altStack flags ctx (.success (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack)
        altStack) :=
    .within upperBytes lowerBytes valueBytes upper lower value stack altStack [] flags ctx _
      decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Every relational execution after a WITHIN decoding error has that failure. -/
theorem Eval.withinScriptNumFailure_result
    {upperBytes lowerBytes valueBytes : StackElement} {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .error error)
    (evaluated : Eval (.op .OP_WITHIN :: script) (upperBytes :: lowerBytes :: valueBytes :: stack)
      altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.within_scriptnum_failure upperBytes lowerBytes valueBytes stack script altStack flags ctx
      error decoded)

theorem Eval.pushDataNext
    {data : StackElement} {rest : Script} {stack altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval rest (data :: stack) altStack flags ctx result) :
    Eval (.pushData data :: rest) stack altStack flags ctx result :=
  .pushData data rest stack altStack flags ctx result next

theorem Eval.checksigTrue
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true)
    (next : Eval script (trueElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result :=
  .checksig_success pubkey sig rest script altStack flags ctx result checked next

theorem Eval.checksigFalse
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok false)
    (next : Eval script (falseElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result :=
  .checksig_failure pubkey sig rest script altStack flags ctx result checked next

/-- Rejected nonempty ECDSA signatures terminate at the checked boundary. -/
theorem Eval.checksigNullFail
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error .sigNullFail) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx (.failure .sigNullFail) :=
  .checksig_encoding_failure pubkey sig rest script altStack flags ctx .sigNullFail checked

theorem Eval.verifyTrue
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (truthy : castToBool top = true)
    (next : Eval script rest altStack flags ctx result) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx result :=
  .verify_success top rest script altStack flags ctx result truthy next

theorem Eval.verifyFalse
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (falsey : castToBool top = false) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx
      (.failure .verify) :=
  .verify_failure top rest script altStack flags ctx falsey

theorem Eval.toAltStackNext
    {x : StackElement} {rest altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script rest (x :: altStack) flags ctx result) :
    Eval (.op .OP_TOALTSTACK :: script) (x :: rest) altStack flags ctx result :=
  .toAltStack x rest altStack script flags ctx result next

theorem Eval.fromAltStackNext
    {x : StackElement} {stack altRest : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script (x :: stack) altRest flags ctx result) :
    Eval (.op .OP_FROMALTSTACK :: script) stack (x :: altRest) flags ctx result :=
  .fromAltStack x stack altRest script flags ctx result next

/-- A concrete non-minimal truthy IF argument fails when the active signature
    version requires MINIMALIF. -/
theorem nonMinimalTruthy_if_else_minimalif_failure
    (rest altStack : Stack) (thenBranch elseBranch after : Script)
    (flags : ScriptFlags) (ctx : TxContext)
    (nonMinimal : ¬ minimalIfSatisfied flags ctx.sigVersion
      nonMinimalTruthyElement) :
    Eval (.op .OP_IF ::
          (thenBranch ++ (.op .OP_ELSE ::
            elseBranch ++ .op .OP_ENDIF :: after)))
      (nonMinimalTruthyElement :: rest) altStack flags ctx
      (.failure (minimalIfError ctx.sigVersion)) := by
  exact Eval.if_minimalif_failure nonMinimalTruthyElement rest altStack
    (thenBranch ++ (.op .OP_ELSE :: elseBranch ++ .op .OP_ENDIF :: after))
    flags ctx nonMinimal

/-- When the active signature-version rules admit it, the same concrete
    non-minimal truthy IF argument selects the true branch. -/
theorem nonMinimalTruthy_if_else_relaxed_true
    (rest altStack : Stack) (script : Script) (frame : ConditionalFrame)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult)
    (minimal : minimalIfSatisfied flags ctx.sigVersion
      nonMinimalTruthyElement)
    (hSplit : splitConditional script = some frame)
    (hSelected : Eval (frame.select true) rest altStack flags ctx result) :
    Eval (.op .OP_IF :: script) (nonMinimalTruthyElement :: rest)
      altStack flags ctx result := by
  apply Eval.if_execute nonMinimalTruthyElement rest altStack script frame
    flags ctx result hSplit minimal
  simpa [nonMinimalTruthyElement_truthy] using hSelected

/-- Moving a stack element to the alt stack and immediately back preserves both
    stacks. -/
theorem toAltStack_fromAltStack_roundtrip
    (x : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    Eval [.op .OP_TOALTSTACK, .op .OP_FROMALTSTACK]
      (x :: stack) altStack flags ctx (.success (x :: stack) altStack) := by
  exact Eval.toAltStack x stack altStack [.op .OP_FROMALTSTACK] flags ctx _
    (Eval.fromAltStack x stack altStack [] flags ctx _
      (Eval.empty (x :: stack) altStack flags ctx))

end LeanMiniscript.Script
