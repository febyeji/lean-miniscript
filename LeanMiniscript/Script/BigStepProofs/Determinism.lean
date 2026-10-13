import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
# Big-step proofs: composition, failure API, and determinism

Sequencing over script concatenation, proof-facing failure constructors and
their terminal results, and uniqueness of big-step results.
-/

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

end LeanMiniscript.Script
