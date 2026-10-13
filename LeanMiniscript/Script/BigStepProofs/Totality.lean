import LeanMiniscript.Script.BigStep
import LeanMiniscript.Script.BigStepProofs.Determinism

namespace LeanMiniscript.Script

/-!
# Big-step proofs: totality

Every script in the modeled opcode subset has exactly one big-step result.
-/

/-! ## Opcode-family case helpers

Each helper discharges the stack-underflow or decoder-error branches shared by
one opcode family, leaving only the well-shaped continuation to the caller. -/

/-- A fixed-arity opcode underflows on a short stack, so totality only needs
    the case with enough inputs. -/
private theorem exists_of_fixedArity
    {opcode : Opcode} {required : Nat} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some required)
    (step : required ≤ stack.length →
      ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result := by
  by_cases short : stack.length < required
  · exact ⟨_, .stack_underflow opcode required rest stack altStack flags ctx arity short⟩
  · exact step (by omega)

/-- Unary specialization of `exists_of_fixedArity`. -/
private theorem exists_of_arity1
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 1)
    (step : ∀ top stackRest,
      ∃ result, Eval (.op opcode :: rest) (top :: stackRest) altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result :=
  exists_of_fixedArity arity fun long => by
    rcases stack with _ | ⟨top, stackRest⟩
    all_goals first | exact step top stackRest | simp at long

/-- Binary specialization of `exists_of_fixedArity`. -/
private theorem exists_of_arity2
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 2)
    (step : ∀ top second stackRest,
      ∃ result, Eval (.op opcode :: rest) (top :: second :: stackRest) altStack flags ctx
        result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result :=
  exists_of_fixedArity arity fun long => by
    rcases stack with _ | ⟨top, _ | ⟨second, stackRest⟩⟩
    all_goals first | exact step top second stackRest | simp at long

/-- Ternary specialization of `exists_of_fixedArity`. -/
private theorem exists_of_arity3
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 3)
    (step : ∀ top second third stackRest,
      ∃ result, Eval (.op opcode :: rest) (top :: second :: third :: stackRest) altStack
        flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result :=
  exists_of_fixedArity arity fun long => by
    rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, stackRest⟩⟩⟩
    all_goals first | exact step top second third stackRest | simp at long

/-- Four-input specialization of `exists_of_fixedArity`. -/
private theorem exists_of_arity4
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 4)
    (step : ∀ top second third fourth stackRest,
      ∃ result, Eval (.op opcode :: rest) (top :: second :: third :: fourth :: stackRest)
        altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result :=
  exists_of_fixedArity arity fun long => by
    rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, stackRest⟩⟩⟩⟩
    all_goals first | exact step top second third fourth stackRest | simp at long

/-- Six-input specialization of `exists_of_fixedArity`. -/
private theorem exists_of_arity6
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 6)
    (step : ∀ top second third fourth fifth sixth stackRest,
      ∃ result, Eval (.op opcode :: rest)
        (top :: second :: third :: fourth :: fifth :: sixth :: stackRest)
        altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result :=
  exists_of_fixedArity arity fun long => by
    rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ |
      ⟨fifth, _ | ⟨sixth, stackRest⟩⟩⟩⟩⟩⟩
    all_goals first | exact step top second third fourth fifth sixth stackRest | simp at long

/-- An upgradeable NOP is either discouraged or continues unchanged. -/
private theorem exists_of_upgradeableNop
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (upgradeable : opcode.isUpgradeableNop = true)
    (next : ∃ result, Eval rest stack altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result := by
  cases discouraged : flags.discourageUpgradableNops with
  | false =>
      exact next.imp fun result evaluated =>
        .upgradeableNop opcode rest stack altStack flags ctx result upgradeable discouraged
          evaluated
  | true =>
      exact ⟨_, .upgradeableNop_discouraged opcode rest stack altStack flags ctx
        upgradeable discouraged⟩

/-- Unary arithmetic underflows, reports its decoder error, or continues from
    the decoded operand. -/
private theorem exists_of_unaryArithmetic
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 1)
    (usesNumber : opcode.usesUnaryArithmetic = true)
    (step : ∀ operand stackRest value,
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes = .ok value →
      ∃ result, Eval (.op opcode :: rest) (operand :: stackRest) altStack flags ctx result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result := by
  refine exists_of_arity1 arity fun operand stackRest => ?_
  cases decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
  | error error =>
      exact ⟨_, .unaryArithmetic_scriptnum_failure opcode operand stackRest rest altStack
        flags ctx error usesNumber decoded⟩
  | ok value => exact step operand stackRest value decoded

/-- A binary numeric opcode underflows, reports its decoder error, or
    continues from the decoded operands. -/
private theorem exists_of_binaryScriptNums
    {opcode : Opcode} {rest : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.activeFixedMainStackInputs? ctx.sigVersion = some 2)
    (usesNumbers : opcode.usesBinaryScriptNums = true)
    (step : ∀ top belowTop stackRest a b,
      decodeBinaryScriptNums flags top belowTop = .ok (a, b) →
      ∃ result, Eval (.op opcode :: rest) (top :: belowTop :: stackRest) altStack flags ctx
        result) :
    ∃ result, Eval (.op opcode :: rest) stack altStack flags ctx result := by
  refine exists_of_arity2 arity fun top belowTop stackRest => ?_
  cases decoded : decodeBinaryScriptNums flags top belowTop with
  | error error =>
      exact ⟨_, .binary_scriptnum_failure opcode top belowTop stackRest rest altStack
        flags ctx error usesNumbers decoded⟩
  | ok pair => exact step top belowTop stackRest pair.1 pair.2 decoded

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
              exact (next (data :: stack) altStack).imp fun result evaluated =>
                .pushData data rest stack altStack flags ctx result evaluated
          | pushNum value =>
              exact (next (scriptNum value :: stack) altStack).imp fun result evaluated =>
                .pushNum value rest stack altStack flags ctx result evaluated
          | op opcode =>
              cases opcode with
              | OP_NOP =>
                  exact (next stack altStack).imp fun result evaluated =>
                    .nop rest stack altStack flags ctx result evaluated
              | OP_NOP1 | OP_NOP4 | OP_NOP5 | OP_NOP6 | OP_NOP7 | OP_NOP8 | OP_NOP9
                | OP_NOP10 =>
                  exact exists_of_upgradeableNop rfl (next stack altStack)
              | OP_RETURN =>
                  exact ⟨.failure .opReturn, .opReturn rest stack altStack flags ctx⟩
              | OP_IF =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
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
                        exact (ih _ selectedShort _ stackRest altStack rfl).imp
                          fun result evaluated => .if_execute top stackRest altStack rest
                            frame flags ctx result hSplit minimal evaluated
                  · exact ⟨.failure (minimalIfError ctx.sigVersion),
                      .if_minimalif_failure top stackRest altStack rest flags ctx
                        minimal⟩
              | OP_NOTIF =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
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
                        exact (ih _ selectedShort _ stackRest altStack rfl).imp
                          fun result evaluated => .notif_execute top stackRest altStack
                            rest frame flags ctx result hSplit minimal evaluated
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
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  cases hTruthy : castToBool top with
                  | false =>
                      exact (next (top :: stackRest) altStack).imp fun result evaluated =>
                        .ifdup_false top stackRest altStack rest flags ctx result hTruthy
                          evaluated
                  | true =>
                      exact (next (top :: top :: stackRest) altStack).imp
                        fun result evaluated => .ifdup_true top stackRest altStack rest
                          flags ctx result hTruthy evaluated
              | OP_DEPTH =>
                  exact (next (scriptNat stack.length :: stack) altStack).imp
                    fun result evaluated =>
                      .depth stack altStack rest flags ctx result evaluated
              | OP_DROP =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next stackRest altStack).imp fun result evaluated =>
                    .drop top stackRest rest altStack flags ctx result evaluated
              | OP_DUP =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (top :: top :: stackRest) altStack).imp fun result evaluated =>
                    .dup top stackRest rest altStack flags ctx result evaluated
              | OP_NIP =>
                  refine exists_of_arity2 rfl fun top discarded stackRest => ?_
                  exact (next (top :: stackRest) altStack).imp fun result evaluated =>
                    .nip top discarded stackRest altStack rest flags ctx result evaluated
              | OP_2DROP =>
                  refine exists_of_arity2 rfl fun top discarded stackRest => ?_
                  exact (next stackRest altStack).imp fun result evaluated =>
                    .twoDrop top discarded stackRest altStack rest flags ctx result evaluated
              | OP_2DUP =>
                  refine exists_of_arity2 rfl fun top below stackRest => ?_
                  exact (next (top :: below :: top :: below :: stackRest) altStack).imp
                    fun result evaluated =>
                      .twoDup top below stackRest altStack rest flags ctx result evaluated
              | OP_3DUP =>
                  refine exists_of_arity3 rfl fun top second third stackRest => ?_
                  exact (next (top :: second :: third :: top :: second :: third :: stackRest)
                    altStack).imp fun result evaluated =>
                      .threeDup top second third stackRest altStack rest flags ctx result
                        evaluated
              | OP_2OVER =>
                  refine exists_of_arity4 rfl fun top second third fourth stackRest => ?_
                  exact (next (third :: fourth :: top :: second :: third :: fourth :: stackRest)
                    altStack).imp fun result evaluated =>
                      .twoOver top second third fourth stackRest altStack rest flags ctx
                        result evaluated
              | OP_OVER =>
                  refine exists_of_arity2 rfl fun top below stackRest => ?_
                  exact (next (below :: top :: below :: stackRest) altStack).imp
                    fun result evaluated =>
                      .over top below stackRest altStack rest flags ctx result evaluated
              | OP_PICK =>
                  refine exists_of_arity2 rfl fun operand top stackRest => ?_
                  cases decoded : decodeStackIndex flags operand (top :: stackRest).length with
                  | error error =>
                      exact ⟨.failure error,
                        .stackindex_failure .OP_PICK operand top stackRest rest altStack
                          flags ctx error rfl decoded⟩
                  | ok index =>
                      exact (next ((top :: stackRest)[index]?.getD ByteArray.empty ::
                          (top :: stackRest)) altStack).imp fun result evaluated =>
                        .pick operand top index stackRest altStack rest flags ctx result
                          decoded evaluated
              | OP_ROLL =>
                  refine exists_of_arity2 rfl fun operand top stackRest => ?_
                  cases decoded : decodeStackIndex flags operand (top :: stackRest).length with
                  | error error =>
                      exact ⟨.failure error,
                        .stackindex_failure .OP_ROLL operand top stackRest rest altStack
                          flags ctx error rfl decoded⟩
                  | ok index =>
                      exact (next ((top :: stackRest)[index]?.getD ByteArray.empty ::
                          (top :: stackRest).eraseIdx index) altStack).imp
                        fun result evaluated =>
                          .roll operand top index stackRest altStack rest flags ctx result
                            decoded evaluated
              | OP_TUCK =>
                  refine exists_of_arity2 rfl fun top below stackRest => ?_
                  exact (next (top :: below :: top :: stackRest) altStack).imp
                    fun result evaluated =>
                      .tuck top below stackRest altStack rest flags ctx result evaluated
              | OP_ROT =>
                  refine exists_of_arity3 rfl fun top second third stackRest => ?_
                  exact (next (third :: top :: second :: stackRest) altStack).imp
                    fun result evaluated =>
                      .rot top second third stackRest altStack rest flags ctx result evaluated
              | OP_2ROT =>
                  refine exists_of_arity6 rfl
                    fun top second third fourth fifth sixth stackRest => ?_
                  exact (next (fifth :: sixth :: top :: second :: third :: fourth :: stackRest)
                    altStack).imp fun result evaluated =>
                      .twoRot top second third fourth fifth sixth stackRest altStack rest
                        flags ctx result evaluated
              | OP_2SWAP =>
                  refine exists_of_arity4 rfl fun top second third fourth stackRest => ?_
                  exact (next (third :: fourth :: top :: second :: stackRest) altStack).imp
                    fun result evaluated =>
                      .twoSwap top second third fourth stackRest altStack rest flags ctx
                        result evaluated
              | OP_SWAP =>
                  refine exists_of_arity2 rfl fun top belowTop stackRest => ?_
                  exact (next (belowTop :: top :: stackRest) altStack).imp
                    fun result evaluated =>
                      .swap top belowTop stackRest altStack rest flags ctx result evaluated
              | OP_TOALTSTACK =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next stackRest (top :: altStack)).imp fun result evaluated =>
                    .toAltStack top stackRest altStack rest flags ctx result evaluated
              | OP_FROMALTSTACK =>
                  cases altStack with
                  | nil =>
                      exact ⟨.failure .altStackUnderflow,
                        .fromaltstack_underflow rest stack flags ctx⟩
                  | cons top altRest =>
                      exact (next (top :: stack) altRest).imp fun result evaluated =>
                        .fromAltStack top stack altRest rest flags ctx result evaluated
              | OP_1ADD =>
                  refine exists_of_unaryArithmetic rfl rfl
                    fun operand stackRest value decoded => ?_
                  exact (next (scriptNum (value + 1) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .oneAdd operand value stackRest altStack rest flags ctx result
                        decoded evaluated
              | OP_1SUB =>
                  refine exists_of_unaryArithmetic rfl rfl
                    fun operand stackRest value decoded => ?_
                  exact (next (scriptNum (value - 1) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .oneSub operand value stackRest altStack rest flags ctx result
                        decoded evaluated
              | OP_NEGATE =>
                  refine exists_of_unaryArithmetic rfl rfl
                    fun operand stackRest value decoded => ?_
                  exact (next (scriptNum (-value) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .negate operand value stackRest altStack rest flags ctx result
                        decoded evaluated
              | OP_ABS =>
                  refine exists_of_unaryArithmetic rfl rfl
                    fun operand stackRest value decoded => ?_
                  exact (next (scriptNum (if value < 0 then -value else value) :: stackRest)
                    altStack).imp fun result evaluated =>
                      .abs operand value stackRest altStack rest flags ctx result
                        decoded evaluated
              | OP_SUB =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (scriptNum (b - a) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .sub top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_MIN =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (scriptNum (Min.min b a) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .min top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_MAX =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (scriptNum (Max.max b a) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .max top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_NUMNOTEQUAL =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (decide (a ≠ b)) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .numNotEqual top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_LESSTHAN =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (decide (b < a)) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .lessThan top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_GREATERTHAN =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (decide (b > a)) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .greaterThan top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_LESSTHANOREQUAL =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (decide (b ≤ a)) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .lessThanOrEqual top belowTop a b stackRest rest altStack flags ctx
                        result decoded evaluated
              | OP_GREATERTHANOREQUAL =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (decide (b ≥ a)) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .greaterThanOrEqual top belowTop a b stackRest rest altStack flags ctx
                        result decoded evaluated
              | OP_ADD =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (scriptNum (a + b) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .add top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_BOOLAND =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement ((a != 0) && (b != 0)) :: stackRest)
                    altStack).imp fun result evaluated =>
                      .booland top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_BOOLOR =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement ((a != 0) || (b != 0)) :: stackRest)
                    altStack).imp fun result evaluated =>
                      .boolor top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_WITHIN =>
                  refine exists_of_arity3 rfl
                    fun upperBytes lowerBytes valueBytes stackRest => ?_
                  cases decoded : decodeWithinScriptNums flags
                      upperBytes lowerBytes valueBytes with
                  | error error =>
                      exact ⟨.failure error, .within_scriptnum_failure
                        upperBytes lowerBytes valueBytes stackRest rest altStack
                        flags ctx error decoded⟩
                  | ok values =>
                      rcases values with ⟨upper, lower, value⟩
                      exact (next
                          (boolToElement (decide (lower ≤ value ∧ value < upper)) ::
                            stackRest) altStack).imp fun result evaluated =>
                        .within upperBytes lowerBytes valueBytes upper lower value
                          stackRest altStack rest flags ctx result decoded evaluated
              | OP_NOT =>
                  refine exists_of_arity1 rfl fun operand stackRest => ?_
                  cases decoded : decodeScriptNum operand flags.minimalData
                      maxArithmeticScriptNumBytes with
                  | error error =>
                      exact ⟨.failure error, .not_scriptnum_failure operand
                        stackRest rest altStack flags ctx error decoded⟩
                  | ok value =>
                      exact (next (boolToElement (value == 0) :: stackRest) altStack).imp
                        fun result evaluated =>
                          .op_not operand value stackRest altStack rest flags ctx result
                            decoded evaluated
              | OP_0NOTEQUAL =>
                  refine exists_of_arity1 rfl fun operand stackRest => ?_
                  cases decoded : decodeScriptNum operand flags.minimalData
                      maxArithmeticScriptNumBytes with
                  | error error =>
                      exact ⟨.failure error, .unary_scriptnum_failure operand
                        stackRest rest altStack flags ctx error decoded⟩
                  | ok value =>
                      exact (next (boolToElement (value != 0) :: stackRest) altStack).imp
                        fun result evaluated =>
                          .zeroNotEqual operand value stackRest altStack rest flags ctx
                            result decoded evaluated
              | OP_EQUAL =>
                  refine exists_of_arity2 rfl fun top belowTop stackRest => ?_
                  by_cases equal : top = belowTop
                  · exact (next (trueElement :: stackRest) altStack).imp
                      fun result evaluated =>
                        .equal_true top belowTop stackRest rest altStack flags ctx result
                          equal evaluated
                  · exact (next (falseElement :: stackRest) altStack).imp
                      fun result evaluated =>
                        .equal_false top belowTop stackRest rest altStack flags ctx result
                          equal evaluated
              | OP_EQUALVERIFY =>
                  refine exists_of_arity2 rfl fun top belowTop stackRest => ?_
                  by_cases equal : top = belowTop
                  · exact (next stackRest altStack).imp fun result evaluated =>
                      .equalverify_success top belowTop stackRest rest altStack flags ctx
                        result equal evaluated
                  · exact ⟨.failure .equalVerify,
                      .equalverify_failure top belowTop stackRest rest altStack
                        flags ctx equal⟩
              | OP_NUMEQUAL =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  exact (next (boolToElement (a == b) :: stackRest) altStack).imp
                    fun result evaluated =>
                      .numequal top belowTop a b stackRest rest altStack flags ctx result
                        decoded evaluated
              | OP_NUMEQUALVERIFY =>
                  refine exists_of_binaryScriptNums rfl rfl
                    fun top belowTop stackRest a b decoded => ?_
                  by_cases equal : a = b
                  · exact (next stackRest altStack).imp fun result evaluated =>
                      .numequalverify_success top belowTop a b stackRest rest altStack
                        flags ctx result decoded equal evaluated
                  · exact ⟨.failure .numEqualVerify,
                      .numequalverify_failure top belowTop a b stackRest rest
                        altStack flags ctx decoded equal⟩
              | OP_SHA256 =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (sha256 top :: stackRest) altStack).imp fun result evaluated =>
                    .op_sha256 top stackRest rest altStack flags ctx result evaluated
              | OP_HASH256 =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (hash256 top :: stackRest) altStack).imp fun result evaluated =>
                    .op_hash256 top stackRest rest altStack flags ctx result evaluated
              | OP_RIPEMD160 =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (ripemd160 top :: stackRest) altStack).imp
                    fun result evaluated =>
                      .op_ripemd160 top stackRest rest altStack flags ctx result evaluated
              | OP_HASH160 =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (hash160 top :: stackRest) altStack).imp fun result evaluated =>
                    .op_hash160 top stackRest rest altStack flags ctx result evaluated
              | OP_CHECKSIG =>
                  refine exists_of_arity2 rfl fun pubkey sig stackRest => ?_
                  cases hChecked : checkSigWithEncoding checkSig checkSchnorrSig
                      flags ctx sig pubkey with
                  | error error =>
                      exact ⟨.failure error, .checksig_encoding_failure pubkey
                        sig stackRest rest altStack flags ctx error hChecked⟩
                  | ok checked =>
                      cases checked with
                      | false =>
                          exact (next (falseElement :: stackRest) altStack).imp
                            fun result evaluated =>
                              .checksig_failure pubkey sig stackRest rest altStack flags
                                ctx result hChecked evaluated
                      | true =>
                          exact (next (trueElement :: stackRest) altStack).imp
                            fun result evaluated =>
                              .checksig_success pubkey sig stackRest rest altStack flags
                                ctx result hChecked evaluated
              | OP_CHECKSIGVERIFY =>
                  refine exists_of_arity2 rfl fun pubkey sig stackRest => ?_
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
                          exact (next stackRest altStack).imp fun result evaluated =>
                            .checksigverify_success pubkey sig stackRest rest altStack
                              flags ctx result hChecked evaluated
              | OP_CHECKSIGADD =>
                  by_cases available : ctx.sigVersion = .tapscript
                  · have arity : Opcode.activeFixedMainStackInputs? .OP_CHECKSIGADD
                        ctx.sigVersion = some 3 := by
                      simp [Opcode.activeFixedMainStackInputs?, available]
                    refine exists_of_arity3 arity fun pubkey countBytes sig stackRest => ?_
                    cases hDecoded : decodeCheckSigAddCount flags ctx countBytes with
                    | error error =>
                        exact ⟨.failure error, .checksigadd_scriptnum_failure pubkey
                          countBytes sig stackRest rest altStack flags ctx error available
                          hDecoded⟩
                    | ok count =>
                        cases hChecked : checkSigWithEncoding checkSig checkSchnorrSig
                            flags ctx sig pubkey with
                        | error error =>
                            exact ⟨.failure error, .checksigadd_encoding_failure pubkey
                              countBytes sig count stackRest rest altStack flags ctx error
                              hDecoded hChecked⟩
                        | ok checked =>
                            cases checked with
                            | false =>
                                exact (next (scriptNum count :: stackRest) altStack).imp
                                  fun result evaluated =>
                                    .checksigadd_failure pubkey countBytes sig count
                                      stackRest rest altStack flags ctx result hDecoded
                                      hChecked evaluated
                            | true =>
                                exact (next (scriptNum (count + 1) :: stackRest)
                                  altStack).imp fun result evaluated =>
                                    .checksigadd_success pubkey countBytes sig count
                                      stackRest rest altStack flags ctx result hDecoded
                                      hChecked evaluated
                  · exact ⟨.failure .badOpcode,
                      .checksigadd_unavailable stack rest altStack flags ctx available⟩
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
                                    exact (next (falseElement :: operands.rest) altStack).imp
                                      fun result evaluated =>
                                        .checkmultisig_failure stack operands rest altStack
                                          flags ctx result hDecoded hChecked nullFail hDummy
                                          evaluated
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
                                  exact (next (trueElement :: operands.rest) altStack).imp
                                    fun result evaluated =>
                                      .checkmultisig_success stack operands rest altStack
                                        flags ctx result hDecoded hChecked hDummy evaluated
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
                                  exact (next operands.rest altStack).imp
                                    fun result evaluated =>
                                      .checkmultisigverify_success stack operands rest
                                        altStack flags ctx result hDecoded hChecked hDummy
                                        evaluated
              | OP_CHECKSEQUENCEVERIFY =>
                  refine exists_of_arity1 rfl fun operand stackRest => ?_
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
                        · exact (next (operand :: stackRest) altStack).imp
                            fun result evaluated =>
                              .checksequenceverify_success operand value stackRest rest
                                altStack flags ctx result hDecoded nonnegative satisfied
                                evaluated
                        · exact ⟨.failure .checkSequenceVerify,
                            .checksequenceverify_failure operand value stackRest rest
                              altStack flags ctx hDecoded nonnegative satisfied⟩
              | OP_CHECKLOCKTIMEVERIFY =>
                  refine exists_of_arity1 rfl fun operand stackRest => ?_
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
                        · exact (next (operand :: stackRest) altStack).imp
                            fun result evaluated =>
                              .checklocktimeverify_success operand value stackRest rest
                                altStack flags ctx result hDecoded nonnegative satisfied
                                evaluated
                        · exact ⟨.failure .checkLockTimeVerify,
                            .checklocktimeverify_failure operand value stackRest rest
                              altStack flags ctx hDecoded nonnegative satisfied⟩
              | OP_VERIFY =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  cases hTruthy : castToBool top with
                  | false =>
                      exact ⟨.failure .verify,
                        .verify_failure top stackRest rest altStack flags ctx hTruthy⟩
                  | true =>
                      exact (next stackRest altStack).imp fun result evaluated =>
                        .verify_success top stackRest rest altStack flags ctx result
                          hTruthy evaluated
              | OP_SIZE =>
                  refine exists_of_arity1 rfl fun top stackRest => ?_
                  exact (next (scriptNat top.size :: top :: stackRest) altStack).imp
                    fun result evaluated =>
                      .size top stackRest altStack rest flags ctx result evaluated

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

end LeanMiniscript.Script
