import LeanMiniscript.Script.BigStep
import LeanMiniscript.Script.BigStepProofs.Determinism

namespace LeanMiniscript.Script

/-!
# Big-step proofs: totality

Every script in the modeled opcode subset has exactly one big-step result.
-/

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

end LeanMiniscript.Script
