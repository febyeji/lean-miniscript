import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A successful suffix after a balanced prefix can be replaced whenever the
replacement preserves every successful execution of that suffix. -/
theorem Eval.replaceSuccessfulSuffix
    {prefixScript suffix replacement : Script}
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow prefixScript)
    (replace : ∀ {middle middleAlt final finalAlt : Stack},
      Eval suffix middle middleAlt flags ctx (.success final finalAlt) →
      Eval replacement middle middleAlt flags ctx (.success final finalAlt))
    (run : Eval (prefixScript ++ suffix) stack altStack flags ctx
      (.success out outAlt)) :
    Eval (prefixScript ++ replacement) stack altStack flags ctx
      (.success out outAlt) := by
  induction balanced generalizing suffix replacement stack altStack out outAlt with
  | nil =>
      simpa using replace run
  | append leftBalanced rightBalanced leftIH rightIH =>
      rw [List.append_assoc] at run ⊢
      apply leftIH (suffix := _ ++ suffix) (replacement := _ ++ replacement) ?_ run
      intro middle middleAlt final finalAlt rightRun
      exact rightIH replace rightRun
  | atom nonConditional =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run <;>
        simp_all [NonConditional] <;>
        grind [Eval]
  | @ifThen body bodyBalanced bodyIH =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run
      case if_execute =>
          rename_i top rest frame split minimal selected
          cases resultEq
          have expectedSplit := splitConditional_balanced_ifThen bodyBalanced
            (suffix := suffix)
          have scriptEq :
              ((([] : Script).append body).append [.op .OP_ENDIF]).append suffix =
                body ++ [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
          cases selectedBool : castToBool top
          case false =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.if_execute top rest altStack
              (body ++ [.op .OP_ENDIF] ++ replacement)
              { branches := [body], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.if_execute top rest altStack
              (body ++ [.op .OP_ENDIF] ++ replacement)
              { branches := [body], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                bodyIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
      case if_unbalanced =>
          rename_i top rest selectedResult split minimal selected
          have expectedSplit := splitConditional_balanced_ifThen bodyBalanced
            (suffix := suffix)
          have scriptEq :
              ((([] : Script).append body).append [.op .OP_ENDIF]).append suffix =
                body ++ [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
      all_goals cases resultEq

  | @notifThen body bodyBalanced bodyIH =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run
      case notif_execute =>
          rename_i top rest frame split minimal selected
          cases resultEq
          have expectedSplit := splitConditional_balanced_ifThen bodyBalanced
            (suffix := suffix)
          have scriptEq :
              ((([] : Script).append body).append [.op .OP_ENDIF]).append suffix =
                body ++ [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
          cases selectedBool : castToBool top
          case false =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.notif_execute top rest altStack
              (body ++ [.op .OP_ENDIF] ++ replacement)
              { branches := [body], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                bodyIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.notif_execute top rest altStack
              (body ++ [.op .OP_ENDIF] ++ replacement)
              { branches := [body], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
      case notif_unbalanced =>
          rename_i top rest selectedResult split minimal selected
          have expectedSplit := splitConditional_balanced_ifThen bodyBalanced
            (suffix := suffix)
          have scriptEq :
              ((([] : Script).append body).append [.op .OP_ENDIF]).append suffix =
                body ++ [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
      all_goals cases resultEq
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run
      case if_execute =>
          rename_i top rest frame split minimal selected
          cases resultEq
          have expectedSplit := splitConditional_balanced_ifElse
            thenBalanced elseBalanced (suffix := suffix)
          have scriptEq :
              ((((([] : Script).append thenBranch).append [.op .OP_ELSE]).append
                elseBranch).append [.op .OP_ENDIF]).append suffix =
                thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                  [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
          cases selectedBool : castToBool top
          case false =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.if_execute top rest altStack
              (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                [.op .OP_ENDIF] ++ replacement)
              { branches := [thenBranch, elseBranch], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                elseIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.if_execute top rest altStack
              (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                [.op .OP_ENDIF] ++ replacement)
              { branches := [thenBranch, elseBranch], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                thenIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
      case if_unbalanced =>
          rename_i top rest selectedResult split minimal selected
          have expectedSplit := splitConditional_balanced_ifElse
            thenBalanced elseBalanced (suffix := suffix)
          have scriptEq :
              ((((([] : Script).append thenBranch).append [.op .OP_ELSE]).append
                elseBranch).append [.op .OP_ENDIF]).append suffix =
                thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                  [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
      all_goals cases resultEq
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run
      case notif_execute =>
          rename_i top rest frame split minimal selected
          cases resultEq
          have expectedSplit := splitConditional_balanced_ifElse
            thenBalanced elseBalanced (suffix := suffix)
          have scriptEq :
              ((((([] : Script).append thenBranch).append [.op .OP_ELSE]).append
                elseBranch).append [.op .OP_ENDIF]).append suffix =
                thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                  [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
          cases selectedBool : castToBool top
          case false =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.notif_execute top rest altStack
              (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                [.op .OP_ENDIF] ++ replacement)
              { branches := [thenBranch, elseBranch], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                thenIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := Eval.notif_execute top rest altStack
              (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                [.op .OP_ENDIF] ++ replacement)
              { branches := [thenBranch, elseBranch], after := replacement }
              flags ctx (.success out outAlt)
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using
                elseIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
      case notif_unbalanced =>
          rename_i top rest selectedResult split minimal selected
          have expectedSplit := splitConditional_balanced_ifElse
            thenBalanced elseBalanced (suffix := suffix)
          have scriptEq :
              ((((([] : Script).append thenBranch).append [.op .OP_ELSE]).append
                elseBranch).append [.op .OP_ENDIF]).append suffix =
                thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
                  [.op .OP_ENDIF] ++ suffix := by
            simp [List.append_assoc]
          rw [scriptEq, expectedSplit] at split
          cases split
      all_goals cases resultEq

@[simp] private theorem castToBool_falseElement :
    castToBool falseElement = false := by
  native_decide

@[simp] private theorem castToBool_trueElement :
    castToBool trueElement = true := by
  native_decide

@[simp] private theorem castToBool_boolToElement (value : Bool) :
    castToBool (boolToElement value) = value := by
  cases value <;> simp [boolToElement]

/-- A successful `EQUAL VERIFY` execution is preserved by `EQUALVERIFY`. -/
theorem Eval.fuseEqualVerify
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_EQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_EQUALVERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case equal_true =>
    rename_i a b rest equal next
    cases next <;> simp_all <;> grind [Eval]
  case equal_false =>
    rename_i a b rest notEqual next
    cases next <;> simp_all <;> grind [Eval]
  all_goals cases resultEq

/-- A successful `CHECKSIG VERIFY` execution is preserved by
`CHECKSIGVERIFY`. -/
theorem Eval.fuseCheckSigVerify
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_CHECKSIGVERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case checksig_success =>
    rename_i pubkey sig rest checked next
    cases next <;> simp_all <;> grind [Eval]
  case checksig_failure =>
    rename_i pubkey sig rest checked next
    cases next <;> simp_all <;> grind [Eval]
  all_goals cases resultEq

/-- A successful `CHECKMULTISIG VERIFY` execution is preserved by
`CHECKMULTISIGVERIFY`. -/
theorem Eval.fuseCheckMultiSigVerify
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKMULTISIG, .op .OP_VERIFY]
      stack altStack flags ctx (.success out outAlt)) :
    Eval [.op .OP_CHECKMULTISIGVERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case checkmultisig_success =>
    rename_i operands dummy checked decoded next
    cases resultEq
    have verified : Eval [.op .OP_VERIFY]
        (trueElement :: operands.rest) altStack flags ctx
        (.success operands.rest altStack) :=
      Eval.verifyTrue castToBool_trueElement Eval.done
    have sameResult := Eval.result_unique next verified
    cases sameResult
    exact Eval.checkmultisigverify_success stack operands [] altStack flags ctx
      (.success operands.rest altStack) decoded checked dummy Eval.done
  case checkmultisig_failure =>
    rename_i operands decoded checked nullFail dummy next
    cases resultEq
    have rejected : Eval [.op .OP_VERIFY]
        (falseElement :: operands.rest) altStack flags ctx (.failure .verify) :=
      Eval.verifyFalse castToBool_falseElement
    have sameResult := Eval.result_unique next rejected
    cases sameResult
  all_goals cases resultEq

/-- A successful `NUMEQUAL VERIFY` execution is preserved by
`NUMEQUALVERIFY`. -/
theorem Eval.fuseNumEqualVerify
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_NUMEQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_NUMEQUALVERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case numequal =>
    rename_i aBytes bBytes a b rest decoded next
    cases next <;> simp_all <;> grind [Eval]
  all_goals cases resultEq

/-- Folding a terminal `VERIFY` into a specialized opcode preserves every
successful execution of a balanced script. -/
theorem Eval.compileVerify_success
    {script : Script} {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow script)
    (run : Eval (script ++ [.op .OP_VERIFY]) stack altStack flags ctx
      (.success out outAlt)) :
    Eval (compileVerify script) stack altStack flags ctx
      (.success out outAlt) := by
  induction balanced generalizing stack altStack out outAlt with
  | nil => simpa using run
  | @atom element nonConditional =>
      cases element with
      | pushData data =>
          simpa [compileVerify, verifyReplacement?] using run
      | pushNum number =>
          simpa [compileVerify, verifyReplacement?] using run
      | op opcode =>
          cases opcode <;>
            simp [compileVerify, verifyReplacement?] at run ⊢
          all_goals first
            | exact Eval.fuseEqualVerify run
            | exact Eval.fuseCheckSigVerify run
            | exact Eval.fuseCheckMultiSigVerify run
            | exact Eval.fuseNumEqualVerify run
            | exact run
  | @append left right leftBalanced rightBalanced leftIH rightIH =>
      rcases List.eq_nil_or_concat right with rfl | ⟨initScript, last, rfl⟩
      · have verified := leftIH (by simpa using run)
        simpa using verified
      · simp only [List.concat_eq_append] at rightBalanced rightIH ⊢
        have replaced : Eval
            (left ++ compileVerify (initScript ++ [last]))
            stack altStack flags ctx (.success out outAlt) :=
          Eval.replaceSuccessfulSuffix leftBalanced
            (replace := fun rightRun => rightIH rightRun)
            (by simpa [List.append_assoc] using run)
        rw [← List.append_assoc]
        rw [compileVerify_append_singleton]
        rw [compileVerify_append_singleton] at replaced
        cases replacementEq : verifyReplacement? last <;>
          simp [replacementEq, List.append_assoc] at replaced ⊢
        all_goals exact replaced
  | @ifThen body bodyBalanced bodyIH =>
      change Eval
        (compileVerify (([.op .OP_IF] ++ body) ++ [.op .OP_ENDIF]))
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifThen body bodyBalanced bodyIH =>
      change Eval
        (compileVerify (([.op .OP_NOTIF] ++ body) ++ [.op .OP_ENDIF]))
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        (compileVerify
          (([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
            [.op .OP_ENDIF]))
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        (compileVerify
          (([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
            [.op .OP_ENDIF]))
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run

end LeanMiniscript.Miniscript
