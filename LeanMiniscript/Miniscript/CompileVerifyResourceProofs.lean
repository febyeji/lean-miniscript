import LeanMiniscript.Miniscript.CompileVerifyProofs
import LeanMiniscript.Script.ExecutionResources

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Resource preservation for terminal VERIFY fusion

The specialized VERIFY opcodes remove an intermediate Boolean stack state.
These theorems show that a successful fusion preserves both the combined stack
peak and the dynamic multisignature key charge recorded by `EvalResources`.
-/

/-- Fusing `EQUAL VERIFY` into `EQUALVERIFY` preserves the exact successful
resource observation. -/
theorem EvalResources.fuseEqualVerify
    {stack altStack out outAlt : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_EQUAL, .op .OP_VERIFY]
      stack altStack flags ctx out outAlt resources) :
    EvalResources [.op .OP_EQUALVERIFY] stack altStack flags ctx
      out outAlt resources := by
  cases run
  case step head tail =>
    rename_i nextStack nextAlt tailResources
    cases tail
    case step verify finish =>
      cases finish
      have fused : Eval [.op .OP_EQUALVERIFY] stack altStack flags ctx
          (.success out outAlt) :=
        Eval.fuseEqualVerify (by simpa using Eval.append head verify)
      have observed := EvalResources.step fused
        (EvalResources.empty out outAlt flags ctx)
      generalize headEq : ExecResult.success nextStack nextAlt = headResult at head
      cases head
      case equal_true =>
        rename_i a b rest equal next
        cases next
        cases headEq
        have resourcesEq :
            ExecutionResources.prepend (a :: b :: rest) altStack 0
                (ExecutionResources.prepend (trueElement :: rest) altStack 0
                  (ExecutionResources.initial out outAlt)) =
              ExecutionResources.prepend (a :: b :: rest) altStack 0
                (ExecutionResources.initial out outAlt) := by
          simp [ExecutionResources.prepend, ExecutionResources.initial]
          omega
        simpa [executedMultiSigKeyCharge, resourcesEq] using observed
      case equal_false =>
        rename_i a b rest notEqual next
        cases next
        cases headEq
        have expectedVerify : Eval [.op .OP_VERIFY] (falseElement :: rest)
            altStack flags ctx (.failure .verify) :=
          .verify_failure falseElement rest [] altStack flags ctx rfl
        have impossible := Eval.result_unique verify expectedVerify
        cases impossible
      all_goals cases headEq

/-- Fusing `CHECKSIG VERIFY` into `CHECKSIGVERIFY` preserves the exact
successful resource observation. -/
theorem EvalResources.fuseCheckSigVerify
    {stack altStack out outAlt : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_CHECKSIG, .op .OP_VERIFY]
      stack altStack flags ctx out outAlt resources) :
    EvalResources [.op .OP_CHECKSIGVERIFY] stack altStack flags ctx
      out outAlt resources := by
  cases run
  case step head tail =>
    rename_i nextStack nextAlt tailResources
    cases tail
    case step verify finish =>
      cases finish
      generalize headEq : ExecResult.success nextStack nextAlt = headResult at head
      cases head
      case checksig_success =>
        rename_i pubkey sig rest checked next
        cases next
        cases headEq
        have expectedVerify : Eval [.op .OP_VERIFY] (trueElement :: rest)
            altStack flags ctx (.success rest altStack) :=
          .verify_success trueElement rest [] altStack flags ctx _ rfl
            (.empty rest altStack flags ctx)
        have sameResult := Eval.result_unique verify expectedVerify
        injection sameResult with outEq outAltEq
        subst out
        subst outAlt
        have fused : Eval [.op .OP_CHECKSIGVERIFY]
            (pubkey :: sig :: rest) altStack flags ctx
            (.success rest altStack) :=
          .checksigverify_success pubkey sig rest [] altStack flags ctx _
            checked (.empty rest altStack flags ctx)
        have observed := EvalResources.step fused
          (EvalResources.empty rest altStack flags ctx)
        have resourcesEq :
            ExecutionResources.prepend (pubkey :: sig :: rest) altStack 0
                (ExecutionResources.prepend (trueElement :: rest) altStack 0
                  (ExecutionResources.initial rest altStack)) =
              ExecutionResources.prepend (pubkey :: sig :: rest) altStack 0
                (ExecutionResources.initial rest altStack) := by
          simp [ExecutionResources.prepend, ExecutionResources.initial]
          omega
        simpa [executedMultiSigKeyCharge, resourcesEq] using observed
      case checksig_failure =>
        rename_i pubkey sig rest checked next
        cases next
        cases headEq
        have expectedVerify : Eval [.op .OP_VERIFY] (falseElement :: rest)
            altStack flags ctx (.failure .verify) :=
          .verify_failure falseElement rest [] altStack flags ctx rfl
        have impossible := Eval.result_unique verify expectedVerify
        cases impossible
      all_goals cases headEq

private theorem decodedMultiRestSuccLe
    {flags : ScriptFlags} {ctx : TxContext} {stack : Stack}
    {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands)
    (dummyOk : checkMultiSigDummy flags operands.dummy = .ok ()) :
    operands.rest.length + 1 ≤ stack.length := by
  unfold decodeCheckMultiSigOperandsFor at decoded
  split at decoded
  · contradiction
  · unfold decodeCheckMultiSigOperands at decoded
    split at decoded <;> simp only [bind, Except.bind] at decoded
    · contradiction
    · repeat' (split at decoded <;> try simp only [bind, Except.bind] at decoded)
      all_goals simp_all
      all_goals subst operands
      · simp [checkMultiSigDummy] at dummyOk
      · rename_i _ _ _ keyFrame _ _ _ _ signatureFrame
        have keyLength := congrArg List.length keyFrame
        have signatureLength := congrArg List.length signatureFrame
        simp only [List.length_drop, List.length_cons] at keyLength signatureLength
        dsimp only
        omega

/-- Fusing `CHECKMULTISIG VERIFY` into `CHECKMULTISIGVERIFY` preserves the
exact successful resource observation, including the decoded key charge. -/
theorem EvalResources.fuseCheckMultiSigVerify
    {stack altStack out outAlt : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_CHECKMULTISIG, .op .OP_VERIFY]
      stack altStack flags ctx out outAlt resources) :
    EvalResources [.op .OP_CHECKMULTISIGVERIFY] stack altStack flags ctx
      out outAlt resources := by
  cases run
  case step head tail =>
    rename_i nextStack nextAlt tailResources
    cases tail
    case step verify finish =>
      cases finish
      generalize headEq : ExecResult.success nextStack nextAlt = headResult at head
      cases head
      case checkmultisig_success =>
        rename_i operands dummy checked decoded next
        cases next
        cases headEq
        have expectedVerify : Eval [.op .OP_VERIFY]
            (trueElement :: operands.rest) altStack flags ctx
            (.success operands.rest altStack) :=
          .verify_success trueElement operands.rest [] altStack flags ctx _ rfl
            (.empty operands.rest altStack flags ctx)
        have sameResult := Eval.result_unique verify expectedVerify
        injection sameResult with outEq outAltEq
        subst out
        subst outAlt
        have fused : Eval [.op .OP_CHECKMULTISIGVERIFY] stack altStack
            flags ctx (.success operands.rest altStack) :=
          .checkmultisigverify_success stack operands [] altStack flags ctx _
            decoded checked dummy (.empty operands.rest altStack flags ctx)
        have observed := EvalResources.step fused
          (EvalResources.empty operands.rest altStack flags ctx)
        have remaining := decodedMultiRestSuccLe decoded dummy
        have resourcesEq :
            ExecutionResources.prepend stack altStack operands.pubkeys.length
                (ExecutionResources.prepend (trueElement :: operands.rest)
                  altStack 0
                  (ExecutionResources.initial operands.rest altStack)) =
              ExecutionResources.prepend stack altStack operands.pubkeys.length
                (ExecutionResources.initial operands.rest altStack) := by
          simp [ExecutionResources.prepend, ExecutionResources.initial]
          omega
        simpa [executedMultiSigKeyCharge, decoded, resourcesEq] using observed
      case checkmultisig_failure =>
        rename_i operands decoded checked nullFail dummy next
        cases next
        cases headEq
        have expectedVerify : Eval [.op .OP_VERIFY]
            (falseElement :: operands.rest) altStack flags ctx
            (.failure .verify) :=
          .verify_failure falseElement operands.rest [] altStack flags ctx rfl
        have impossible := Eval.result_unique verify expectedVerify
        cases impossible
      all_goals cases headEq

/-- Fusing `NUMEQUAL VERIFY` into `NUMEQUALVERIFY` preserves the exact
successful resource observation. -/
theorem EvalResources.fuseNumEqualVerify
    {stack altStack out outAlt : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {resources : ExecutionResources}
    (run : EvalResources [.op .OP_NUMEQUAL, .op .OP_VERIFY]
      stack altStack flags ctx out outAlt resources) :
    EvalResources [.op .OP_NUMEQUALVERIFY] stack altStack flags ctx
      out outAlt resources := by
  cases run
  case step head tail =>
    rename_i nextStack nextAlt tailResources
    cases tail
    case step verify finish =>
      cases finish
      have fused : Eval [.op .OP_NUMEQUALVERIFY] stack altStack flags ctx
          (.success out outAlt) :=
        Eval.fuseNumEqualVerify (by simpa using Eval.append head verify)
      have observed := EvalResources.step fused
        (EvalResources.empty out outAlt flags ctx)
      generalize headEq : ExecResult.success nextStack nextAlt = headResult at head
      cases head
      case numequal =>
        rename_i aBytes bBytes a b rest decoded next
        cases next
        cases headEq
        have resourcesEq :
            ExecutionResources.prepend (aBytes :: bBytes :: rest) altStack 0
                (ExecutionResources.prepend
                  (boolToElement (a == b) :: rest) altStack 0
                  (ExecutionResources.initial out outAlt)) =
              ExecutionResources.prepend (aBytes :: bBytes :: rest) altStack 0
                (ExecutionResources.initial out outAlt) := by
          simp [ExecutionResources.prepend, ExecutionResources.initial]
          omega
        simpa [executedMultiSigKeyCharge, resourcesEq] using observed
      all_goals cases headEq

private theorem singletonIfSuccessFalse
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_IF] stack altStack flags ctx (.success out outAlt)) :
    False := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case if_execute split minimal selected =>
    have noSplit : splitConditional [] = none := rfl
    rw [noSplit] at split
    contradiction
  case if_unbalanced selectedResult split minimal selected =>
    cases selectedResult <;> simp [finishUnclosedConditional] at resultEq
  all_goals cases resultEq

private theorem singletonNotIfSuccessFalse
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_NOTIF] stack altStack flags ctx (.success out outAlt)) :
    False := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case notif_execute split minimal selected =>
    have noSplit : splitConditional [] = none := rfl
    rw [noSplit] at split
    contradiction
  case notif_unbalanced selectedResult split minimal selected =>
    cases selectedResult <;> simp [finishUnclosedConditional] at resultEq
  all_goals cases resultEq

/-- Replacing a successful suffix after a balanced prefix preserves the exact
resource observation when the suffix replacement itself does. -/
theorem EvalResources.replaceSuccessfulSuffix
    {prefixScript suffix replacement : Script}
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {resources : ExecutionResources}
    (balanced : BalancedControlFlow prefixScript)
    (replace : ∀ {middle middleAlt final finalAlt : Stack}
      {suffixResources : ExecutionResources},
      EvalResources suffix middle middleAlt flags ctx final finalAlt
        suffixResources →
      EvalResources replacement middle middleAlt flags ctx final finalAlt
        suffixResources)
    (run : EvalResources (prefixScript ++ suffix) stack altStack flags ctx
      out outAlt resources) :
    EvalResources (prefixScript ++ replacement) stack altStack flags ctx
      out outAlt resources := by
  induction balanced generalizing suffix replacement stack altStack out outAlt resources with
  | nil =>
      simpa using replace run
  | append leftBalanced rightBalanced leftIH rightIH =>
      rw [List.append_assoc] at run ⊢
      apply leftIH (suffix := _ ++ suffix) (replacement := _ ++ replacement) ?_ run
      intro middle middleAlt final finalAlt suffixResources rightRun
      exact rightIH replace rightRun
  | atom nonConditional =>
      cases run <;>
        simp_all [NonConditional] <;>
        grind [EvalResources]
  | @ifThen body bodyBalanced bodyIH =>
      cases run
      case step head tail =>
          exact (singletonIfSuccessFalse head).elim
      case if_execute split minimal selected =>
          rename_i top rest frame selectedResources
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
            have rebuilt := EvalResources.if_execute
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := EvalResources.if_execute
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using bodyIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
  | @notifThen body bodyBalanced bodyIH =>
      cases run
      case step head tail =>
          exact (singletonNotIfSuccessFalse head).elim
      case notif_execute split minimal selected =>
          rename_i top rest frame selectedResources
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
            have rebuilt := EvalResources.notif_execute
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using bodyIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := EvalResources.notif_execute
              (splitConditional_balanced_ifThen bodyBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      cases run
      case step head tail =>
          exact (singletonIfSuccessFalse head).elim
      case if_execute split minimal selected =>
          rename_i top rest frame selectedResources
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
            have rebuilt := EvalResources.if_execute
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using elseIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := EvalResources.if_execute
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using thenIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      cases run
      case step head tail =>
          exact (singletonNotIfSuccessFalse head).elim
      case notif_execute split minimal selected =>
          rename_i top rest frame selectedResources
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
            have rebuilt := EvalResources.notif_execute
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using thenIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches, selectedBool] at selected
            have rebuilt := EvalResources.notif_execute
              (splitConditional_balanced_ifElse thenBalanced elseBalanced) minimal
              (by simpa [ConditionalFrame.select, selectConditionalBranches,
                  selectedBool] using elseIH replace selected)
            simpa only [List.nil_append, List.cons_append, List.singleton_append,
              List.append_assoc] using rebuilt

/-- Folding a terminal `VERIFY` into a specialized opcode preserves the exact
successful resource observation of every balanced script. -/
theorem EvalResources.compileVerify_success
    {script : Script} {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    {resources : ExecutionResources}
    (balanced : BalancedControlFlow script)
    (run : EvalResources (script ++ [.op .OP_VERIFY]) stack altStack flags ctx
      out outAlt resources) :
    EvalResources (compileVerify script) stack altStack flags ctx
      out outAlt resources := by
  induction balanced generalizing stack altStack out outAlt resources with
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
            | exact EvalResources.fuseEqualVerify run
            | exact EvalResources.fuseCheckSigVerify run
            | exact EvalResources.fuseCheckMultiSigVerify run
            | exact EvalResources.fuseNumEqualVerify run
            | exact run
  | @append left right leftBalanced rightBalanced leftIH rightIH =>
      rcases List.eq_nil_or_concat right with rfl | ⟨initScript, last, rfl⟩
      · have verified := leftIH (by simpa using run)
        simpa using verified
      · simp only [List.concat_eq_append] at rightBalanced rightIH ⊢
        have replaced : EvalResources
            (left ++ compileVerify (initScript ++ [last]))
            stack altStack flags ctx out outAlt resources :=
          EvalResources.replaceSuccessfulSuffix leftBalanced
            (replace := fun rightRun => rightIH rightRun)
            (by simpa [List.append_assoc] using run)
        rw [← List.append_assoc]
        rw [compileVerify_append_singleton]
        rw [compileVerify_append_singleton] at replaced
        cases replacementEq : verifyReplacement? last <;>
          simp [replacementEq, List.append_assoc] at replaced ⊢
        all_goals exact replaced
  | @ifThen body bodyBalanced bodyIH =>
      change EvalResources
        (compileVerify (([.op .OP_IF] ++ body) ++ [.op .OP_ENDIF]))
        stack altStack flags ctx out outAlt resources
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifThen body bodyBalanced bodyIH =>
      change EvalResources
        (compileVerify (([.op .OP_NOTIF] ++ body) ++ [.op .OP_ENDIF]))
        stack altStack flags ctx out outAlt resources
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change EvalResources
        (compileVerify
          (([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
            [.op .OP_ENDIF]))
        stack altStack flags ctx out outAlt resources
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change EvalResources
        (compileVerify
          (([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
            [.op .OP_ENDIF]))
        stack altStack flags ctx out outAlt resources
      rw [compileVerify_append_singleton]
      simpa [verifyReplacement?, List.append_assoc] using run

end LeanMiniscript.Miniscript
