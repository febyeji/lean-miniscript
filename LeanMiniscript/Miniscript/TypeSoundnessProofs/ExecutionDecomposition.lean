import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type soundness: successful execution decomposition

Splitting successful executions at balanced prefixes and inverting the
`IF`/`NOTIF` branch shapes emitted by the compiler.

Some helper lemmas here were `private` in the former single-file
`TypeSoundnessProofs` module. They are visible only so that sibling
submodules can use them; treat them as internal proof helpers, not stable API.
-/

/-! ## Successful execution decomposition -/

/-- A successful execution across a balanced prefix decomposes at the exact
    prefix boundary. Balanced control flow ensures that a conditional opened
    in the prefix cannot consume delimiters from the suffix. -/
theorem Eval.splitBalancedAppend_success
    {prefixScript suffix : Script}
    {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow prefixScript)
    (run : Eval (prefixScript ++ suffix) stack altStack flags ctx
      (.success out outAlt)) :
    ∃ middle middleAlt,
      Eval prefixScript stack altStack flags ctx (.success middle middleAlt) ∧
      Eval suffix middle middleAlt flags ctx (.success out outAlt) := by
  induction balanced generalizing suffix stack altStack out outAlt with
  | nil =>
      exact ⟨stack, altStack, Eval.done, by simpa using run⟩
  | append leftBalanced rightBalanced leftIH rightIH =>
      rw [List.append_assoc] at run
      obtain ⟨leftOut, leftAlt, leftRun, tailRun⟩ := leftIH run
      obtain ⟨middle, middleAlt, rightRun, suffixRun⟩ := rightIH tailRun
      exact ⟨middle, middleAlt, Eval.append leftRun rightRun, suffixRun⟩
  | atom nonConditional =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run <;>
        simp_all [NonConditional] <;>
        try grind [Eval, Opcode.isUpgradeableNop]
      case within =>
        rename_i upperBytes lowerBytes valueBytes upper lower value rest decoded tail
        cases resultEq
        refine ⟨boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest, altStack,
          Eval.within upperBytes lowerBytes valueBytes upper lower value rest altStack
            [] flags ctx _ decoded (.empty _ _ _ _), ?_⟩
        simpa using tail
  | @ifThen body bodyBalanced bodyIH =>
      generalize resultEq : ExecResult.success out outAlt = result at run
      cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
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
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            refine ⟨rest, altStack, ?_, selected⟩
            apply Eval.if_execute (frame := { branches := [body], after := [] })
            · simpa using splitConditional_balanced_ifThen bodyBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using
                (Eval.done (stack := rest) (altStack := altStack))
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, bodyRun, suffixRun⟩ := bodyIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.if_execute (frame := { branches := [body], after := [] })
            · simpa using splitConditional_balanced_ifThen bodyBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using bodyRun
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
      cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
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
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, bodyRun, suffixRun⟩ := bodyIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.notif_execute (frame := { branches := [body], after := [] })
            · simpa using splitConditional_balanced_ifThen bodyBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using bodyRun
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            refine ⟨rest, altStack, ?_, selected⟩
            apply Eval.notif_execute (frame := { branches := [body], after := [] })
            · simpa using splitConditional_balanced_ifThen bodyBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using
                (Eval.done (stack := rest) (altStack := altStack))
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
      cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
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
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, branchRun, suffixRun⟩ := elseIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.if_execute (frame :=
              { branches := [thenBranch, elseBranch], after := [] })
            · simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using branchRun
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, branchRun, suffixRun⟩ := thenIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.if_execute (frame :=
              { branches := [thenBranch, elseBranch], after := [] })
            · simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using branchRun
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
      cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
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
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, branchRun, suffixRun⟩ := thenIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.notif_execute (frame :=
              { branches := [thenBranch, elseBranch], after := [] })
            · simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using branchRun
          case true =>
            simp [ConditionalFrame.select, selectConditionalBranches,
              selectedBool] at selected
            obtain ⟨middle, middleAlt, branchRun, suffixRun⟩ := elseIH selected
            refine ⟨middle, middleAlt, ?_, suffixRun⟩
            apply Eval.notif_execute (frame :=
              { branches := [thenBranch, elseBranch], after := [] })
            · simpa using splitConditional_balanced_ifElse thenBalanced elseBalanced
                (suffix := [])
            · exact minimal
            · simpa [ConditionalFrame.select, selectConditionalBranches,
                selectedBool] using branchRun
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

/-- A successful closed IF with one balanced branch either skips the branch or
    executes that branch successfully. -/
theorem Eval.ifThen_success_cases
    {body : Script} {selector : StackElement} {rest altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval ([.op .OP_IF] ++ body ++ [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    (castToBool selector = false ∧ out = rest ∧ outAlt = altStack) ∨
      (castToBool selector = true ∧
        Eval body rest altStack flags ctx (.success out outAlt)) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case if_execute =>
      rename_i frame split minimal selected
      cases resultEq
      change splitConditional (body ++ [.op .OP_ENDIF]) = some frame at split
      rw [show splitConditional (body ++ [.op .OP_ENDIF]) =
        some { branches := [body], after := [] } by
          simpa using splitConditional_balanced_ifThen balanced
            (suffix := [])] at split
      cases split
      cases selectedBool : castToBool selector
      · left
        simp [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] at selected
        have equal := Eval.result_unique selected
          (Eval.done (stack := rest) (altStack := altStack))
        cases equal
        exact ⟨rfl, rfl, rfl⟩
      · right
        exact ⟨rfl, by
          simpa [ConditionalFrame.select, selectConditionalBranches,
            selectedBool] using selected⟩
  case if_unbalanced =>
      rename_i selectedResult split minimal selected
      change splitConditional (body ++ [.op .OP_ENDIF]) = none at split
      rw [show splitConditional (body ++ [.op .OP_ENDIF]) =
        some { branches := [body], after := [] } by
          simpa using splitConditional_balanced_ifThen balanced
            (suffix := [])] at split
      contradiction
  all_goals cases resultEq

/-- A successful closed NOTIF with one balanced branch either skips the branch
    or executes that branch successfully. -/
theorem Eval.notifThen_success_cases
    {body : Script} {selector : StackElement} {rest altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    (castToBool selector = true ∧ out = rest ∧ outAlt = altStack) ∨
      (castToBool selector = false ∧
        Eval body rest altStack flags ctx (.success out outAlt)) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case notif_execute =>
      rename_i frame split minimal selected
      cases resultEq
      change splitConditional (body ++ [.op .OP_ENDIF]) = some frame at split
      rw [show splitConditional (body ++ [.op .OP_ENDIF]) =
        some { branches := [body], after := [] } by
          simpa using splitConditional_balanced_ifThen balanced
            (suffix := [])] at split
      cases split
      cases selectedBool : castToBool selector
      · right
        exact ⟨rfl, by
          simpa [ConditionalFrame.select, selectConditionalBranches,
            selectedBool] using selected⟩
      · left
        simp [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] at selected
        have equal := Eval.result_unique selected
          (Eval.done (stack := rest) (altStack := altStack))
        cases equal
        exact ⟨rfl, rfl, rfl⟩
  case notif_unbalanced =>
      rename_i selectedResult split minimal selected
      change splitConditional (body ++ [.op .OP_ENDIF]) = none at split
      rw [show splitConditional (body ++ [.op .OP_ENDIF]) =
        some { branches := [body], after := [] } by
          simpa using splitConditional_balanced_ifThen balanced
            (suffix := [])] at split
      contradiction
  all_goals cases resultEq

/-- A successful closed IF/ELSE executes exactly one balanced branch. -/
theorem Eval.ifElse_success_cases
    {thenBranch elseBranch : Script} {selector : StackElement}
    {rest altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (thenBalanced : BalancedControlFlow thenBranch)
    (elseBalanced : BalancedControlFlow elseBranch)
    (run : Eval
      ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
        [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    Eval thenBranch rest altStack flags ctx (.success out outAlt) ∨
      Eval elseBranch rest altStack flags ctx (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case if_execute =>
      rename_i frame split minimal selected
      cases resultEq
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some frame at split
      rw [show splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some { branches := [thenBranch, elseBranch], after := [] } by
            simpa using splitConditional_balanced_ifElse thenBalanced
              elseBalanced (suffix := [])] at split
      cases split
      cases selectedBool : castToBool selector
      · right
        simpa [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] using selected
      · left
        simpa [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] using selected
  case if_unbalanced =>
      rename_i selectedResult split minimal selected
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          none at split
      rw [show splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some { branches := [thenBranch, elseBranch], after := [] } by
            simpa using splitConditional_balanced_ifElse thenBalanced
              elseBalanced (suffix := [])] at split
      contradiction
  all_goals cases resultEq

/-- A successful closed NOTIF/ELSE executes exactly one balanced branch. -/
theorem Eval.notifElse_success_cases
    {thenBranch elseBranch : Script} {selector : StackElement}
    {rest altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (thenBalanced : BalancedControlFlow thenBranch)
    (elseBalanced : BalancedControlFlow elseBranch)
    (run : Eval
      ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
        [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    Eval thenBranch rest altStack flags ctx (.success out outAlt) ∨
      Eval elseBranch rest altStack flags ctx (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case notif_execute =>
      rename_i frame split minimal selected
      cases resultEq
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some frame at split
      rw [show splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some { branches := [thenBranch, elseBranch], after := [] } by
            simpa using splitConditional_balanced_ifElse thenBalanced
              elseBalanced (suffix := [])] at split
      cases split
      cases selectedBool : castToBool selector
      · left
        simpa [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] using selected
      · right
        simpa [ConditionalFrame.select, selectConditionalBranches,
          selectedBool] using selected
  case notif_unbalanced =>
      rename_i selectedResult split minimal selected
      change splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          none at split
      rw [show splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++ [.op .OP_ENDIF]) =
          some { branches := [thenBranch, elseBranch], after := [] } by
            simpa using splitConditional_balanced_ifElse thenBalanced
              elseBalanced (suffix := [])] at split
      contradiction
  all_goals cases resultEq

end LeanMiniscript.Miniscript
