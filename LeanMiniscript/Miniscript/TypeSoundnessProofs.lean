import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type-soundness proof target

The semantic contract keeps arbitrary-input stack safety, generated-witness
correctness, and unconditional dissatisfaction availability as separate proof
obligations. This module is proof-only so the stable executable facade does not
import the recursive generated-contract development.
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
private theorem Eval.ifThen_success_cases
    {body : Script} {selector : StackElement} {rest altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval ([.op .OP_IF] ++ body ++ [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    (castToBool selector = false ∧ out = rest ∧ outAlt = altStack) ∨
      (castToBool selector = true ∧
        Eval body rest altStack flags ctx (.success out outAlt)) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
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
private theorem Eval.notifThen_success_cases
    {body : Script} {selector : StackElement} {rest altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow body)
    (run : Eval ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF])
      (selector :: rest) altStack flags ctx (.success out outAlt)) :
    (castToBool selector = true ∧ out = rest ∧ outAlt = altStack) ∨
      (castToBool selector = false ∧
        Eval body rest altStack flags ctx (.success out outAlt)) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
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
private theorem Eval.ifElse_success_cases
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
  cases run
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
private theorem Eval.notifElse_success_cases
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
  cases run
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

/-- The generated-witness part of type soundness. `GeneratedContract` gives
    B/V/K/W execution semantics, bounded witnesses, the exact `z`/`o` input
    counts, the satisfying-input `n` condition, and canonical `u` results. -/
def GeneratedTypeGuarantee (scriptCtx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop :=
  ∀ (env : SatEnv) (flags : ScriptFlags),
    ModeledContextVersion scriptCtx env.txCtx →
    ModeledContextFlags scriptCtx flags →
    env.Sound →
    env.EncodingSound flags →
    (satisfactionCandidates m env).SupportsGeneratedContract
      scriptCtx m ty flags env.txCtx

/-- Combined semantic proof target for a correctness type. -/
structure MiniTypeGuarantee (scriptCtx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop where
  base : BaseTypeGuarantee m ty.base
  generated : GeneratedTypeGuarantee scriptCtx m ty
  dissatisfiable : ty.mods.d = true → UnconditionalDissatisfaction m

/-- Generated-witness soundness for every valid core type. -/
def GeneratedTypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    GeneratedTypeGuarantee ctx m ty

/-- Every valid core fragment satisfies the generated-witness contract for its
    complete type. -/
theorem generatedTypeSoundnessCore : GeneratedTypeSoundnessCore := by
  intro ctx m ty valid env flags version modeled sound encodings
  exact supportsGeneratedContract_of_wellFormed_hasType version modeled sound
    encodings valid.hasType valid.wellFormed

/-- Surface generated-witness soundness is inherited through desugaring. -/
def GeneratedTypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    GeneratedTypeGuarantee ctx (desugar m) ty

/-- Desugaring transports the core generated-witness theorem without an
    additional surface proof. -/
theorem generatedTypeSoundnessSurface : GeneratedTypeSoundnessSurface := by
  intro ctx m ty valid
  exact generatedTypeSoundnessCore valid

/-! ## Unconditional dissatisfaction completeness -/

/-- Every candidate pair in a list carries a possible raw dissatisfaction. -/
def AllDissatisfactionCandidatesPossible : List CandidatePair → Prop
  | [] => True
  | pair :: pairs =>
      pair.dsat.Possible ∧ AllDissatisfactionCandidatesPossible pairs

namespace AllDissatisfactionCandidatesPossible

/-- Project raw dissatisfaction possibility for one member of the list. -/
theorem of_mem {pairs : List CandidatePair}
    (all : AllDissatisfactionCandidatesPossible pairs)
    {pair : CandidatePair} (member : pair ∈ pairs) : pair.dsat.Possible := by
  induction pairs with
  | nil => simp at member
  | cons head tail ih =>
      simp only [AllDissatisfactionCandidatesPossible] at all
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact all.1
      · exact ih all.2 member

end AllDissatisfactionCandidatesPossible

mutual

/-- A well-formed typed fragment whose type carries `d` has a possible raw
    dissatisfaction candidate in every material environment. -/
theorem dissatisfactionCandidatePossible_of_wellFormed_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx)
    (dissatisfiable : ty.mods.d = true) :
    ∀ env, (satisfactionCandidates fragment env).dsat.Possible := by
  cases typed with
  | zero =>
      intro env
      exact CandidateResult.Possible.usable [] false
  | one => simp at dissatisfiable
  | pk_k key =>
      intro env
      simpa [satisfactionCandidates, keyCandidates] using
        (CandidateResult.Possible.usable [falseElement] false)
  | pk_h key =>
      intro env
      simpa [satisfactionCandidates, keyCandidates] using
        (CandidateResult.Possible.usable [falseElement, key.bytes] false)
  | older n => simp at dissatisfiable
  | after n => simp at dissatisfiable
  | sha256 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.sha256 hash)] false .canonical)
  | hash256 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.hash256 hash)] false .canonical)
  | ripemd160 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.ripemd160 hash)] false .canonical)
  | hash160 hash =>
      intro env
      simpa [satisfactionCandidates, hashCandidates] using
        (CandidateResult.Possible.dontUse
          [env.nonPreimageFor (.hash160 hash)] false .canonical)
  | and_v => simp at dissatisfiable
  | @and_b first second firstMods secondMods firstTyped secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have childD : firstMods.d = true ∧ secondMods.d = true := by
        simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 childD.1 env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2.1 childD.2 env
      have canonical := firstPossible.combine secondPossible
      simpa [satisfactionCandidates] using canonical.selectLeft.selectLeft
  | @or_b first second firstMods secondMods firstTyped firstD secondTyped secondD =>
      simp only [CoreFragment.WellFormed] at wellFormed
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2 secondD env
      simpa [satisfactionCandidates] using firstPossible.combine secondPossible
  | or_c => simp at dissatisfiable
  | @or_d first second firstMods secondMods firstTyped firstD firstUnit secondTyped =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have secondD : secondMods.d = true := by simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have secondPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          secondTyped wellFormed.2 secondD env
      simpa [satisfactionCandidates] using firstPossible.combine secondPossible
  | @or_i first second firstType secondType firstTyped secondTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have childD : firstType.mods.d = true ∨ secondType.mods.d = true :=
        by simpa using dissatisfiable
      intro env
      rcases childD with firstD | secondD
      · have possible :=
          dissatisfactionCandidatePossible_of_wellFormed_hasType
            firstTyped wellFormed.1 firstD env
        simpa [satisfactionCandidates] using
          (possible.withSelector trueElement).selectLeft
      · have possible :=
          dissatisfactionCandidatePossible_of_wellFormed_hasType
            secondTyped wellFormed.2 secondD env
        simpa [satisfactionCandidates] using
          (possible.withSelector falseElement).selectRight
  | @andor first second third firstMods secondType thirdType firstTyped firstD
      firstUnit secondTyped thirdTyped branch baseEq =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have thirdD : thirdType.mods.d = true := by simpa using dissatisfiable
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped wellFormed.1 firstD env
      have thirdPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          thirdTyped wellFormed.2.2.1 thirdD env
      have canonical := firstPossible.combine thirdPossible
      simpa [satisfactionCandidates] using canonical.selectLeft
  | @c_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | v_wrap => simp at dissatisfiable
  | @a_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @s_wrap child mods childTyped oneArg =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @d_wrap child mods childTyped zeroArg =>
      intro env
      simpa [satisfactionCandidates] using
        (CandidateResult.Possible.usable [falseElement] false)
  | @j_wrap child mods childTyped nonzero =>
      intro env
      have canonical := CandidateResult.Possible.usable [falseElement] false
      simpa [satisfactionCandidates] using canonical.selectLeft
  | @n_wrap child mods childTyped =>
      have childD : mods.d = true := by simpa using dissatisfiable
      intro env
      simpa [satisfactionCandidates] using
        (dissatisfactionCandidatePossible_of_wellFormed_hasType
          childTyped wellFormed childD env)
  | @thresh threshold first rest firstMods restTypes firstTyped firstD firstUnit
      restTyped restShape positive atMost =>
      have childrenWellFormed := wellFormed.2.1
      simp only [CoreFragment.allWellFormed] at childrenWellFormed
      have safe : ArithmeticScriptNatSafe threshold :=
        ArithmeticScriptNatSafe.of_lt (by
          simpa [MAX_BIP_ARITHMETIC_VALUE, MAX_BIP_LOCK_VALUE,
            maxArithmeticScriptNatExclusive] using
            wellFormed.2.2.2)
      intro env
      have firstPossible :=
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          firstTyped childrenWellFormed.1 firstD env
      have restPossible :=
        dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
          restTyped childrenWellFormed.2 restShape env
      have valid : candidateThresholdValid threshold (first :: rest).length :=
        ⟨by omega, atMost, safe⟩
      rw [satisfactionCandidates_thresh_valid threshold (first :: rest) env valid]
      apply CandidatePair.thresholdDissatisfaction_possible_of_children
      intro pair member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact firstPossible
      · apply AllDissatisfactionCandidatesPossible.of_mem
        · simpa [satisfactionCandidatesList_eq_map] using restPossible
        · exact member
  | multi threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
        simpa [validLegacyMultiKeyCount, maxPubKeysPerMultiSig] using
          wellFormed.2.2.1
      have guard : ¬ (threshold = 0 ∨ keys.length < threshold ∨
          maxPubKeysPerMultiSig < keys.length) := by
        simp only [not_or]
        exact ⟨by omega, by omega, Nat.not_lt_of_ge keyBound⟩
      intro env
      simpa [satisfactionCandidates, legacyMultiCandidates, guard] using
        (CandidateResult.Possible.usable
          (List.replicate (threshold + 1) falseElement) false)
  | multi_a threshold keys positive atMost =>
      simp only [CoreFragment.WellFormed] at wellFormed
      have keyBound : keys.length ≤ MAX_PUBKEYS_PER_MULTI_A :=
        wellFormed.2.2.1
      have safe : ArithmeticScriptNatSafe threshold :=
        ArithmeticScriptNatSafe.of_lt (by
          change threshold < 2147483648
          have : threshold ≤ 999 := by
            simpa [MAX_PUBKEYS_PER_MULTI_A] using Nat.le_trans atMost keyBound
          omega)
      have valid : candidateThresholdValid threshold keys.length :=
        ⟨by omega, atMost, safe⟩
      intro env
      simpa [satisfactionCandidates, multiACandidates, valid] using
        (CandidateResult.Possible.usable
          (List.replicate keys.length falseElement) false)

/-- Pointwise list counterpart used by threshold completeness. -/
theorem dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
    {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType}
    (typed : HasTypeList scriptCtx fragments types)
    (wellFormed : CoreFragment.allWellFormed scriptCtx fragments)
    (restTypes : thresholdRestTypes types) :
    ∀ env, AllDissatisfactionCandidatesPossible
      (satisfactionCandidatesList fragments env) := by
  cases typed with
  | nil =>
      intro env
      trivial
  | @cons fragment ty fragments types headTyped tailTyped =>
      simp only [CoreFragment.allWellFormed] at wellFormed
      simp only [thresholdRestTypes] at restTypes
      intro env
      exact ⟨
        dissatisfactionCandidatePossible_of_wellFormed_hasType
          headTyped wellFormed.1 restTypes.2.1 env,
        dissatisfactionCandidatesListPossible_of_allWellFormed_hasTypeList
          tailTyped wellFormed.2 restTypes.2.2.2 env⟩

end

/-- Every valid `d`-typed fragment has an unconditional raw dissatisfaction,
    including canonical candidates marked `DONTUSE`. -/
theorem unconditionalDissatisfaction_of_wellFormed_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx)
    (dissatisfiable : ty.mods.d = true) :
    UnconditionalDissatisfaction fragment := by
  intro env
  exact (dissatisfactionCandidatePossible_of_wellFormed_hasType
    typed wellFormed dissatisfiable env).witness

/-! ## Arbitrary-input base-type soundness -/

/-- Successful execution of a threshold tail consumes an arbitrary prefix
    below its incoming accumulator, leaves one accumulator, and restores the
    alternate stack. -/
def ThresholdTailBaseGuarantee (fragments : List CoreFragment) : Prop :=
  ∀ (accumulator : StackElement) (stack altStack : Stack)
      (flags : ScriptFlags) (ctx : TxContext) (outcome : ExecResult),
    Eval (compileThreshTail fragments) (accumulator :: stack) altStack
      flags ctx outcome →
    match outcome with
    | .success finalStack finalAltStack =>
        finalAltStack = altStack ∧
          ∃ args rest result,
            stack = args ++ rest ∧ finalStack = result :: rest
    | .failure _ => True

/-- Argument-frame lengths carried internally by the correctness modifiers.
    B and V fragments consume their argument frame. K fragments leave the
    following signature slot for a later `c:` wrapper, so their `z`/`o`
    guarantees both correspond to an empty consumed prefix. W fragments use a
    separately protected element and expose no direct `z`/`o` rule. -/
def ArgumentFrameMatches (base : BaseType) (mods : CorrectnessModifiers)
    (args : Stack) : Prop :=
  match base with
  | .B | .V =>
      (mods.z = true → args.length = 0) ∧
      (mods.o = true → args.length = 1)
  | .K =>
      (mods.z = true → args.length = 0) ∧
      (mods.o = true → args.length = 0)
  | .W => True

/-- Base stack effects strengthened with the argument-frame length information
    needed when a parent constructor consumes a child's `z` or `o` modifier. -/
inductive RefinedBaseStackEffect : MiniType → Stack → Stack → Prop where
  | b (mods : CorrectnessModifiers) (args rest : Stack)
      (result : StackElement) (frameMatches : ArgumentFrameMatches .B mods args) :
      RefinedBaseStackEffect ⟨.B, mods⟩ (args ++ rest) (result :: rest)
  | v (mods : CorrectnessModifiers) (args rest : Stack)
      (frameMatches : ArgumentFrameMatches .V mods args) :
      RefinedBaseStackEffect ⟨.V, mods⟩ (args ++ rest) rest
  | k (mods : CorrectnessModifiers) (args rest : Stack)
      (key : StackElement) (frameMatches : ArgumentFrameMatches .K mods args) :
      RefinedBaseStackEffect ⟨.K, mods⟩ (args ++ rest) (key :: rest)
  | w (mods : CorrectnessModifiers) (args rest : Stack)
      (saved result : StackElement) (order : BaseWOutputOrder)
      (frameMatches : ArgumentFrameMatches .W mods args) :
      RefinedBaseStackEffect ⟨.W, mods⟩ (saved :: args ++ rest)
        (order.outputs saved result ++ rest)

namespace RefinedBaseStackEffect

/-- Invert a refined B effect without dependent-index elimination at a
    concrete input stack. -/
theorem b_inv {mods : CorrectnessModifiers} {input output : Stack}
    (effect : RefinedBaseStackEffect ⟨.B, mods⟩ input output) :
    ∃ args rest result,
      input = args ++ rest ∧ output = result :: rest ∧
        ArgumentFrameMatches .B mods args := by
  cases effect with
  | b mods args rest result frameMatches =>
      exact ⟨args, rest, result, rfl, rfl, frameMatches⟩

/-- Invert a refined K effect. -/
theorem k_inv {mods : CorrectnessModifiers} {input output : Stack}
    (effect : RefinedBaseStackEffect ⟨.K, mods⟩ input output) :
    ∃ args rest key,
      input = args ++ rest ∧ output = key :: rest ∧
        ArgumentFrameMatches .K mods args := by
  cases effect with
  | k mods args rest key frameMatches =>
      exact ⟨args, rest, key, rfl, rfl, frameMatches⟩

/-- Invert a refined V effect. -/
theorem v_inv {mods : CorrectnessModifiers} {input output : Stack}
    (effect : RefinedBaseStackEffect ⟨.V, mods⟩ input output) :
    ∃ args, input = args ++ output ∧
      ArgumentFrameMatches .V mods args := by
  cases effect with
  | v mods args rest frameMatches =>
      exact ⟨args, rfl, frameMatches⟩

/-- Invert a refined W effect. -/
theorem w_inv {mods : CorrectnessModifiers} {input output : Stack}
    (effect : RefinedBaseStackEffect ⟨.W, mods⟩ input output) :
    ∃ args rest saved result, ∃ order : BaseWOutputOrder,
      input = saved :: args ++ rest ∧
        output = order.outputs saved result ++ rest := by
  cases effect with
  | w mods args rest saved result order frameMatches =>
      exact ⟨args, rest, saved, result, order, rfl, rfl⟩

/-- Forget correctness-modifier frame lengths. -/
theorem toBase {ty : MiniType} {input output : Stack}
    (effect : RefinedBaseStackEffect ty input output) :
    BaseStackEffect ty.base input output := by
  cases effect with
  | b mods args rest result frameMatches => exact .b args rest result
  | v mods args rest frameMatches => exact .v args output
  | k mods args rest key frameMatches => exact .k args rest key
  | w mods args rest saved result order frameMatches =>
      exact .w args rest saved result order

end RefinedBaseStackEffect

/-- Strengthened arbitrary-input guarantee used by the structural induction. -/
def RefinedBaseTypeGuarantee (fragment : CoreFragment) (ty : MiniType) : Prop :=
  ∀ (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
      (outcome : ExecResult),
    Eval (compile fragment) stack altStack flags ctx outcome →
    match outcome with
    | .success finalStack finalAltStack =>
        finalAltStack = altStack ∧
          RefinedBaseStackEffect ty stack finalStack
    | .failure _ => True

/-- A well-typed K fragment never has the zero-argument modifier. Its eventual
    CHECKSIG wrapper always needs a signature slot. -/
private theorem HasType.k_not_z
    {scriptCtx : ScriptContext} {fragment : CoreFragment}
    {ty : MiniType} (typed : HasType scriptCtx fragment ty)
    (baseEq : ty.base = .K) : ty.mods.z = false := by
  induction sizeEq : sizeOf fragment using Nat.strongRecOn
      generalizing fragment ty with
  | ind size ih =>
      cases typed <;> simp_all [branchBase]
      case and_v X Y firstMods secondType firstTyped secondTyped =>
        intro _
        apply ih (sizeOf Y)
        · omega
        · assumption
        · assumption
        · rfl
      case andor X Y Z firstMods secondType thirdType firstTyped firstD
          firstUnit secondTyped thirdTyped sameBase =>
        intro _ _
        apply ih (sizeOf Z)
        · omega
        · assumption
        · assumption
        · rfl

/-- W-producing typing rules deliberately clear both argument-count
    modifiers. -/
private theorem HasType.w_no_zo
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty) (baseEq : ty.base = .W) :
    ty.mods.z = false ∧ ty.mods.o = false := by
  cases typed <;> simp_all [branchBase]

/-- Any nonempty threshold tail starts with a W fragment, so both aggregate
    argument-count modifiers are false. -/
private theorem thresholdRestModifiers_noCount
    {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType}
    (typed : HasTypeList scriptCtx fragments types)
    (restTypes : thresholdRestTypes types)
    (nonempty : fragments ≠ []) :
    CorrectnessModifiers.allZ (MiniType.modifiers types) = false ∧
      CorrectnessModifiers.oneOWithRestZ (MiniType.modifiers types) = false := by
  cases typed with
  | nil => contradiction
  | @cons fragment ty fragments types headTyped tailTyped =>
      simp only [thresholdRestTypes] at restTypes
      have noCount : ty.mods.z = false ∧ ty.mods.o = false :=
        HasType.w_no_zo headTyped restTypes.1
      simp [MiniType.modifiers, CorrectnessModifiers.allZ,
        CorrectnessModifiers.oneOWithRestZ, noCount.1, noCount.2]

/-- Threshold-tail compilation is balanced. -/
private theorem compileThreshTail_balancedControlFlow
    (fragments : List CoreFragment) :
    BalancedControlFlow (compileThreshTail fragments) := by
  exact (compileThreshTailWithKeyHash_conforms modelKeyHash fragments).balancedControlFlow

/-- Sequentially consumed argument frames satisfy the modifier formula used by
    `and_v`. -/
private theorem ArgumentFrameMatches.afterV
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {firstArgs secondArgs : Stack}
    (first : ArgumentFrameMatches .V firstMods firstArgs)
    (second : ArgumentFrameMatches base secondMods secondArgs)
    (branch : branchBase base)
    (kNotZ : base = .K → secondMods.z = false) :
    ArgumentFrameMatches base {
      z := firstMods.z && secondMods.z
      o := (firstMods.z && secondMods.o) ||
        (firstMods.o && secondMods.z)
      n := firstMods.n || (firstMods.z && secondMods.n)
      d := false
      u := secondMods.u
    } (firstArgs ++ secondArgs) := by
  cases base with
  | B =>
      simp only [ArgumentFrameMatches] at first second ⊢
      constructor
      · intro zero
        simp only [Bool.and_eq_true] at zero
        simp [List.length_append, first.1 zero.1, second.1 zero.2]
      · intro one
        simp only [Bool.or_eq_true, Bool.and_eq_true] at one
        rcases one with one | one
        · simp [List.length_append, first.1 one.1, second.2 one.2]
        · simp [List.length_append, first.2 one.1, second.1 one.2]
  | V =>
      simp only [ArgumentFrameMatches] at first second ⊢
      constructor
      · intro zero
        simp only [Bool.and_eq_true] at zero
        simp [List.length_append, first.1 zero.1, second.1 zero.2]
      · intro one
        simp only [Bool.or_eq_true, Bool.and_eq_true] at one
        rcases one with one | one
        · simp [List.length_append, first.1 one.1, second.2 one.2]
        · simp [List.length_append, first.2 one.1, second.1 one.2]
  | K =>
      simp only [ArgumentFrameMatches] at first second ⊢
      have secondNotZ := kNotZ rfl
      constructor
      · intro zero
        simp only [Bool.and_eq_true] at zero
        simp_all
      · intro one
        simp only [Bool.or_eq_true, Bool.and_eq_true] at one
        rcases one with one | one
        · simp [List.length_append, first.1 one.1, second.2 one.2]
        · simp_all
  | W => simp [branchBase] at branch

/-- Refined V-prefix composition for every branch-capable base type. -/
private theorem RefinedBaseStackEffect.afterV
    {base : BaseType} {firstMods secondMods : CorrectnessModifiers}
    {input middle output : Stack}
    (first : RefinedBaseStackEffect ⟨.V, firstMods⟩ input middle)
    (second : RefinedBaseStackEffect ⟨base, secondMods⟩ middle output)
    (branch : branchBase base)
    (kNotZ : base = .K → secondMods.z = false) :
    RefinedBaseStackEffect ⟨base, {
      z := firstMods.z && secondMods.z
      o := (firstMods.z && secondMods.o) ||
        (firstMods.o && secondMods.z)
      n := firstMods.n || (firstMods.z && secondMods.n)
      d := false
      u := secondMods.u
    }⟩ input output := by
  cases first with
  | v _ firstArgs shared firstMatches =>
      cases second with
      | b _ secondArgs rest result secondMatches =>
          simpa [List.append_assoc] using
            RefinedBaseStackEffect.b _ (firstArgs ++ secondArgs) rest result
              (ArgumentFrameMatches.afterV firstMatches secondMatches branch
                kNotZ)
      | v _ secondArgs rest secondMatches =>
          simpa [List.append_assoc] using
            RefinedBaseStackEffect.v _ (firstArgs ++ secondArgs) output
              (ArgumentFrameMatches.afterV firstMatches secondMatches branch
                kNotZ)
      | k _ secondArgs rest key secondMatches =>
          simpa [List.append_assoc] using
            RefinedBaseStackEffect.k _ (firstArgs ++ secondArgs) rest key
              (ArgumentFrameMatches.afterV firstMatches secondMatches branch
                kNotZ)
      | w _ args rest saved result order secondMatches =>
          simp [branchBase] at branch

/-- A consumed conditional selector extends the argument frame of a selected
    branch. -/
private theorem ArgumentFrameMatches.withSelector
    {base : BaseType} {mods : CorrectnessModifiers} {args : Stack}
    {selector : StackElement} {parentMods : CorrectnessModifiers}
    (frameMatches : ArgumentFrameMatches base mods args)
    (branch : branchBase base)
    (parentNotZ : parentMods.z = false)
    (selectedZ : parentMods.o = true → mods.z = true)
    (kNoO : base = .K → parentMods.o = false) :
    ArgumentFrameMatches base parentMods (selector :: args) := by
  cases base with
  | B =>
      simp only [ArgumentFrameMatches] at frameMatches ⊢
      constructor
      · simp [parentNotZ]
      · intro one
        have argsEmpty := frameMatches.1 (selectedZ one)
        simp [argsEmpty]
  | V =>
      simp only [ArgumentFrameMatches] at frameMatches ⊢
      constructor
      · simp [parentNotZ]
      · intro one
        have argsEmpty := frameMatches.1 (selectedZ one)
        simp [argsEmpty]
  | K =>
      simp only [ArgumentFrameMatches] at frameMatches ⊢
      have parentNotO := kNoO rfl
      simp [parentNotZ, parentNotO]
  | W => simp [branchBase] at branch

/-- Lift a selected branch effect across its consumed selector. -/
private theorem RefinedBaseStackEffect.withSelector
    {base : BaseType} {mods : CorrectnessModifiers} {input output : Stack}
    {selector : StackElement} {parentMods : CorrectnessModifiers}
    (effect : RefinedBaseStackEffect ⟨base, mods⟩ input output)
    (branch : branchBase base)
    (parentNotZ : parentMods.z = false)
    (selectedZ : parentMods.o = true → mods.z = true)
    (kNoO : base = .K → parentMods.o = false) :
    RefinedBaseStackEffect ⟨base, parentMods⟩
      (selector :: input) output := by
  cases effect with
  | b _ args rest result frameMatches =>
      simpa using RefinedBaseStackEffect.b _ (selector :: args) rest result
        (ArgumentFrameMatches.withSelector frameMatches branch parentNotZ selectedZ
          kNoO)
  | v _ args rest frameMatches =>
      simpa using RefinedBaseStackEffect.v _ (selector :: args) output
        (ArgumentFrameMatches.withSelector frameMatches branch parentNotZ selectedZ
          kNoO)
  | k _ args rest key frameMatches =>
      simpa using RefinedBaseStackEffect.k _ (selector :: args) rest key
        (ArgumentFrameMatches.withSelector frameMatches branch parentNotZ selectedZ
          kNoO)
  | w _ args rest saved result order frameMatches =>
      simp [branchBase] at branch

/-- Compose a B-produced conditional selector with the selected branch's
    argument frame. -/
private theorem ArgumentFrameMatches.afterProducedSelector
    {base : BaseType} {firstMods selectedMods parentMods : CorrectnessModifiers}
    {firstArgs selectedArgs : Stack}
    (first : ArgumentFrameMatches .B firstMods firstArgs)
    (selected : ArgumentFrameMatches base selectedMods selectedArgs)
    (branch : branchBase base)
    (parentZ : parentMods.z = true →
      firstMods.z = true ∧ selectedMods.z = true)
    (parentO : parentMods.o = true →
      (firstMods.z = true ∧ selectedMods.o = true) ∨
        (firstMods.o = true ∧ selectedMods.z = true))
    (kNotZ : base = .K → selectedMods.z = false) :
    ArgumentFrameMatches base parentMods (firstArgs ++ selectedArgs) := by
  cases base with
  | B =>
      simp only [ArgumentFrameMatches] at first selected ⊢
      constructor
      · intro zero
        have parts := parentZ zero
        simp [List.length_append, first.1 parts.1, selected.1 parts.2]
      · intro one
        rcases parentO one with parts | parts
        · simp [List.length_append, first.1 parts.1, selected.2 parts.2]
        · simp [List.length_append, first.2 parts.1, selected.1 parts.2]
  | V =>
      simp only [ArgumentFrameMatches] at first selected ⊢
      constructor
      · intro zero
        have parts := parentZ zero
        simp [List.length_append, first.1 parts.1, selected.1 parts.2]
      · intro one
        rcases parentO one with parts | parts
        · simp [List.length_append, first.1 parts.1, selected.2 parts.2]
        · simp [List.length_append, first.2 parts.1, selected.1 parts.2]
  | K =>
      simp only [ArgumentFrameMatches] at first selected ⊢
      have selectedNotZ := kNotZ rfl
      constructor
      · intro zero
        have parts := parentZ zero
        simp_all
      · intro one
        rcases parentO one with parts | parts
        · simp [List.length_append, first.1 parts.1, selected.2 parts.2]
        · simp_all
  | W => simp [branchBase] at branch

/-- Prepend an already-consumed argument prefix to a branch effect. -/
private theorem RefinedBaseStackEffect.prependArguments
    {base : BaseType} {selectedMods parentMods : CorrectnessModifiers}
    {leadingArgs input output : Stack}
    (effect : RefinedBaseStackEffect ⟨base, selectedMods⟩ input output)
    (branch : branchBase base)
    (combine : ∀ {args}, ArgumentFrameMatches base selectedMods args →
      ArgumentFrameMatches base parentMods (leadingArgs ++ args)) :
    RefinedBaseStackEffect ⟨base, parentMods⟩ (leadingArgs ++ input) output := by
  cases effect with
  | b _ args rest result frameMatches =>
      simpa [List.append_assoc] using
        RefinedBaseStackEffect.b _ (leadingArgs ++ args) rest result
          (combine frameMatches)
  | v _ args rest frameMatches =>
      simpa [List.append_assoc] using
        RefinedBaseStackEffect.v _ (leadingArgs ++ args) output
          (combine frameMatches)
  | k _ args rest key frameMatches =>
      simpa [List.append_assoc] using
        RefinedBaseStackEffect.k _ (leadingArgs ++ args) rest key
          (combine frameMatches)
  | w _ args rest saved result order frameMatches =>
      simp [branchBase] at branch

/-- A successful standalone CHECKSIG consumes its key/signature pair, leaves
    one boolean result, and preserves the alternate stack. -/
private theorem Eval.checkSigSingle_success_shape
    {key signature : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIG] (key :: signature :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key with
  | error error =>
      have failed : Eval [.op .OP_CHECKSIG] (key :: signature :: rest)
          altStack flags ctx (.failure error) :=
        Eval.checksig_encoding_failure key signature rest [] altStack flags ctx
          error checked
      have equal := Eval.result_unique run failed
      contradiction
  | ok valid =>
      cases valid with
      | false =>
          have canonical : Eval [.op .OP_CHECKSIG]
              (key :: signature :: rest) altStack flags ctx
              (.success (falseElement :: rest) altStack) :=
            Eval.checksigFalse checked Eval.done
          have equal := Eval.result_unique run canonical
          cases equal
          exact ⟨rfl, ⟨falseElement, rfl⟩⟩
      | true =>
          have canonical : Eval [.op .OP_CHECKSIG]
              (key :: signature :: rest) altStack flags ctx
              (.success (trueElement :: rest) altStack) :=
            Eval.checksigTrue checked Eval.done
          have equal := Eval.result_unique run canonical
          cases equal
          exact ⟨rfl, ⟨trueElement, rfl⟩⟩

/-- A successful standalone 0NOTEQUAL leaves one normalized boolean and
    preserves the alternate stack. -/
private theorem Eval.zeroNotEqualSingle_success_shape
    {operand : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_0NOTEQUAL] (operand :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes with
  | error error =>
      have failed : Eval [.op .OP_0NOTEQUAL] (operand :: rest) altStack
          flags ctx (.failure error) :=
        Eval.unary_scriptnum_failure operand rest [] altStack flags ctx error
          decoded
      have equal := Eval.result_unique run failed
      contradiction
  | ok value =>
      have canonical : Eval [.op .OP_0NOTEQUAL] (operand :: rest) altStack
          flags ctx (.success (boolToElement (value != 0) :: rest) altStack) :=
        Eval.zeroNotEqual operand value rest altStack [] flags ctx _ decoded
          Eval.done
      have equal := Eval.result_unique run canonical
      cases equal
      exact ⟨rfl, ⟨boolToElement (value != 0), rfl⟩⟩

/-- Successful standalone VERIFY consumes its true operand and preserves the
    alternate stack. -/
private theorem Eval.verifySingle_success_shape
    {operand : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_VERIFY] (operand :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalStack = rest ∧ finalAlt = altStack := by
  cases truth : castToBool operand with
  | false =>
      have failed : Eval [.op .OP_VERIFY] (operand :: rest) altStack flags ctx
          (.failure .verify) := Eval.verifyFalse truth
      have equal := Eval.result_unique run failed
      contradiction
  | true =>
      have canonical : Eval [.op .OP_VERIFY] (operand :: rest) altStack
          flags ctx (.success rest altStack) := Eval.verifyTrue truth Eval.done
      have equal := Eval.result_unique run canonical
      cases equal
      exact ⟨rfl, rfl⟩

/-- Successful standalone BOOLAND execution leaves one boolean and preserves
    the alternate stack. -/
private theorem Eval.boolAndSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLAND] (first :: second :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      have failed : Eval [.op .OP_BOOLAND] (first :: second :: rest)
          altStack flags ctx (.failure error) :=
        Eval.binaryScriptNumFailure (opcode := .OP_BOOLAND) rfl decoded
      have equal := Eval.result_unique run failed
      contradiction
  | ok values =>
      obtain ⟨firstValue, secondValue⟩ := values
      have canonical : Eval [.op .OP_BOOLAND] (first :: second :: rest)
          altStack flags ctx
          (.success
            (boolToElement
              ((firstValue != 0) && (secondValue != 0)) :: rest)
            altStack) :=
        Eval.booland first second firstValue secondValue rest [] altStack flags
          ctx _ decoded Eval.done
      have equal := Eval.result_unique run canonical
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩

/-- Successful standalone BOOLOR execution leaves one boolean and preserves
    the alternate stack. -/
private theorem Eval.boolOrSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_BOOLOR] (first :: second :: rest) altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      have failed : Eval [.op .OP_BOOLOR] (first :: second :: rest)
          altStack flags ctx (.failure error) :=
        Eval.binaryScriptNumFailure (opcode := .OP_BOOLOR) rfl decoded
      have equal := Eval.result_unique run failed
      contradiction
  | ok values =>
      obtain ⟨firstValue, secondValue⟩ := values
      have canonical : Eval [.op .OP_BOOLOR] (first :: second :: rest)
          altStack flags ctx
          (.success
            (boolToElement
              ((firstValue != 0) || (secondValue != 0)) :: rest)
            altStack) :=
        Eval.boolor first second firstValue secondValue rest [] altStack flags
          ctx _ decoded Eval.done
      have equal := Eval.result_unique run canonical
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩

/-- Successful standalone ADD execution leaves one accumulator and preserves
    the alternate stack. -/
private theorem Eval.addSingle_success_shape
    {first second : StackElement} {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_ADD] (first :: second :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  cases decoded : decodeBinaryScriptNums flags first second with
  | error error =>
      have failed : Eval [.op .OP_ADD] (first :: second :: rest)
          altStack flags ctx (.failure error) :=
        Eval.binaryScriptNumFailure (opcode := .OP_ADD) rfl decoded
      have equal := Eval.result_unique run failed
      contradiction
  | ok values =>
      obtain ⟨firstValue, secondValue⟩ := values
      have canonical : Eval [.op .OP_ADD] (first :: second :: rest)
          altStack flags ctx
          (.success (scriptNum (firstValue + secondValue) :: rest) altStack) :=
        Eval.add first second firstValue secondValue rest [] altStack flags ctx
          _ decoded Eval.done
      have equal := Eval.result_unique run canonical
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩

/-- Pushing a threshold and comparing it with an accumulator leaves one
    boolean result. -/
private theorem Eval.pushNumEqual_success_shape
    {threshold : Nat} {accumulator : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum threshold, .op .OP_EQUAL]
      (accumulator :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  by_cases equal : scriptNum threshold = accumulator
  · have canonical : Eval [.pushNum threshold, .op .OP_EQUAL]
        (accumulator :: rest) altStack flags ctx
        (.success (trueElement :: rest) altStack) := by
      apply Eval.pushNum
      exact Eval.equal_true _ _ _ [] _ _ _ _ equal Eval.done
    have resultEq := Eval.result_unique run canonical
    cases resultEq
    exact ⟨rfl, ⟨trueElement, rfl⟩⟩
  · have canonical : Eval [.pushNum threshold, .op .OP_EQUAL]
        (accumulator :: rest) altStack flags ctx
        (.success (falseElement :: rest) altStack) := by
      apply Eval.pushNum
      exact Eval.equal_false _ _ _ [] _ _ _ _ equal Eval.done
    have resultEq := Eval.result_unique run canonical
    cases resultEq
    exact ⟨rfl, ⟨falseElement, rfl⟩⟩

/-- Successful standalone CHECKSIGADD leaves one updated accumulator. -/
private theorem Eval.checkSigAddSingle_success_shape
    {pubkey count signature : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIGADD]
      (pubkey :: count :: signature :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  generalize resultEq : ExecResult.success finalStack finalAlt = result at run
  cases run
  case checksigadd_success =>
      rename_i countValue decoded checked next
      cases resultEq
      have equal := Eval.result_unique next
        (Eval.done (stack := scriptNum (countValue + 1) :: rest)
          (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩
  case checksigadd_failure =>
      rename_i countValue decoded checked next
      cases resultEq
      have equal := Eval.result_unique next
        (Eval.done (stack := scriptNum countValue :: rest)
          (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩
  all_goals cases resultEq

/-- Pushing a threshold and applying NUMEQUAL leaves one boolean result. -/
private theorem Eval.pushNumNumEqual_success_shape
    {threshold : Nat} {accumulator : StackElement}
    {rest altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum threshold, .op .OP_NUMEQUAL]
      (accumulator :: rest) altStack flags ctx
      (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ result, finalStack = result :: rest := by
  have pushed : Eval [.pushNum threshold] (accumulator :: rest) altStack
      flags ctx (.success (scriptNum threshold :: accumulator :: rest)
        altStack) := by
    apply Eval.pushNum
    exact Eval.done
  obtain ⟨middle, middleAlt, pushRun, compareRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) run
  have pushEq := Eval.result_unique pushRun pushed
  cases pushEq
  cases decoded : decodeBinaryScriptNums flags (scriptNum threshold)
      accumulator with
  | error error =>
      have failed : Eval [.op .OP_NUMEQUAL]
          (scriptNum threshold :: accumulator :: rest) altStack flags ctx
          (.failure error) :=
        Eval.binaryScriptNumFailure (opcode := .OP_NUMEQUAL) rfl decoded
      have equal := Eval.result_unique compareRun failed
      contradiction
  | ok values =>
      obtain ⟨thresholdValue, accumulatorValue⟩ := values
      have canonical : Eval [.op .OP_NUMEQUAL]
          (scriptNum threshold :: accumulator :: rest) altStack flags ctx
          (.success
            (boolToElement (thresholdValue == accumulatorValue) :: rest)
            altStack) :=
        Eval.numequal _ _ thresholdValue accumulatorValue rest [] altStack
          flags ctx _ decoded Eval.done
      have equal := Eval.result_unique compareRun canonical
      cases equal
      exact ⟨rfl, ⟨_, rfl⟩⟩

/-- Expand a successful EQUALVERIFY back into EQUAL followed by VERIFY. -/
private theorem Eval.unfuseEqualVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_EQUALVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_EQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case equalverify_success =>
      rename_i first second rest equal next
      cases resultEq
      exact Eval.equal_true first second rest [.op .OP_VERIFY] altStack flags ctx
        _ equal (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful CHECKSIGVERIFY back into CHECKSIG followed by VERIFY. -/
private theorem Eval.unfuseCheckSigVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKSIGVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_CHECKSIG, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case checksigverify_success =>
      rename_i pubkey signature rest checked next
      cases resultEq
      exact Eval.checksigTrue checked (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful CHECKMULTISIGVERIFY back into CHECKMULTISIG followed
    by VERIFY. -/
private theorem Eval.unfuseCheckMultiSigVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_CHECKMULTISIGVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_CHECKMULTISIG, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case checkmultisigverify_success =>
      rename_i operands dummy checked decoded next
      cases resultEq
      exact Eval.checkmultisig_success stack operands [.op .OP_VERIFY]
        altStack flags ctx _ decoded checked dummy (Eval.verifyTrue rfl next)
  all_goals cases resultEq

/-- Expand a successful NUMEQUALVERIFY back into NUMEQUAL followed by VERIFY. -/
private theorem Eval.unfuseNumEqualVerify_success
    {stack altStack out outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_NUMEQUALVERIFY] stack altStack flags ctx
      (.success out outAlt)) :
    Eval [.op .OP_NUMEQUAL, .op .OP_VERIFY] stack altStack flags ctx
      (.success out outAlt) := by
  generalize resultEq : ExecResult.success out outAlt = result at run
  cases run
  case numequalverify_success =>
      rename_i first second firstValue secondValue rest equal decoded next
      cases resultEq
      apply Eval.numequal first second firstValue secondValue rest
        [.op .OP_VERIFY] altStack flags ctx _ decoded
      have comparison : (firstValue == secondValue) = true := by
        simp [equal]
      rw [comparison]
      exact Eval.verifyTrue rfl next
  all_goals cases resultEq

/-- Successful optimized VERIFY compilation can be expanded to the original
    balanced script followed by an explicit VERIFY. -/
private theorem Eval.compileVerify_success_inverse
    {script : Script} {stack altStack out outAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (balanced : BalancedControlFlow script)
    (run : Eval (compileVerify script) stack altStack flags ctx
      (.success out outAlt)) :
    Eval (script ++ [.op .OP_VERIFY]) stack altStack flags ctx
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
            | exact Eval.unfuseEqualVerify_success run
            | exact Eval.unfuseCheckSigVerify_success run
            | exact Eval.unfuseCheckMultiSigVerify_success run
            | exact Eval.unfuseNumEqualVerify_success run
            | exact run
  | @append left right leftBalanced rightBalanced leftIH rightIH =>
      rcases List.eq_nil_or_concat right with rfl | ⟨initScript, last, rfl⟩
      · have expanded := leftIH (by simpa using run)
        simpa using expanded
      · simp only [List.concat_eq_append] at run rightBalanced rightIH ⊢
        have normalized : Eval
            (left ++ compileVerify (initScript ++ [last])) stack altStack
            flags ctx (.success out outAlt) := by
          rw [compileVerify_append_singleton]
          rw [← List.append_assoc] at run
          rw [compileVerify_append_singleton] at run
          cases replacementEq : verifyReplacement? last <;>
            simp [replacementEq, List.append_assoc] at run ⊢
          all_goals exact run
        obtain ⟨middle, middleAlt, leftRun, rightRun⟩ :=
          Eval.splitBalancedAppend_success leftBalanced normalized
        have expandedRight := rightIH rightRun
        simpa [List.append_assoc] using Eval.append leftRun expandedRight
  | @ifThen body bodyBalanced bodyIH =>
      change Eval
        ((([.op .OP_IF] ++ body) ++ [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifThen body bodyBalanced bodyIH =>
      change Eval
        ((([.op .OP_NOTIF] ++ body) ++ [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        ((([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
          [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      change Eval
        ((([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++ elseBranch) ++
          [.op .OP_ENDIF]) ++ [.op .OP_VERIFY])
        stack altStack flags ctx (.success out outAlt)
      rw [compileVerify_append_singleton] at run
      simpa [verifyReplacement?, List.append_assoc] using run

/-- CHECKSIGADD helper compilation contains no control-flow delimiters. -/
private theorem compileCheckSigAddTail_balancedControlFlow
    (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append
        (.append (.atom (by simp [NonConditional]))
          (.atom (by simp [NonConditional]))) ih

/-- Nonempty CHECKSIGADD compilation is balanced. -/
private theorem compileCheckSigAdd_balancedControlFlow
    (keys : List PubKey) :
    BalancedControlFlow (compileCheckSigAdd keys) := by
  cases keys with
  | nil => exact .atom (by simp [NonConditional])
  | cons key keys =>
      exact .append
        (.append (.atom (by simp [NonConditional]))
          (.atom (by simp [NonConditional])))
        (compileCheckSigAddTail_balancedControlFlow keys)

/-- A successful CHECKSIGADD tail consumes a prefix of signatures below its
    incoming accumulator and leaves one accumulator. -/
private theorem Eval.compileCheckSigAddTail_success_shape
    (keys : List PubKey) {accumulator : StackElement}
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compileCheckSigAddTail keys) (accumulator :: stack)
      altStack flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  induction keys generalizing accumulator stack altStack finalStack finalAlt with
  | nil =>
      have equal := Eval.result_unique run
        (Eval.done (stack := accumulator :: stack) (altStack := altStack))
      cases equal
      exact ⟨rfl, ⟨[], stack, accumulator, rfl, rfl⟩⟩
  | cons key keys ih =>
      have combined : Eval
          ([.pushData key] ++
            ([.op .OP_CHECKSIGADD] ++ compileCheckSigAddTail keys))
          (accumulator :: stack) altStack flags ctx
          (.success finalStack finalAlt) := by
        simpa [compileCheckSigAddTail, List.append_assoc] using run
      obtain ⟨afterPush, afterPushAlt, pushRun, tailRun⟩ :=
        Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) combined
      obtain ⟨afterCheck, afterCheckAlt, checkRun, restRun⟩ :=
        Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) tailRun
      have canonicalPush : Eval [.pushData key] (accumulator :: stack)
          altStack flags ctx
          (.success (key :: accumulator :: stack) altStack) :=
        Eval.pushDataNext Eval.done
      have pushEq := Eval.result_unique pushRun canonicalPush
      cases pushEq
      cases stack with
      | nil =>
          cases checkRun <;>
            simp_all [Opcode.activeFixedMainStackInputs?,
              Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
              Opcode.usesTimelockScriptNum]
      | cons signature rest =>
          obtain ⟨checkAlt, nextAccumulator, checkEq⟩ :=
            Eval.checkSigAddSingle_success_shape checkRun
          subst afterCheckAlt
          rw [checkEq] at restRun
          obtain ⟨tailAlt, tailArgs, finalRest, result, tailInput,
              finalEq⟩ := ih restRun
          rw [tailInput, finalEq]
          exact ⟨tailAlt,
            ⟨signature :: tailArgs, finalRest, result, by simp, rfl⟩⟩

/-- A successful nonempty CHECKSIGADD multisig body consumes a prefix of
    signatures and leaves one accumulator. -/
private theorem Eval.compileCheckSigAdd_success_shape
    (firstKey : PubKey) (keys : List PubKey)
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compileCheckSigAdd (firstKey :: keys)) stack altStack
      flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  have combined : Eval
      ([.pushData firstKey] ++
        ([.op .OP_CHECKSIG] ++ compileCheckSigAddTail keys))
      stack altStack flags ctx (.success finalStack finalAlt) := by
    simpa [compileCheckSigAdd, List.append_assoc] using run
  obtain ⟨afterPush, afterPushAlt, pushRun, tailRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) combined
  obtain ⟨afterCheck, afterCheckAlt, checkRun, restRun⟩ :=
    Eval.splitBalancedAppend_success
      (.atom (by simp [NonConditional])) tailRun
  have canonicalPush : Eval [.pushData firstKey] stack altStack flags ctx
      (.success (firstKey :: stack) altStack) := Eval.pushDataNext Eval.done
  have pushEq := Eval.result_unique pushRun canonicalPush
  cases pushEq
  cases stack with
  | nil =>
      have failed := Eval.fixedArityStackUnderflow_result
        (opcode := .OP_CHECKSIG) (required := 2) (arity := rfl)
        (underflow := by simp) checkRun
      contradiction
  | cons signature rest =>
      obtain ⟨checkAlt, accumulator, checkEq⟩ :=
        Eval.checkSigSingle_success_shape checkRun
      subst afterCheckAlt
      rw [checkEq] at restRun
      obtain ⟨tailAlt, tailArgs, finalRest, result, tailInput, finalEq⟩ :=
        Eval.compileCheckSigAddTail_success_shape keys restRun
      rw [tailInput, finalEq]
      exact ⟨tailAlt,
        ⟨signature :: tailArgs, finalRest, result, by simp, rfl⟩⟩

/-- A successful legacy multisignature decode over the compiler's canonical
    key/count prefix consumes exactly the threshold signatures and one dummy. -/
private theorem decodeCheckMultiSigOperandsFor_compiled_shape
    {threshold : Nat} {keys : List PubKey} {stack : Stack}
    {operands : CheckMultiSigOperands}
    {flags : ScriptFlags} {ctx : TxContext}
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (decoded : decodeCheckMultiSigOperandsFor flags ctx
      (scriptNat keys.length ::
        (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack) = .ok operands)
    (dummyOk : checkMultiSigDummy flags operands.dummy = .ok ()) :
    ∃ signatures dummy rest,
      stack = signatures ++ dummy :: rest ∧
      signatures.length = threshold ∧ operands.rest = rest := by
  have decodeKeys := decodeScriptNum_scriptNat_multi_count keys.length flags
    keyBound
  have decodeThreshold := decodeScriptNum_scriptNat_multi_count threshold flags
    (Nat.le_trans thresholdBound keyBound)
  unfold decodeCheckMultiSigOperandsFor at decoded
  split at decoded
  · contradiction
  · simp only [decodeCheckMultiSigOperands, bind, Except.bind] at decoded
    simp at decoded
    rw [decodeKeys] at decoded
    have keyNonnegative : ¬ ((keys.length : Int) < 0) := by omega
    have keyWithinLimit :
        ¬ ((maxPubKeysPerMultiSig : Int) < (keys.length : Int)) := by
      omega
    simp [keyNonnegative, keyWithinLimit] at decoded
    rw [decodeThreshold] at decoded
    have thresholdNonnegative : ¬ ((threshold : Int) < 0) := by omega
    have thresholdWithinKeys : ¬ ((keys.length : Int) < threshold) := by omega
    simp [thresholdNonnegative, thresholdWithinKeys] at decoded
    split at decoded
    · contradiction
    · split at decoded
      · cases decoded
        simp [checkMultiSigDummy] at dummyOk
      · rename_i dummy rest afterDrop
        cases decoded
        refine ⟨stack.take threshold, dummy, rest, ?_, ?_, rfl⟩
        · have parts := List.take_append_drop threshold stack
          rw [afterDrop] at parts
          exact parts.symm
        · simp [List.length_take]
          omega

/-- The compiler's legacy key-push prefix contains no control-flow
    delimiters. -/
private theorem compileKeyPushes_balancedControlFlow (keys : List PubKey) :
    BalancedControlFlow (compileKeyPushes keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih =>
      exact .append (.atom (by simp [NonConditional])) ih

/-- Successful legacy multisignature compilation consumes an input prefix and
    replaces it with one boolean result. -/
private theorem Eval.legacyMulti_success_shape
    {threshold : Nat} {keys : List PubKey}
    {stack altStack finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (keyBound : keys.length ≤ maxPubKeysPerMultiSig)
    (thresholdBound : threshold ≤ keys.length)
    (run : Eval
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length, .op .OP_CHECKMULTISIG])
      stack altStack flags ctx (.success finalStack finalAlt)) :
    finalAlt = altStack ∧ ∃ args rest result,
      stack = args ++ rest ∧ finalStack = result :: rest := by
  have combined : Eval
      (([.pushNum threshold] ++ compileKeyPushes keys ++
          [.pushNum keys.length]) ++ [.op .OP_CHECKMULTISIG])
      stack altStack flags ctx (.success finalStack finalAlt) := by
    simpa [List.append_assoc] using run
  have prefixBalanced : BalancedControlFlow
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length]) :=
    .append
      (.append (.atom (by simp [NonConditional]))
        (compileKeyPushes_balancedControlFlow keys))
      (.atom (by simp [NonConditional]))
  obtain ⟨middle, middleAlt, prefixRun, checkRun⟩ :=
    Eval.splitBalancedAppend_success prefixBalanced combined
  have thresholdRun : Eval [.pushNum threshold] stack altStack flags ctx
      (.success (scriptNat threshold :: stack) altStack) := by
    exact Eval.pushNum threshold [] stack altStack flags ctx _ Eval.done
  have keysRun := compileKeyPushes_execution keys flags ctx
    (scriptNat threshold :: stack) altStack
  have countRun : Eval [.pushNum keys.length]
      ((keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack)
      altStack flags ctx
      (.success
        (scriptNat keys.length ::
          (keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: stack)
        altStack) := by
    exact Eval.pushNum keys.length [] _ altStack flags ctx _ Eval.done
  have canonicalPrefix : Eval
      ([.pushNum threshold] ++ compileKeyPushes keys ++
        [.pushNum keys.length]) stack altStack flags ctx
      (.success
        (scriptNat keys.length ::
          (keys.map (fun key => key.bytes)).reverse ++
            scriptNat threshold :: stack)
        altStack) := by
    exact Eval.append (Eval.append thresholdRun keysRun) countRun
  have prefixEq := Eval.result_unique prefixRun canonicalPrefix
  cases prefixEq
  let opcodeStack : Stack :=
    scriptNat keys.length ::
      (keys.map (fun key => key.bytes)).reverse ++
        scriptNat threshold :: stack
  cases decodedEq : decodeCheckMultiSigOperandsFor flags ctx opcodeStack with
  | error error =>
      have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack altStack flags ctx
          (.failure error) :=
        Eval.checkmultisig_operand_failure opcodeStack [] altStack flags ctx
          error decodedEq
      have equal := Eval.result_unique checkRun failed
      contradiction
  | ok operands =>
      cases checkedEq : checkMultiSigFor checkSig flags ctx
          operands.signatures operands.pubkeys with
      | error error =>
          have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack altStack
              flags ctx (.failure error) :=
            Eval.checkmultisig_encoding_failure opcodeStack operands []
              altStack flags ctx error decodedEq checkedEq
          have equal := Eval.result_unique checkRun failed
          contradiction
      | ok checked =>
          cases checked with
          | false =>
              by_cases nullFail : nullFailSatisfied flags operands.signatures
              · cases dummyEq : checkMultiSigDummy flags operands.dummy with
                | error error =>
                    have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                        altStack flags ctx (.failure error) :=
                      Eval.checkmultisig_dummy_failure opcodeStack operands []
                        altStack flags ctx false error decodedEq checkedEq
                        (Or.inr nullFail) dummyEq
                    have equal := Eval.result_unique checkRun failed
                    contradiction
                | ok successValue =>
                    cases successValue
                    have canonical : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                        altStack flags ctx
                        (.success (falseElement :: operands.rest) altStack) :=
                      Eval.checkmultisig_failure opcodeStack operands []
                        altStack flags ctx _ decodedEq checkedEq nullFail dummyEq
                        Eval.done
                    have equal := Eval.result_unique checkRun canonical
                    cases equal
                    obtain ⟨signatures, dummy, rest, inputEq,
                        signatureCount, restEq⟩ :=
                      decodeCheckMultiSigOperandsFor_compiled_shape keyBound
                        thresholdBound decodedEq dummyEq
                    rw [restEq]
                    refine ⟨rfl, signatures ++ [dummy], rest, falseElement,
                      ?_, rfl⟩
                    simpa [List.append_assoc] using inputEq
              · have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                    altStack flags ctx (.failure .sigNullFail) :=
                  Eval.checkmultisig_nullfail_failure opcodeStack operands []
                    altStack flags ctx decodedEq checkedEq nullFail
                have equal := Eval.result_unique checkRun failed
                contradiction
          | true =>
              cases dummyEq : checkMultiSigDummy flags operands.dummy with
              | error error =>
                  have failed : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                      altStack flags ctx (.failure error) :=
                    Eval.checkmultisig_dummy_failure opcodeStack operands []
                      altStack flags ctx true error decodedEq checkedEq
                      (Or.inl rfl) dummyEq
                  have equal := Eval.result_unique checkRun failed
                  contradiction
              | ok successValue =>
                  cases successValue
                  have canonical : Eval [.op .OP_CHECKMULTISIG] opcodeStack
                      altStack flags ctx
                      (.success (trueElement :: operands.rest) altStack) :=
                    Eval.checkmultisig_success opcodeStack operands [] altStack
                      flags ctx _ decodedEq checkedEq dummyEq Eval.done
                  have equal := Eval.result_unique checkRun canonical
                  cases equal
                  obtain ⟨signatures, dummy, rest, inputEq,
                      signatureCount, restEq⟩ :=
                    decodeCheckMultiSigOperandsFor_compiled_shape keyBound
                      thresholdBound decodedEq dummyEq
                  rw [restEq]
                  refine ⟨rfl, signatures ++ [dummy], rest, trueElement,
                    ?_, rfl⟩
                  simpa [List.append_assoc] using inputEq

set_option maxHeartbeats 800000 in
mutual

/-- Every correctness-typed fragment has the successful stack-frame behavior
    specified by its base type on arbitrary input stacks. -/
theorem refinedBaseTypeGuarantee_of_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx) :
    RefinedBaseTypeGuarantee fragment ty := by
  cases typed with
  | zero =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have canonical : Eval (compile .zero) stack altStack flags ctx
              (.success (scriptNum 0 :: stack) altStack) := by
            simp [compile, compileWithKeyHash]
            apply Eval.pushNum
            exact Eval.done
          have equal := Eval.result_unique evaluated canonical
          cases equal
          exact ⟨rfl, .b _ [] stack (scriptNum 0)
            (by simp [ArgumentFrameMatches])⟩
  | one =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have canonical : Eval (compile .one) stack altStack flags ctx
              (.success (scriptNum 1 :: stack) altStack) := by
            simp [compile, compileWithKeyHash]
            apply Eval.pushNum
            exact Eval.done
          have equal := Eval.result_unique evaluated canonical
          cases equal
          exact ⟨rfl, .b _ [] stack (scriptNum 1)
            (by simp [ArgumentFrameMatches])⟩
  | pk_k key =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have canonical : Eval (compile (.pk_k key)) stack altStack flags ctx
              (.success (key :: stack) altStack) := by
            simpa [compile, compileWithKeyHash] using
              (Eval.pushDataNext (data := key) Eval.done)
          have equal := Eval.result_unique evaluated canonical
          cases equal
          exact ⟨rfl, .k _ [] stack key
            (by simp [ArgumentFrameMatches])⟩
  | pk_h key =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          cases stack with
          | nil => grind [Eval]
          | cons top rest =>
              have altEq : finalAltStack = altStack := by grind [Eval]
              have stackEq : finalStack = top :: rest := by grind [Eval]
              rw [stackEq]
              exact ⟨altEq, .k _ [top] rest top
                (by simp [ArgumentFrameMatches])⟩
  | older n =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          have altEq : finalAltStack = altStack := by grind [Eval]
          have stackEq : finalStack = scriptNum n :: stack := by grind [Eval]
          rw [stackEq]
          exact ⟨altEq, .b _ [] stack (scriptNum n)
            (by simp [ArgumentFrameMatches])⟩
  | after n =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          have altEq : finalAltStack = altStack := by grind [Eval]
          have stackEq : finalStack = scriptNum n :: stack := by grind [Eval]
          rw [stackEq]
          exact ⟨altEq, .b _ [] stack (scriptNum n)
            (by simp [ArgumentFrameMatches])⟩
  | sha256 hash =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          cases stack with
          | nil => grind [Eval]
          | cons preimage rest =>
              have altEq : finalAltStack = altStack := by grind [Eval]
              obtain ⟨result, stackEq⟩ :
                  ∃ result, finalStack = result :: rest := by grind [Eval]
              rw [stackEq]
              exact ⟨altEq, .b _ [preimage] rest result
                (by simp [ArgumentFrameMatches])⟩
  | hash256 hash =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          cases stack with
          | nil => grind [Eval]
          | cons preimage rest =>
              have altEq : finalAltStack = altStack := by grind [Eval]
              obtain ⟨result, stackEq⟩ :
                  ∃ result, finalStack = result :: rest := by grind [Eval]
              rw [stackEq]
              exact ⟨altEq, .b _ [preimage] rest result
                (by simp [ArgumentFrameMatches])⟩
  | ripemd160 hash =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          cases stack with
          | nil => grind [Eval]
          | cons preimage rest =>
              have altEq : finalAltStack = altStack := by grind [Eval]
              obtain ⟨result, stackEq⟩ :
                  ∃ result, finalStack = result :: rest := by grind [Eval]
              rw [stackEq]
              exact ⟨altEq, .b _ [preimage] rest result
                (by simp [ArgumentFrameMatches])⟩
  | hash160 hash =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          simp only [compile, compileWithKeyHash] at evaluated
          cases stack with
          | nil => grind [Eval]
          | cons preimage rest =>
              have altEq : finalAltStack = altStack := by grind [Eval]
              obtain ⟨result, stackEq⟩ :
                  ∃ result, finalStack = result :: rest := by grind [Eval]
              rw [stackEq]
              exact ⟨altEq, .b _ [preimage] rest result
                (by simp [ArgumentFrameMatches])⟩
  | @and_v first second firstMods secondType firstTyped secondTyped branch =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval (compile first ++ compile second) stack altStack
              flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          obtain ⟨middle, middleAlt, firstRun, secondRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          obtain ⟨secondAlt, secondEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2.1
              middle middleAlt flags ctx (.success finalStack finalAltStack)
              secondRun
          subst middleAlt
          exact ⟨secondAlt,
            RefinedBaseStackEffect.afterV firstEffect secondEffect branch (by
              intro baseEq
              exact HasType.k_not_z secondTyped baseEq)⟩
  | @and_b first second firstMods secondMods firstTyped secondTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++ (compile second ++ [.op .OP_BOOLAND])) stack
              altStack flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, firstRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨beforeOp, beforeOpAlt, secondRun, binaryRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow second) tailRun
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          obtain ⟨secondAlt, secondEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2.1
              middle middleAlt flags ctx (.success beforeOp beforeOpAlt)
              secondRun
          subst middleAlt
          subst beforeOpAlt
          obtain ⟨firstArgs, firstRest, firstResult, firstInput,
              firstOutput, firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at secondEffect
          obtain ⟨secondArgs, rest, saved, secondResult, order, secondInput,
              secondOutput⟩ := secondEffect.w_inv
          have restEq : firstRest = secondArgs ++ rest := by
            grind
          rw [restEq] at firstInput
          cases order <;>
            simp only [BaseWOutputOrder.outputs, List.cons_append,
              List.nil_append] at secondOutput <;>
            rw [secondOutput] at binaryRun
          all_goals
            obtain ⟨altEq, result, finalEq⟩ :=
              Eval.boolAndSingle_success_shape binaryRun
            rw [firstInput, finalEq]
            exact ⟨altEq,
              (by
                simpa [List.append_assoc] using
                  RefinedBaseStackEffect.b
                    { z := firstMods.z && secondMods.z
                      o := (firstMods.z && secondMods.o) ||
                        (firstMods.o && secondMods.z)
                      n := firstMods.n || (firstMods.z && secondMods.n)
                      d := firstMods.d && secondMods.d
                      u := true }
                    (firstArgs ++ secondArgs) rest result (by
                      have noCount :
                          secondMods.z = false ∧ secondMods.o = false :=
                        HasType.w_no_zo secondTyped rfl
                      simp [ArgumentFrameMatches, noCount.1, noCount.2]))⟩
  | @or_b first second firstMods secondMods firstTyped firstD secondTyped
      secondD =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++ (compile second ++ [.op .OP_BOOLOR])) stack
              altStack flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, firstRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨beforeOp, beforeOpAlt, secondRun, binaryRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow second) tailRun
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          obtain ⟨secondAlt, secondEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2
              middle middleAlt flags ctx (.success beforeOp beforeOpAlt)
              secondRun
          subst middleAlt
          subst beforeOpAlt
          obtain ⟨firstArgs, firstRest, firstResult, firstInput,
              firstOutput, firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at secondEffect
          obtain ⟨secondArgs, rest, saved, secondResult, order, secondInput,
              secondOutput⟩ := secondEffect.w_inv
          have restEq : firstRest = secondArgs ++ rest := by
            grind
          rw [restEq] at firstInput
          cases order <;>
            simp only [BaseWOutputOrder.outputs, List.cons_append,
              List.nil_append] at secondOutput <;>
            rw [secondOutput] at binaryRun
          all_goals
            obtain ⟨altEq, result, finalEq⟩ :=
              Eval.boolOrSingle_success_shape binaryRun
            rw [firstInput, finalEq]
            exact ⟨altEq,
              (by
                simpa [List.append_assoc] using
                  RefinedBaseStackEffect.b
                    { z := firstMods.z && secondMods.z
                      o := (firstMods.z && secondMods.o) ||
                        (firstMods.o && secondMods.z)
                      n := false, d := true, u := true }
                    (firstArgs ++ secondArgs) rest result (by
                      have noCount :
                          secondMods.z = false ∧ secondMods.o = false :=
                        HasType.w_no_zo secondTyped rfl
                      simp [ArgumentFrameMatches, noCount.1, noCount.2]))⟩
  | @or_c first second firstMods secondMods firstTyped firstD firstUnit
      secondTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++
                ([.op .OP_NOTIF] ++ compile second ++ [.op .OP_ENDIF]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, firstRun, conditionalRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          subst middleAlt
          obtain ⟨firstArgs, rest, selector, firstInput, firstOutput,
              firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at conditionalRun
          rcases Eval.notifThen_success_cases
              (compile_balancedControlFlow second) conditionalRun with
            skipped | executed
          · obtain ⟨selectedTrue, finalEq, altEq⟩ := skipped
            rw [firstInput, finalEq]
            refine ⟨altEq, .v _ firstArgs rest ?_⟩
            simp only [ArgumentFrameMatches] at firstMatches ⊢
            constructor
            · intro zero
              simp only [Bool.and_eq_true] at zero
              exact firstMatches.1 zero.1
            · intro one
              simp only [Bool.and_eq_true] at one
              exact firstMatches.2 one.1
          · obtain ⟨selectedFalse, executed⟩ := executed
            obtain ⟨childAlt, childEffect⟩ :=
              refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2 rest
                altStack flags ctx (.success finalStack finalAltStack) executed
            obtain ⟨secondArgs, secondInput, secondMatches⟩ := childEffect.v_inv
            rw [secondInput] at firstInput
            rw [firstInput]
            refine ⟨childAlt,
              (by
                simpa [List.append_assoc] using
                  RefinedBaseStackEffect.v
                    { z := firstMods.z && secondMods.z
                      o := firstMods.o && secondMods.z }
                    (firstArgs ++ secondArgs) finalStack (by
                      simp only [ArgumentFrameMatches] at firstMatches secondMatches ⊢
                      constructor
                      · intro zero
                        simp only [Bool.and_eq_true] at zero
                        simp [List.length_append, firstMatches.1 zero.1,
                          secondMatches.1 zero.2]
                      · intro one
                        simp only [Bool.and_eq_true] at one
                        simp [List.length_append, firstMatches.2 one.1,
                          secondMatches.1 one.2]))⟩
  | @or_d first second firstMods secondMods firstTyped firstD firstUnit
      secondTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++
                ([.op .OP_IFDUP, .op .OP_NOTIF] ++ compile second ++
                  [.op .OP_ENDIF]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, firstRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨afterDup, afterDupAlt, dupRun, conditionalRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) tailRun
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          subst middleAlt
          obtain ⟨firstArgs, rest, selector, firstInput, firstOutput,
              firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at dupRun
          cases selectorBool : castToBool selector with
          | false =>
              have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest)
                  altStack flags ctx (.success (selector :: rest) altStack) :=
                Eval.ifdup_false selector rest altStack [] flags ctx _
                  selectorBool Eval.done
              have dupEq := Eval.result_unique dupRun canonicalDup
              cases dupEq
              rcases Eval.notifThen_success_cases
                  (compile_balancedControlFlow second) conditionalRun with
                skipped | executed
              · simp_all
              · obtain ⟨selectedFalse, secondRun⟩ := executed
                obtain ⟨childAlt, childEffect⟩ :=
                  refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2
                    rest altStack flags ctx
                    (.success finalStack finalAltStack) secondRun
                rw [firstInput]
                refine ⟨childAlt,
                  RefinedBaseStackEffect.prependArguments
                    (parentMods := {
                      z := firstMods.z && secondMods.z
                      o := firstMods.o && secondMods.z
                      n := false, d := secondMods.d, u := secondMods.u })
                    (leadingArgs := firstArgs) childEffect trivial (by
                      intro args childMatches
                      apply ArgumentFrameMatches.afterProducedSelector
                        firstMatches childMatches trivial
                      · intro zero
                        simp only [Bool.and_eq_true] at zero
                        exact zero
                      · intro one
                        simp only [Bool.and_eq_true] at one
                        exact Or.inr one
                      · intro impossible
                        contradiction)⟩
          | true =>
              have canonicalDup : Eval [.op .OP_IFDUP] (selector :: rest)
                  altStack flags ctx
                  (.success (selector :: selector :: rest) altStack) :=
                Eval.ifdup_true selector rest altStack [] flags ctx _
                  selectorBool Eval.done
              have dupEq := Eval.result_unique dupRun canonicalDup
              cases dupEq
              rcases Eval.notifThen_success_cases
                  (compile_balancedControlFlow second) conditionalRun with
                skipped | executed
              · obtain ⟨selectedTrue, finalEq, altEq⟩ := skipped
                rw [firstInput, finalEq]
                refine ⟨altEq, .b _ firstArgs rest selector ?_⟩
                simp only [ArgumentFrameMatches] at firstMatches ⊢
                constructor
                · intro zero
                  simp only [Bool.and_eq_true] at zero
                  exact firstMatches.1 zero.1
                · intro one
                  simp only [Bool.and_eq_true] at one
                  exact firstMatches.2 one.1
              · simp_all
  | @or_i first second firstType secondType firstTyped secondTyped branch
      sameBase =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have conditionalRun : Eval
              ([.op .OP_IF] ++ compile first ++ [.op .OP_ELSE] ++
                compile second ++ [.op .OP_ENDIF])
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          cases stack with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_IF) (required := 1) (arity := rfl)
                (underflow := by simp) conditionalRun
              contradiction
          | cons selector rest =>
              rcases Eval.ifElse_success_cases
                  (compile_balancedControlFlow first)
                  (compile_balancedControlFlow second) conditionalRun with
                firstRun | secondRun
              · obtain ⟨childAlt, childEffect⟩ :=
                  refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1
                    rest altStack flags ctx (.success finalStack finalAltStack)
                    firstRun
                refine ⟨childAlt,
                  RefinedBaseStackEffect.withSelector childEffect branch rfl
                    ?_ ?_⟩
                · intro one
                  exact (Bool.and_eq_true_iff.mp one).1
                · intro baseEq
                  have notZ := HasType.k_not_z firstTyped baseEq
                  simp [notZ]
              · obtain ⟨childAlt, childEffect⟩ :=
                  refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2
                    rest altStack flags ctx (.success finalStack finalAltStack)
                    secondRun
                have secondBranch : branchBase secondType.base := by
                  rw [← sameBase]
                  exact branch
                refine ⟨childAlt, ?_⟩
                simpa [sameBase] using
                  (RefinedBaseStackEffect.withSelector childEffect secondBranch
                    (parentMods := {
                      z := false
                      o := firstType.mods.z && secondType.mods.z
                      n := false
                      d := firstType.mods.d || secondType.mods.d
                      u := firstType.mods.u && secondType.mods.u }) rfl
                    (by
                      intro one
                      exact (Bool.and_eq_true_iff.mp one).2)
                    (by
                      intro baseEq
                      have notZ := HasType.k_not_z secondTyped baseEq
                      simp [notZ]))
  | @andor first second third firstMods secondType thirdType firstTyped firstD
      firstUnit secondTyped thirdTyped branch sameBase =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++
                ([.op .OP_NOTIF] ++ compile third ++ [.op .OP_ELSE] ++
                  compile second ++ [.op .OP_ENDIF]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, firstRun, conditionalRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.1 stack
              altStack flags ctx (.success middle middleAlt) firstRun
          subst middleAlt
          obtain ⟨firstArgs, rest, selector, firstInput, firstOutput,
              firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at conditionalRun
          rcases Eval.notifElse_success_cases
              (compile_balancedControlFlow third)
              (compile_balancedControlFlow second) conditionalRun with
            thirdRun | secondRun
          · obtain ⟨childAlt, childEffect⟩ :=
              refinedBaseTypeGuarantee_of_hasType thirdTyped wellFormed.2.2.1
                rest altStack flags ctx (.success finalStack finalAltStack)
                thirdRun
            have thirdBranch : branchBase thirdType.base := by
              rw [← sameBase]
              exact branch
            rw [firstInput]
            refine ⟨childAlt, ?_⟩
            simpa [sameBase] using
              (RefinedBaseStackEffect.prependArguments
                (parentMods := {
                  z := firstMods.z && secondType.mods.z && thirdType.mods.z
                  o := (firstMods.z && secondType.mods.o && thirdType.mods.o) ||
                    (firstMods.o && secondType.mods.z && thirdType.mods.z)
                  n := false
                  d := thirdType.mods.d
                  u := secondType.mods.u && thirdType.mods.u })
                (leadingArgs := firstArgs) childEffect thirdBranch (by
                  intro args childMatches
                  apply ArgumentFrameMatches.afterProducedSelector
                    firstMatches childMatches thirdBranch
                  · intro zero
                    simp only [Bool.and_eq_true] at zero
                    exact ⟨zero.1.1, zero.2⟩
                  · intro one
                    simp only [Bool.or_eq_true, Bool.and_eq_true] at one
                    rcases one with one | one
                    · exact Or.inl ⟨one.1.1, one.2⟩
                    · exact Or.inr ⟨one.1.1, one.2⟩
                  · intro baseEq
                    exact HasType.k_not_z thirdTyped baseEq))
          · obtain ⟨childAlt, childEffect⟩ :=
              refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2.1
                rest altStack flags ctx (.success finalStack finalAltStack)
                secondRun
            rw [firstInput]
            refine ⟨childAlt,
              RefinedBaseStackEffect.prependArguments
                (parentMods := {
                  z := firstMods.z && secondType.mods.z && thirdType.mods.z
                  o := (firstMods.z && secondType.mods.o && thirdType.mods.o) ||
                    (firstMods.o && secondType.mods.z && thirdType.mods.z)
                  n := false
                  d := thirdType.mods.d
                  u := secondType.mods.u && thirdType.mods.u })
                (leadingArgs := firstArgs) childEffect branch (by
                  intro args childMatches
                  apply ArgumentFrameMatches.afterProducedSelector
                    firstMatches childMatches branch
                  · intro zero
                    simp only [Bool.and_eq_true] at zero
                    exact ⟨zero.1.1, zero.1.2⟩
                  · intro one
                    simp only [Bool.or_eq_true, Bool.and_eq_true] at one
                    rcases one with one | one
                    · exact Or.inl ⟨one.1.1, one.1.2⟩
                    · exact Or.inr ⟨one.1.1, one.1.2⟩
                  · intro baseEq
                    exact HasType.k_not_z secondTyped baseEq)⟩
  | @c_wrap child mods childTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval (compile child ++ [.op .OP_CHECKSIG]) stack
              altStack flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          obtain ⟨middle, middleAlt, childRun, checkRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow child) combined
          obtain ⟨childAlt, childEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType childTyped wellFormed stack
              altStack flags ctx (.success middle middleAlt) childRun
          subst middleAlt
          obtain ⟨args, rest, key, inputEq, middleEq, frameMatches⟩ :=
            childEffect.k_inv
          rw [middleEq] at checkRun
          rw [inputEq]
          cases rest with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_CHECKSIG) (required := 2)
                (arity := rfl) (underflow := by simp) checkRun
              contradiction
          | cons signature suffix =>
              obtain ⟨altEq, result, stackEq⟩ :=
                Eval.checkSigSingle_success_shape checkRun
              rw [stackEq]
              have parentEffect : RefinedBaseStackEffect
                  ⟨.B, { o := mods.o, n := mods.n, d := mods.d, u := true }⟩
                  (args ++ signature :: suffix) (result :: suffix) := by
                simpa [List.append_assoc] using
                  RefinedBaseStackEffect.b
                    { o := mods.o, n := mods.n, d := mods.d, u := true }
                    (args ++ [signature]) suffix result (by
                      constructor
                      · simp
                      · intro one
                        have emptyArgs := frameMatches.2 one
                        simp at emptyArgs ⊢
                        omega)
              exact ⟨altEq, parentEffect⟩
  | @v_wrap child mods childTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have optimized : Eval (compileVerify (compile child)) stack altStack
              flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          have expanded := Eval.compileVerify_success_inverse
            (compile_balancedControlFlow child) optimized
          obtain ⟨middle, middleAlt, childRun, verifyRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow child) expanded
          obtain ⟨childAlt, childEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType childTyped wellFormed stack
              altStack flags ctx (.success middle middleAlt) childRun
          subst middleAlt
          obtain ⟨args, rest, result, inputEq, outputEq, frameMatches⟩ :=
            childEffect.b_inv
          rw [outputEq] at verifyRun
          obtain ⟨finalEq, altEq⟩ :=
            Eval.verifySingle_success_shape verifyRun
          rw [inputEq, finalEq]
          refine ⟨altEq, .v _ args rest ?_⟩
          simpa [ArgumentFrameMatches] using frameMatches
  | @a_wrap child mods childTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              ([.op .OP_TOALTSTACK] ++ compile child ++
                [.op .OP_FROMALTSTACK]) stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨middle, middleAlt, saveRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) combined
          obtain ⟨beforeRestore, beforeRestoreAlt, childRun, restoreRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow child) tailRun
          obtain ⟨childAlt, childEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType childTyped wellFormed middle
              middleAlt flags ctx (.success beforeRestore beforeRestoreAlt)
              childRun
          subst beforeRestoreAlt
          cases stack with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_TOALTSTACK) (required := 1)
                (arity := rfl) (underflow := by simp) saveRun
              contradiction
          | cons saved tail =>
              have canonicalSave : Eval [.op .OP_TOALTSTACK]
                  (saved :: tail) altStack flags ctx
                  (.success tail (saved :: altStack)) := by
                apply Eval.toAltStackNext
                exact Eval.done
              have saveEq := Eval.result_unique saveRun canonicalSave
              cases saveEq
              obtain ⟨args, rest, result, inputEq, outputEq, frameMatches⟩ :=
                childEffect.b_inv
              rw [outputEq] at restoreRun
              rw [inputEq]
              have canonicalRestore : Eval [.op .OP_FROMALTSTACK]
                  (result :: rest) (saved :: altStack) flags ctx
                  (.success (saved :: result :: rest) altStack) := by
                apply Eval.fromAltStackNext
                exact Eval.done
              have restoreEq := Eval.result_unique restoreRun canonicalRestore
              cases restoreEq
              exact ⟨rfl,
                .w _ args rest saved result .savedFirst trivial⟩
  | @s_wrap child mods childTyped oneArg =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval ([.op .OP_SWAP] ++ compile child) stack
              altStack flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          obtain ⟨middle, middleAlt, swapRun, childRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) combined
          cases stack with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_SWAP) (required := 2)
                (arity := rfl) (underflow := by simp) swapRun
              contradiction
          | cons saved tail =>
              cases tail with
              | nil =>
                  have failed := Eval.fixedArityStackUnderflow_result
                    (opcode := .OP_SWAP) (required := 2)
                    (arity := rfl) (underflow := by simp) swapRun
                  contradiction
              | cons argument rest =>
                  have canonicalSwap : Eval [.op .OP_SWAP]
                      (saved :: argument :: rest) altStack flags ctx
                      (.success (argument :: saved :: rest) altStack) := by
                    apply Eval.swap
                    exact Eval.done
                  have swapEq := Eval.result_unique swapRun canonicalSwap
                  cases swapEq
                  obtain ⟨altEq, childEffect⟩ :=
                    refinedBaseTypeGuarantee_of_hasType childTyped wellFormed
                      (argument :: saved :: rest) altStack flags ctx
                      (.success finalStack finalAltStack) childRun
                  obtain ⟨args, childRest, result, inputEq, outputEq,
                      frameMatches⟩ := childEffect.b_inv
                  have argsLength : args.length = 1 :=
                    frameMatches.2 oneArg
                  cases args with
                  | nil => simp at argsLength
                  | cons only remaining =>
                      cases remaining with
                      | cons second tail => simp at argsLength
                      | nil =>
                          simp only [List.singleton_append] at inputEq
                          cases inputEq
                          rw [outputEq]
                          exact ⟨altEq,
                            .w _ [argument] rest saved result .resultFirst
                              trivial⟩
  | @d_wrap child mods childTyped zeroArgs =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              ([.op .OP_DUP] ++
                ([.op .OP_IF] ++ compile child ++ [.op .OP_ENDIF]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨afterDup, afterDupAlt, dupRun, conditionalRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) combined
          cases stack with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_DUP) (required := 1) (arity := rfl)
                (underflow := by simp) dupRun
              contradiction
          | cons selector rest =>
              have canonicalDup : Eval [.op .OP_DUP] (selector :: rest)
                  altStack flags ctx
                  (.success (selector :: selector :: rest) altStack) :=
                Eval.dup selector rest [] altStack flags ctx _ Eval.done
              have dupEq := Eval.result_unique dupRun canonicalDup
              cases dupEq
              rcases Eval.ifThen_success_cases
                  (compile_balancedControlFlow child) conditionalRun with
                skipped | executed
              · obtain ⟨selectedFalse, finalEq, altEq⟩ := skipped
                rw [finalEq]
                exact ⟨altEq,
                  .b _ [selector] rest selector (by
                    simp [ArgumentFrameMatches])⟩
              · obtain ⟨selectedTrue, childRun⟩ := executed
                obtain ⟨childAlt, childEffect⟩ :=
                  refinedBaseTypeGuarantee_of_hasType childTyped wellFormed
                    (selector :: rest) altStack flags ctx
                    (.success finalStack finalAltStack) childRun
                obtain ⟨args, inputEq, frameMatches⟩ := childEffect.v_inv
                have emptyLength := frameMatches.1 zeroArgs
                have argsEmpty : args = [] :=
                  List.eq_nil_of_length_eq_zero emptyLength
                rw [argsEmpty] at inputEq
                simp only [List.nil_append] at inputEq
                rw [← inputEq]
                exact ⟨childAlt,
                  .b _ [selector] rest selector (by
                    simp [ArgumentFrameMatches])⟩
  | @j_wrap child mods childTyped nonzero =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              ([.op .OP_SIZE] ++ [.op .OP_0NOTEQUAL] ++
                ([.op .OP_IF] ++ compile child ++ [.op .OP_ENDIF]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
          obtain ⟨afterSize, afterSizeAlt, sizeRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) combined
          obtain ⟨afterGuard, afterGuardAlt, guardRun, conditionalRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) tailRun
          cases stack with
          | nil =>
              have failed := Eval.fixedArityStackUnderflow_result
                (opcode := .OP_SIZE) (required := 1) (arity := rfl)
                (underflow := by simp) sizeRun
              contradiction
          | cons top rest =>
              have canonicalSize : Eval [.op .OP_SIZE] (top :: rest)
                  altStack flags ctx
                  (.success (scriptNat top.size :: top :: rest) altStack) :=
                Eval.size top rest altStack [] flags ctx _ Eval.done
              have sizeEq := Eval.result_unique sizeRun canonicalSize
              cases sizeEq
              obtain ⟨guardAlt, guard, guardEq⟩ :=
                Eval.zeroNotEqualSingle_success_shape guardRun
              subst afterGuardAlt
              rw [guardEq] at conditionalRun
              rcases Eval.ifThen_success_cases
                  (compile_balancedControlFlow child) conditionalRun with
                skipped | executed
              · obtain ⟨selectedFalse, finalEq, altEq⟩ := skipped
                rw [finalEq]
                refine ⟨altEq, .b _ [top] rest top ?_⟩
                simp [ArgumentFrameMatches]
              · obtain ⟨selectedTrue, childRun⟩ := executed
                obtain ⟨childAlt, childEffect⟩ :=
                  refinedBaseTypeGuarantee_of_hasType childTyped wellFormed
                    (top :: rest) altStack flags ctx
                    (.success finalStack finalAltStack) childRun
                obtain ⟨args, childRest, result, inputEq, outputEq,
                    frameMatches⟩ := childEffect.b_inv
                rw [inputEq, outputEq]
                refine ⟨childAlt, .b _ args childRest result ?_⟩
                simp only [ArgumentFrameMatches] at frameMatches ⊢
                constructor
                · simp
                · exact frameMatches.2
  | @n_wrap child mods childTyped =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval (compile child ++ [.op .OP_0NOTEQUAL]) stack
              altStack flags ctx (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          obtain ⟨middle, middleAlt, childRun, normalizeRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow child) combined
          obtain ⟨childAlt, childEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType childTyped wellFormed stack
              altStack flags ctx (.success middle middleAlt) childRun
          subst middleAlt
          cases childEffect with
          | b childMods args rest result frameMatches =>
              obtain ⟨altEq, normalized, stackEq⟩ :=
                Eval.zeroNotEqualSingle_success_shape normalizeRun
              rw [stackEq]
              refine ⟨altEq, .b _ args rest normalized ?_⟩
              simpa [ArgumentFrameMatches] using frameMatches
  | @thresh threshold first fragments firstMods restTypes firstTyped firstD
      firstUnit restTyped restShape positive atMost =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile first ++
                (compileThreshTail fragments ++
                  [.pushNum threshold, .op .OP_EQUAL]))
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash, compileThresh,
              compileThreshWithKeyHash, compileThreshTail,
              List.append_assoc] using evaluated
          obtain ⟨afterFirst, afterFirstAlt, firstRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow first) combined
          obtain ⟨beforeFinal, beforeFinalAlt, thresholdTailRun, finalRun⟩ :=
            Eval.splitBalancedAppend_success
              (compileThreshTail_balancedControlFlow fragments) tailRun
          obtain ⟨firstAlt, firstEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType firstTyped wellFormed.2.1.1
              stack altStack flags ctx (.success afterFirst afterFirstAlt)
              firstRun
          subst afterFirstAlt
          obtain ⟨firstArgs, firstRest, accumulator, firstInput, firstOutput,
              firstMatches⟩ := firstEffect.b_inv
          rw [firstOutput] at thresholdTailRun
          cases fragments with
          | nil =>
              cases restTyped
              have tailEq := Eval.result_unique thresholdTailRun
                (Eval.done (stack := accumulator :: firstRest)
                  (altStack := altStack))
              cases tailEq
              obtain ⟨finalAlt, result, finalEq⟩ :=
                Eval.pushNumEqual_success_shape finalRun
              rw [firstInput, finalEq]
              refine ⟨finalAlt, .b _ firstArgs firstRest result ?_⟩
              simpa [ArgumentFrameMatches, MiniType.modifiers,
                CorrectnessModifiers.allZ,
                CorrectnessModifiers.oneOWithRestZ] using firstMatches
          | cons head tail =>
              obtain ⟨tailAlt, tailArgs, rest, tailAccumulator, tailInput,
                  tailOutput⟩ :=
                thresholdTailBaseGuarantee_of_hasTypeList restTyped restShape
                  wellFormed.2.1.2 accumulator firstRest altStack flags ctx
                  (.success beforeFinal beforeFinalAlt) thresholdTailRun
              subst beforeFinalAlt
              rw [tailOutput] at finalRun
              obtain ⟨finalAlt, result, finalEq⟩ :=
                Eval.pushNumEqual_success_shape finalRun
              rw [tailInput] at firstInput
              rw [firstInput, finalEq]
              refine ⟨finalAlt,
                (by
                  simpa [List.append_assoc] using
                    RefinedBaseStackEffect.b
                      { z := CorrectnessModifiers.allZ
                          (firstMods :: MiniType.modifiers restTypes)
                        o := CorrectnessModifiers.oneOWithRestZ
                          (firstMods :: MiniType.modifiers restTypes)
                        n := false, d := true, u := true }
                      (firstArgs ++ tailArgs) rest result (by
                        have noCount := thresholdRestModifiers_noCount
                          restTyped restShape (by simp)
                        simp [ArgumentFrameMatches,
                          CorrectnessModifiers.allZ,
                          CorrectnessModifiers.oneOWithRestZ,
                          noCount.1, noCount.2]))⟩
  | @multi threshold keys positive atMost =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have keyBound : keys.length ≤ maxPubKeysPerMultiSig := by
            simpa [CoreFragment.WellFormed, validLegacyMultiKeyCount,
              maxPubKeysPerMultiSig] using wellFormed.2.2.1
          have multiRun : Eval
              ([.pushNum threshold] ++ compileKeyPushes keys ++
                [.pushNum keys.length, .op .OP_CHECKMULTISIG])
              stack altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compile, compileWithKeyHash] using evaluated
          obtain ⟨finalAlt, args, rest, result, inputEq, outputEq⟩ :=
            Eval.legacyMulti_success_shape keyBound atMost multiRun
          rw [inputEq, outputEq]
          exact ⟨finalAlt,
            .b _ args rest result (by simp [ArgumentFrameMatches])⟩
  | @multi_a threshold keys positive atMost =>
      intro stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          cases keys with
          | nil => simp at atMost; omega
          | cons firstKey keys =>
              have combined : Eval
                  (compileCheckSigAdd (firstKey :: keys) ++
                    [.pushNum threshold, .op .OP_NUMEQUAL])
                  stack altStack flags ctx
                  (.success finalStack finalAltStack) := by
                simpa [compile, compileWithKeyHash] using evaluated
              obtain ⟨beforeFinal, beforeFinalAlt, bodyRun, finalRun⟩ :=
                Eval.splitBalancedAppend_success
                  (compileCheckSigAdd_balancedControlFlow (firstKey :: keys))
                  combined
              obtain ⟨bodyAlt, args, rest, accumulator, inputEq, outputEq⟩ :=
                Eval.compileCheckSigAdd_success_shape firstKey keys bodyRun
              subst beforeFinalAlt
              rw [outputEq] at finalRun
              obtain ⟨finalAlt, result, finalEq⟩ :=
                Eval.pushNumNumEqual_success_shape finalRun
              rw [inputEq, finalEq]
              exact ⟨finalAlt,
                .b _ args rest result (by simp [ArgumentFrameMatches])⟩

/-- Pointwise W typing supplies the accumulator-preserving contract used by a
    threshold tail. -/
theorem thresholdTailBaseGuarantee_of_hasTypeList
    {scriptCtx : ScriptContext} {fragments : List CoreFragment}
    {types : List MiniType}
    (typed : HasTypeList scriptCtx fragments types)
    (restTypes : thresholdRestTypes types)
    (wellFormed : CoreFragment.allWellFormed scriptCtx fragments) :
    ThresholdTailBaseGuarantee fragments := by
  cases typed with
  | nil =>
      intro accumulator stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have equal := Eval.result_unique evaluated
            (Eval.done (stack := accumulator :: stack) (altStack := altStack))
          cases equal
          exact ⟨rfl, ⟨[], stack, accumulator, rfl, rfl⟩⟩
  | @cons fragment ty fragments types headTyped tailTyped =>
      simp only [thresholdRestTypes] at restTypes
      intro accumulator stack altStack flags ctx outcome evaluated
      cases outcome with
      | failure error => trivial
      | success finalStack finalAltStack =>
          have combined : Eval
              (compile fragment ++
                ([.op .OP_ADD] ++ compileThreshTail fragments))
              (accumulator :: stack) altStack flags ctx
              (.success finalStack finalAltStack) := by
            simpa [compileThreshTail, compileThreshTailWithKeyHash,
              compile, List.append_assoc] using evaluated
          obtain ⟨beforeAdd, beforeAddAlt, headRun, tailRun⟩ :=
            Eval.splitBalancedAppend_success
              (compile_balancedControlFlow fragment) combined
          obtain ⟨afterAdd, afterAddAlt, addRun, restRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) tailRun
          obtain ⟨headAlt, headEffect⟩ :=
            refinedBaseTypeGuarantee_of_hasType headTyped wellFormed.1
              (accumulator :: stack) altStack flags ctx
              (.success beforeAdd beforeAddAlt) headRun
          subst beforeAddAlt
          have tyEq : ty = ⟨.W, ty.mods⟩ := by
            cases ty with
            | mk base mods =>
                simp only at restTypes ⊢
                rw [restTypes.1]
          have headEffectW : RefinedBaseStackEffect ⟨.W, ty.mods⟩
              (accumulator :: stack) beforeAdd := by
            rw [← tyEq]
            exact headEffect
          obtain ⟨headArgs, headRest, saved, headResult, order, headInput,
              headOutput⟩ := headEffectW.w_inv
          have stackEq : stack = headArgs ++ headRest := by
            grind
          cases order <;>
            simp only [BaseWOutputOrder.outputs, List.cons_append,
              List.nil_append] at headOutput <;>
            rw [headOutput] at addRun
          all_goals
            obtain ⟨addAlt, nextAccumulator, addOutput⟩ :=
              Eval.addSingle_success_shape addRun
            subst afterAddAlt
            rw [addOutput] at restRun
            obtain ⟨tailAlt, tailArgs, finalRest, result, tailInput,
                finalEq⟩ :=
              thresholdTailBaseGuarantee_of_hasTypeList tailTyped restTypes.2.2.2
                wellFormed.2 nextAccumulator headRest altStack flags ctx
                (.success finalStack finalAltStack) restRun
            rw [tailInput] at stackEq
            rw [finalEq]
            refine ⟨tailAlt, ⟨headArgs ++ tailArgs, finalRest, result, ?_, rfl⟩⟩
            simpa [List.append_assoc] using stackEq

end

/-- Correctness typing implies the public arbitrary-input base contract. -/
theorem baseTypeGuarantee_of_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx) :
    BaseTypeGuarantee fragment ty.base := by
  intro stack altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      obtain ⟨altEq, effect⟩ :=
        refinedBaseTypeGuarantee_of_hasType typed wellFormed stack altStack
          flags ctx (.success finalStack finalAltStack) evaluated
      exact ⟨altEq, effect.toBase⟩

/-- The remaining arbitrary-input part of core type soundness. -/
def BaseTypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    BaseTypeGuarantee m ty.base

/-- Core type soundness covers every B, V, K, and W correctness type. -/
def TypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    MiniTypeGuarantee ctx m ty

/-- Arbitrary-input base soundness now suffices for the complete core contract;
    generated-witness correctness and `d` completeness are discharged here. -/
theorem typeSoundnessCore_of_base
    (baseSound : BaseTypeSoundnessCore) : TypeSoundnessCore := by
  intro ctx m ty valid
  exact {
    base := baseSound valid
    generated := generatedTypeSoundnessCore valid
    dissatisfiable := fun enabled =>
      unconditionalDissatisfaction_of_wellFormed_hasType
        valid.hasType valid.wellFormed enabled
  }

/-- Surface type soundness is the same contract after core desugaring. -/
def TypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    MiniTypeGuarantee ctx (desugar m) ty

/-- Any proof of the core theorem immediately supplies the surface theorem. -/
theorem typeSoundnessSurface_of_core
    (sound : TypeSoundnessCore) : TypeSoundnessSurface := by
  intro ctx m ty valid
  exact sound valid

/-- Every valid, correctly typed core fragment satisfies its arbitrary-input
    B/V/K/W stack-frame contract. -/
theorem baseTypeSoundnessCore : BaseTypeSoundnessCore := by
  intro ctx m ty valid
  exact baseTypeGuarantee_of_hasType valid.hasType valid.wellFormed

/-- Complete correctness type soundness for core Miniscript fragments. -/
theorem typeSoundnessCore : TypeSoundnessCore :=
  typeSoundnessCore_of_base baseTypeSoundnessCore

/-- Complete correctness type soundness for surface Miniscript fragments after
    desugaring. -/
theorem typeSoundnessSurface : TypeSoundnessSurface :=
  typeSoundnessSurface_of_core typeSoundnessCore

end LeanMiniscript.Miniscript
