import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs
import LeanMiniscript.Miniscript.TypeSoundnessProofs.ExecutionDecomposition
import LeanMiniscript.Miniscript.TypeSoundnessProofs.BaseFrames
import LeanMiniscript.Miniscript.TypeSoundnessProofs.SuccessShapes

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type soundness: arbitrary-input base-type guarantee

The mutual induction proving the refined B/V/K/W stack-frame contract for every
correctly typed core fragment and threshold tail.
-/

/-- Build a refined guarantee by handling only successful executions; failing
    outcomes satisfy the guarantee trivially. -/
private theorem RefinedBaseTypeGuarantee.of_success
    {fragment : CoreFragment} {ty : MiniType}
    (success : ∀ (stack altStack : Stack) (flags : ScriptFlags)
        (ctx : TxContext) (finalStack finalAltStack : Stack),
      Eval (compile fragment) stack altStack flags ctx
          (.success finalStack finalAltStack) →
        finalAltStack = altStack ∧
          RefinedBaseStackEffect ty stack finalStack) :
    RefinedBaseTypeGuarantee fragment ty := by
  intro stack altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      exact success stack altStack flags ctx finalStack finalAltStack evaluated

/-- Apply a refined guarantee to one successful execution. -/
private theorem RefinedBaseTypeGuarantee.run
    {fragment : CoreFragment} {ty : MiniType}
    {stack altStack finalStack finalAltStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (guarantee : RefinedBaseTypeGuarantee fragment ty)
    (run : Eval (compile fragment) stack altStack flags ctx
      (.success finalStack finalAltStack)) :
    finalAltStack = altStack ∧ RefinedBaseStackEffect ty stack finalStack :=
  guarantee stack altStack flags ctx _ run

/-- A successful run of a compiled fragment followed by a suffix splits into
    the fragment's refined effect and a suffix run that starts from the
    original alternate stack. -/
private theorem RefinedBaseTypeGuarantee.append_success
    {fragment : CoreFragment} {ty : MiniType} {suffix : Script}
    {stack altStack finalStack finalAltStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (guarantee : RefinedBaseTypeGuarantee fragment ty)
    (run : Eval (compile fragment ++ suffix) stack altStack flags ctx
      (.success finalStack finalAltStack)) :
    ∃ middle, RefinedBaseStackEffect ty stack middle ∧
      Eval suffix middle altStack flags ctx
        (.success finalStack finalAltStack) := by
  obtain ⟨middle, middleAlt, fragmentRun, suffixRun⟩ :=
    Eval.splitBalancedAppend_success (compile_balancedControlFlow fragment) run
  obtain ⟨altEq, effect⟩ := guarantee.run fragmentRun
  subst altEq
  exact ⟨middle, effect, suffixRun⟩

set_option maxHeartbeats 800000 in
mutual

/-- Every correctness-typed fragment has the successful stack-frame behavior
    specified by its base type on arbitrary input stacks. -/
theorem refinedBaseTypeGuarantee_of_hasType
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty)
    (wellFormed : fragment.WellFormed scriptCtx) :
    RefinedBaseTypeGuarantee fragment ty := by
  apply RefinedBaseTypeGuarantee.of_success
  intro stack altStack flags ctx finalStack finalAltStack evaluated
  cases typed with
  | zero =>
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
      have canonical : Eval (compile (.pk_k key)) stack altStack flags ctx
          (.success (key :: stack) altStack) := by
        simpa [compile, compileWithKeyHash] using
          (Eval.pushDataNext (data := key) Eval.done)
      have equal := Eval.result_unique evaluated canonical
      cases equal
      exact ⟨rfl, .k _ [] stack key
        (by simp [ArgumentFrameMatches])⟩
  | pk_h key =>
      simp only [compile, compileWithKeyHash] at evaluated
      cases stack with
      | nil => grind [Eval, Opcode.isUpgradeableNop]
      | cons top rest =>
          have altEq : finalAltStack = altStack := by grind [Eval, Opcode.isUpgradeableNop]
          have stackEq : finalStack = top :: rest := by grind [Eval, Opcode.isUpgradeableNop]
          rw [stackEq]
          exact ⟨altEq, .k _ [top] rest top
            (by simp [ArgumentFrameMatches])⟩
  | older n | after n =>
      simp only [compile, compileWithKeyHash] at evaluated
      have altEq : finalAltStack = altStack := by grind [Eval, Opcode.isUpgradeableNop]
      have stackEq : finalStack = scriptNum n :: stack := by grind [Eval, Opcode.isUpgradeableNop]
      rw [stackEq]
      exact ⟨altEq, .b _ [] stack (scriptNum n)
        (by simp [ArgumentFrameMatches])⟩
  | sha256 hash | hash256 hash | ripemd160 hash | hash160 hash =>
      simp only [compile, compileWithKeyHash] at evaluated
      cases stack with
      | nil => grind [Eval, Opcode.isUpgradeableNop]
      | cons preimage rest =>
          have altEq : finalAltStack = altStack := by grind [Eval, Opcode.isUpgradeableNop]
          obtain ⟨result, stackEq⟩ :
              ∃ result, finalStack = result :: rest := by grind [Eval, Opcode.isUpgradeableNop]
          rw [stackEq]
          exact ⟨altEq, .b _ [preimage] rest result
            (by simp [ArgumentFrameMatches])⟩
  | @and_v first second firstMods secondType firstTyped secondTyped branch =>
      have combined : Eval (compile first ++ compile second) stack altStack
          flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash] using evaluated
      obtain ⟨middle, firstEffect, secondRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨secondAlt, secondEffect⟩ :=
        (refinedBaseTypeGuarantee_of_hasType secondTyped wellFormed.2.1).run
          secondRun
      exact ⟨secondAlt,
        RefinedBaseStackEffect.afterV firstEffect secondEffect branch (by
          intro baseEq
          exact HasType.k_not_z secondTyped baseEq)⟩
  | @and_b first second firstMods secondMods firstTyped secondTyped =>
      have combined : Eval
          (compile first ++ (compile second ++ [.op .OP_BOOLAND])) stack
          altStack flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
      obtain ⟨middle, firstEffect, tailRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨beforeOp, secondEffect, binaryRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType secondTyped
          wellFormed.2.1).append_success tailRun
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
      have combined : Eval
          (compile first ++ (compile second ++ [.op .OP_BOOLOR])) stack
          altStack flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
      obtain ⟨middle, firstEffect, tailRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨beforeOp, secondEffect, binaryRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType secondTyped
          wellFormed.2).append_success tailRun
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
      have combined : Eval
          (compile first ++
            ([.op .OP_NOTIF] ++ compile second ++ [.op .OP_ENDIF]))
          stack altStack flags ctx
          (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
      obtain ⟨middle, firstEffect, conditionalRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨firstArgs, rest, selector, firstInput, firstOutput,
          firstMatches⟩ := firstEffect.b_inv
      rw [firstOutput] at conditionalRun
      rcases Eval.notifThen_success_cases
          (compile_balancedControlFlow second) conditionalRun with
        skipped | executed
      · obtain ⟨selectedTrue, finalEq, altEq⟩ := skipped
        rw [firstInput, finalEq]
        refine ⟨altEq, .v _ firstArgs rest ?_⟩
        simp only [ArgumentFrameMatches, Bool.and_eq_true] at firstMatches ⊢
        exact ⟨fun zero => firstMatches.1 zero.1,
          fun one => firstMatches.2 one.1⟩
      · obtain ⟨selectedFalse, executed⟩ := executed
        obtain ⟨childAlt, childEffect⟩ :=
          (refinedBaseTypeGuarantee_of_hasType secondTyped
            wellFormed.2).run executed
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
      have combined : Eval
          (compile first ++
            ([.op .OP_IFDUP, .op .OP_NOTIF] ++ compile second ++
              [.op .OP_ENDIF]))
          stack altStack flags ctx
          (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
      obtain ⟨middle, firstEffect, tailRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨afterDup, afterDupAlt, dupRun, conditionalRun⟩ :=
        Eval.splitBalancedAppend_success
          (.atom (by simp [NonConditional])) tailRun
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
              (refinedBaseTypeGuarantee_of_hasType secondTyped
                wellFormed.2).run secondRun
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
            simp only [ArgumentFrameMatches, Bool.and_eq_true] at firstMatches ⊢
            exact ⟨fun zero => firstMatches.1 zero.1,
              fun one => firstMatches.2 one.1⟩
          · simp_all
  | @or_i first second firstType secondType firstTyped secondTyped branch
      sameBase =>
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
              (refinedBaseTypeGuarantee_of_hasType firstTyped
                wellFormed.1).run firstRun
            refine ⟨childAlt,
              RefinedBaseStackEffect.withSelector childEffect branch rfl
                ?_ ?_⟩
            · intro one
              exact (Bool.and_eq_true_iff.mp one).1
            · intro baseEq
              have notZ := HasType.k_not_z firstTyped baseEq
              simp [notZ]
          · obtain ⟨childAlt, childEffect⟩ :=
              (refinedBaseTypeGuarantee_of_hasType secondTyped
                wellFormed.2).run secondRun
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
      have combined : Eval
          (compile first ++
            ([.op .OP_NOTIF] ++ compile third ++ [.op .OP_ELSE] ++
              compile second ++ [.op .OP_ENDIF]))
          stack altStack flags ctx
          (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, List.append_assoc] using evaluated
      obtain ⟨middle, firstEffect, conditionalRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.1).append_success combined
      obtain ⟨firstArgs, rest, selector, firstInput, firstOutput,
          firstMatches⟩ := firstEffect.b_inv
      rw [firstOutput] at conditionalRun
      rcases Eval.notifElse_success_cases
          (compile_balancedControlFlow third)
          (compile_balancedControlFlow second) conditionalRun with
        thirdRun | secondRun
      · obtain ⟨childAlt, childEffect⟩ :=
          (refinedBaseTypeGuarantee_of_hasType thirdTyped
            wellFormed.2.2.1).run thirdRun
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
          (refinedBaseTypeGuarantee_of_hasType secondTyped
            wellFormed.2.1).run secondRun
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
      have combined : Eval (compile child ++ [.op .OP_CHECKSIG]) stack
          altStack flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash] using evaluated
      obtain ⟨middle, childEffect, checkRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType childTyped
          wellFormed).append_success combined
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
      have optimized : Eval (compileVerify (compile child)) stack altStack
          flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash] using evaluated
      have expanded := Eval.compileVerify_success_inverse
        (compile_balancedControlFlow child) optimized
      obtain ⟨middle, childEffect, verifyRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType childTyped
          wellFormed).append_success expanded
      obtain ⟨args, rest, result, inputEq, outputEq, frameMatches⟩ :=
        childEffect.b_inv
      rw [outputEq] at verifyRun
      obtain ⟨finalEq, altEq⟩ :=
        Eval.verifySingle_success_shape verifyRun
      rw [inputEq, finalEq]
      refine ⟨altEq, .v _ args rest ?_⟩
      simpa [ArgumentFrameMatches] using frameMatches
  | @a_wrap child mods childTyped =>
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
        (refinedBaseTypeGuarantee_of_hasType childTyped wellFormed).run
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
                (refinedBaseTypeGuarantee_of_hasType childTyped
                  wellFormed).run childRun
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
              (refinedBaseTypeGuarantee_of_hasType childTyped
                wellFormed).run childRun
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
              (refinedBaseTypeGuarantee_of_hasType childTyped
                wellFormed).run childRun
            obtain ⟨args, childRest, result, inputEq, outputEq,
                frameMatches⟩ := childEffect.b_inv
            rw [inputEq, outputEq]
            refine ⟨childAlt, .b _ args childRest result ?_⟩
            simp only [ArgumentFrameMatches] at frameMatches ⊢
            constructor
            · simp
            · exact frameMatches.2
  | @n_wrap child mods childTyped =>
      have combined : Eval (compile child ++ [.op .OP_0NOTEQUAL]) stack
          altStack flags ctx (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash] using evaluated
      obtain ⟨middle, childEffect, normalizeRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType childTyped
          wellFormed).append_success combined
      cases childEffect with
      | b childMods args rest result frameMatches =>
          obtain ⟨altEq, normalized, stackEq⟩ :=
            Eval.zeroNotEqualSingle_success_shape normalizeRun
          rw [stackEq]
          refine ⟨altEq, .b _ args rest normalized ?_⟩
          simpa [ArgumentFrameMatches] using frameMatches
  | @thresh threshold first fragments firstMods restTypes firstTyped firstD
      firstUnit restTyped restShape positive atMost =>
      have combined : Eval
          (compile first ++
            (compileThreshTail fragments ++
              [.pushNum threshold, .op .OP_EQUAL]))
          stack altStack flags ctx
          (.success finalStack finalAltStack) := by
        simpa [compile, compileWithKeyHash, compileThresh,
          compileThreshWithKeyHash, compileThreshTail,
          List.append_assoc] using evaluated
      obtain ⟨afterFirst, firstEffect, tailRun⟩ :=
        (refinedBaseTypeGuarantee_of_hasType firstTyped
          wellFormed.2.1.1).append_success combined
      obtain ⟨beforeFinal, beforeFinalAlt, thresholdTailRun, finalRun⟩ :=
        Eval.splitBalancedAppend_success
          (compileThreshTail_balancedControlFlow fragments) tailRun
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
          obtain ⟨beforeAdd, headEffect, tailRun⟩ :=
            (refinedBaseTypeGuarantee_of_hasType headTyped
              wellFormed.1).append_success combined
          obtain ⟨afterAdd, afterAddAlt, addRun, restRun⟩ :=
            Eval.splitBalancedAppend_success
              (.atom (by simp [NonConditional])) tailRun
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

end LeanMiniscript.Miniscript
