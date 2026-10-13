import LeanMiniscript.Miniscript.SatisfactionCandidateProofs
import LeanMiniscript.Miniscript.SatisfactionProofs
import LeanMiniscript.Script.ScriptNumProofs
import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs.Wrappers

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Generated satisfactions: connective contracts

`GeneratedContract` composition for `and_v`, `and_b`, `or_b`, `or_c`, `or_d`,
`or_i`, and `andor`.
-/

/-! ## Compositional connective contracts -/

namespace GeneratedContract

private theorem andVInput
    {firstWitness secondWitness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness true firstMods)
    (second : GeneratedInput secondWitness expected secondMods) :
    GeneratedInput (Witness.combine firstWitness secondWitness) expected {
      z := firstMods.z && secondMods.z
      o := (firstMods.z && secondMods.o) ||
        (firstMods.o && secondMods.z)
      n := firstMods.n || (firstMods.z && secondMods.n)
      d := false
      u := secondMods.u
    } := by
  apply first.combine second
  · intro enabled
    simpa using enabled
  · intro enabled
    simpa [Bool.or_eq_true] using enabled
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with firstN | ⟨firstZero, secondN⟩
    · exact Or.inl ⟨firstN, fun _ => rfl⟩
    · exact Or.inr ⟨firstZero, secondN, fun truth => truth⟩

theorem andV_b
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          exact .b (andVInput firstInput secondInput)
            (secondFacts.retype (by simp))
            (by simpa using firstExec.and_v_b secondExec)

theorem andV_k
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | k secondInput ownArgs key signature stackShape secondExec checked =>
          apply GeneratedContract.k
            (input := andVInput firstInput secondInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.and_v_k secondExec
          · exact checked

theorem andV_v
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.V, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.and_v first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | v firstInput firstTrue firstExec =>
      cases secondContract with
      | v secondInput secondTrue secondExec =>
          exact .v (andVInput firstInput secondInput) secondTrue
            (by simpa using firstExec.and_v_v secondExec)

private theorem booleanInput
    {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods targetMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness firstExpected firstMods)
    (second : GeneratedInput secondWitness secondExpected secondMods)
    (zero : targetMods.z = true →
      firstMods.z = true ∧ secondMods.z = true)
    (one : targetMods.o = true →
      (firstMods.z = true ∧ secondMods.o = true) ∨
      (firstMods.o = true ∧ secondMods.z = true))
    (nonzero : targetMods.n = true →
      firstMods.n = true ∨
      (firstMods.z = true ∧ secondMods.n = true))
    (truth : expected = true →
      firstExpected = true ∧ secondExpected = true) :
    GeneratedInput (Witness.combine firstWitness secondWitness)
      expected targetMods := by
  apply first.combine second zero one
  intro enabled
  rcases nonzero enabled with firstN | ⟨firstZero, secondN⟩
  · exact Or.inl ⟨firstN, fun expectedTrue => (truth expectedTrue).1⟩
  · exact Or.inr ⟨firstZero, secondN,
      fun expectedTrue => (truth expectedTrue).2⟩

theorem andB
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness firstExpected flags txCtx
      ⟨.B, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness secondExpected
      flags txCtx ⟨.W, secondMods⟩)
    (expectedEq : (firstExpected && secondExpected) = expected) :
    GeneratedContract (.and_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := firstMods.n || (firstMods.z && secondMods.n)
        d := firstMods.d && secondMods.d
        u := true
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | w secondInput order secondFacts secondExec =>
          apply GeneratedContract.b
          · apply booleanInput firstInput secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · intro expectedTrue
              have both : (firstExpected && secondExpected) = true :=
                expectedEq.trans expectedTrue
              simpa using both
          · exact BooleanResultFacts.canonical expected _ flags
          · have executed := firstExec.and_b secondExec
              (firstFacts.binaryDecoded secondFacts order)
            rw [firstFacts.nonzero, secondFacts.nonzero, expectedEq] at executed
            simpa using executed

theorem orB
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstExpected secondExpected expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness firstExpected flags txCtx
      ⟨.B, firstMods⟩)
    (secondContract : GeneratedContract second secondWitness secondExpected
      flags txCtx ⟨.W, secondMods⟩)
    (expectedEq : (firstExpected || secondExpected) = expected) :
    GeneratedContract (.or_b first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := (firstMods.z && secondMods.o) ||
          (firstMods.o && secondMods.z)
        n := false
        d := true
        u := true
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | w secondInput order secondFacts secondExec =>
          apply GeneratedContract.b
          · apply firstInput.combine secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              simpa [Bool.or_eq_true] using enabled
            · simp
          · exact BooleanResultFacts.canonical expected _ flags
          · have executed := firstExec.or_b secondExec
              (firstFacts.binaryDecoded secondFacts order)
            rw [firstFacts.nonzero, secondFacts.nonzero, expectedEq] at executed
            simpa using executed

theorem orC_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedContract (.or_c first second) witness true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
      }⟩ := by
  cases contract with
  | b input facts executed =>
      apply GeneratedContract.v
        (input := input.mono (by simp_all) (by simp_all) (by simp)) rfl
      exact executed.or_c_left (facts.minimalIfSatisfied firstUnit) facts.truth

theorem orC_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness true flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.or_c first second)
      (Witness.combine firstWitness secondWitness) true flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | v secondInput secondTrue secondExec =>
          apply GeneratedContract.v
            (input := by
              apply firstInput.combine secondInput
              · intro enabled
                simpa using enabled
              · intro enabled
                right
                simpa using enabled
              · simp)
            rfl
          simpa using firstExec.or_c_right
            (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec

theorem orD_left
    {first second : CoreFragment} {witness : Witness}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true) :
    GeneratedContract (.or_d first second) witness true flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (input.mono (by simp_all) (by simp_all) (by simp))
        (facts.retype (fun _ => firstUnit))
        (executed.or_d_left (facts.minimalIfSatisfied firstUnit) facts.truth)

theorem orD_right
    {first second : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.or_d first second)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z
        o := firstMods.o && secondMods.z
        d := secondMods.d
        u := secondMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          apply GeneratedContract.b
          · apply firstInput.combine secondInput
            · intro enabled
              simpa using enabled
            · intro enabled
              right
              simpa using enabled
            · simp
          · exact secondFacts.retype (by simp)
          · simpa using firstExec.or_d_right
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec

private theorem orIInput
    {witness : Witness} {expected : Bool}
    {source firstMods secondMods : CorrectnessModifiers}
    {selector : StackElement}
    (input : GeneratedInput witness expected source)
    (selectorBounded : selector.size ≤ maxScriptElementSize)
    (sourceZero : (firstMods.z && secondMods.z) = true → source.z = true) :
    GeneratedInput (witness.withSelector selector) expected {
      o := firstMods.z && secondMods.z
      d := firstMods.d || secondMods.d
      u := firstMods.u && secondMods.u
    } := by
  apply input.withSelector selectorBounded
  · simp
  · exact sourceZero
  · simp

theorem orILeft_b
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.B, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.B, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (orIInput input trueElement_size_le (by simp_all))
        (facts.retype (by simp_all)) (by simpa using executed.or_i_left)

theorem orIRight_b
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.B, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | b input facts executed =>
      exact .b (orIInput input falseElement_size_le (by simp_all))
        (facts.retype (by simp_all)) (by simpa using executed.or_i_right)

theorem orILeft_k
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.K, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.K, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      apply GeneratedContract.k
        (input := orIInput input trueElement_size_le (by simp_all))
        (ownArgs := trueElement :: ownArgs) (key := key) (signature := signature)
      · simp [stackShape]
      · exact executed.or_i_left
      · exact checked

theorem orIRight_k
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.K, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | k input ownArgs key signature stackShape executed checked =>
      apply GeneratedContract.k
        (input := orIInput input falseElement_size_le (by simp_all))
        (ownArgs := falseElement :: ownArgs) (key := key) (signature := signature)
      · simp [stackShape]
      · exact executed.or_i_right
      · exact checked

theorem orILeft_v
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract first witness expected flags txCtx
      ⟨.V, firstMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector trueElement)
      expected flags txCtx ⟨.V, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | v input expectedTrue executed =>
      exact .v (orIInput input trueElement_size_le (by simp_all)) expectedTrue
        (by simpa using executed.or_i_left)

theorem orIRight_v
    {first second : CoreFragment} {witness : Witness} {expected : Bool}
    {firstMods secondMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (contract : GeneratedContract second witness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.or_i first second) (witness.withSelector falseElement)
      expected flags txCtx ⟨.V, {
        o := firstMods.z && secondMods.z
        d := firstMods.d || secondMods.d
        u := firstMods.u && secondMods.u
      }⟩ := by
  cases contract with
  | v input expectedTrue executed =>
      exact .v (orIInput input falseElement_size_le (by simp_all)) expectedTrue
        (by simpa using executed.or_i_right)

private theorem andorTrueInput
    {firstWitness secondWitness : Witness} {expected : Bool}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness true firstMods)
    (second : GeneratedInput secondWitness expected secondMods) :
    GeneratedInput (Witness.combine firstWitness secondWitness) expected {
      z := firstMods.z && secondMods.z && thirdMods.z
      o := (firstMods.z && secondMods.o && thirdMods.o) ||
        (firstMods.o && secondMods.z && thirdMods.z)
      d := thirdMods.d
      u := secondMods.u && thirdMods.u
    } := by
  apply first.combine second
  · intro enabled
    simp only [Bool.and_eq_true] at enabled
    exact ⟨enabled.1.1, enabled.1.2⟩
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with left | right
    · exact Or.inl ⟨left.1.1, left.1.2⟩
    · exact Or.inr ⟨right.1.1, right.1.2⟩
  · simp

private theorem andorFalseInput
    {firstWitness thirdWitness : Witness} {expected : Bool}
    {firstMods secondMods thirdMods : CorrectnessModifiers}
    (first : GeneratedInput firstWitness false firstMods)
    (third : GeneratedInput thirdWitness expected thirdMods) :
    GeneratedInput (Witness.combine firstWitness thirdWitness) expected {
      z := firstMods.z && secondMods.z && thirdMods.z
      o := (firstMods.z && secondMods.o && thirdMods.o) ||
        (firstMods.o && secondMods.z && thirdMods.z)
      d := thirdMods.d
      u := secondMods.u && thirdMods.u
    } := by
  apply first.combine third
  · intro enabled
    simp only [Bool.and_eq_true] at enabled
    exact ⟨enabled.1.1, enabled.2⟩
  · intro enabled
    simp only [Bool.or_eq_true, Bool.and_eq_true] at enabled
    rcases enabled with left | right
    · exact Or.inl ⟨left.1.1, left.2⟩
    · exact Or.inr ⟨right.1.1, right.2⟩
  · simp

theorem andorTrue_b
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.B, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | b secondInput secondFacts secondExec =>
          exact .b (andorTrueInput firstInput secondInput)
            (secondFacts.retype (by simp_all))
            (by simpa using
              (BExecution.andor_true firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                secondExec))

theorem andorFalse_b
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.B, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.B, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | b thirdInput thirdFacts thirdExec =>
          exact .b (andorFalseInput firstInput thirdInput)
            (thirdFacts.retype (by simp_all))
            (by simpa using
              (BExecution.andor_false firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                thirdExec))

theorem andorTrue_k
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.K, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | k secondInput ownArgs key signature stackShape secondExec checked =>
          apply GeneratedContract.k
            (input := andorTrueInput firstInput secondInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.andor_true
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth secondExec
          · exact checked

theorem andorFalse_k
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.K, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.K, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | k thirdInput ownArgs key signature stackShape thirdExec checked =>
          apply GeneratedContract.k
            (input := andorFalseInput firstInput thirdInput)
            (ownArgs := firstWitness.toInitialStack ++ ownArgs)
            (key := key) (signature := signature)
          · simp [stackShape, List.append_assoc]
          · exact firstExec.andor_false
              (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth thirdExec
          · exact checked

theorem andorTrue_v
    {first second third : CoreFragment} {firstWitness secondWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness true flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (secondContract : GeneratedContract second secondWitness expected flags txCtx
      ⟨.V, secondMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness secondWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases secondContract with
      | v secondInput expectedTrue secondExec =>
          exact .v (andorTrueInput firstInput secondInput) expectedTrue
            (by simpa using
              (VExecution.andor_true firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                secondExec))

theorem andorFalse_v
    {first second third : CoreFragment} {firstWitness thirdWitness : Witness}
    {expected : Bool} {firstMods secondMods thirdMods : CorrectnessModifiers}
    {flags : ScriptFlags} {txCtx : TxContext}
    (firstContract : GeneratedContract first firstWitness false flags txCtx
      ⟨.B, firstMods⟩) (firstUnit : firstMods.u = true)
    (thirdContract : GeneratedContract third thirdWitness expected flags txCtx
      ⟨.V, thirdMods⟩) :
    GeneratedContract (.andor first second third)
      (Witness.combine firstWitness thirdWitness) expected flags txCtx
      ⟨.V, {
        z := firstMods.z && secondMods.z && thirdMods.z
        o := (firstMods.z && secondMods.o && thirdMods.o) ||
          (firstMods.o && secondMods.z && thirdMods.z)
        d := thirdMods.d
        u := secondMods.u && thirdMods.u
      }⟩ := by
  cases firstContract with
  | b firstInput firstFacts firstExec =>
      cases thirdContract with
      | v thirdInput expectedTrue thirdExec =>
          exact .v (andorFalseInput firstInput thirdInput) expectedTrue
            (by simpa using
              (VExecution.andor_false firstExec
                (firstFacts.minimalIfSatisfied firstUnit) firstFacts.truth
                thirdExec))

end GeneratedContract

end LeanMiniscript.Miniscript
