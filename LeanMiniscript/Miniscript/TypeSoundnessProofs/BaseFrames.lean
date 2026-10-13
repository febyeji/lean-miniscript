import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Type soundness: refined base-type stack frames

The refined B/V/K/W stack-effect relation used by the arbitrary-input
base-type proof, together with its frame-transport lemmas.

Some helper lemmas here were `private` in the former single-file
`TypeSoundnessProofs` module. They are visible only so that sibling
submodules can use them; treat them as internal proof helpers, not stable API.
-/

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
theorem HasType.k_not_z
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
theorem HasType.w_no_zo
    {scriptCtx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
    (typed : HasType scriptCtx fragment ty) (baseEq : ty.base = .W) :
    ty.mods.z = false ∧ ty.mods.o = false := by
  cases typed <;> simp_all [branchBase]

/-- Any nonempty threshold tail starts with a W fragment, so both aggregate
    argument-count modifiers are false. -/
theorem thresholdRestModifiers_noCount
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
theorem compileThreshTail_balancedControlFlow
    (fragments : List CoreFragment) :
    BalancedControlFlow (compileThreshTail fragments) := by
  exact (compileThreshTailWithKeyHash_conforms modelKeyHash fragments).balancedControlFlow

/-- Sequentially consumed argument frames satisfy the modifier formula used by
    `and_v`. -/
theorem ArgumentFrameMatches.afterV
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
theorem RefinedBaseStackEffect.afterV
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
theorem ArgumentFrameMatches.withSelector
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
theorem RefinedBaseStackEffect.withSelector
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
theorem ArgumentFrameMatches.afterProducedSelector
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
theorem RefinedBaseStackEffect.prependArguments
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

end LeanMiniscript.Miniscript
