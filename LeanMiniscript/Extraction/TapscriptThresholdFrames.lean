import LeanMiniscript.Miniscript.TypeSoundnessProofs.BaseType
import LeanMiniscript.Miniscript.SatisfactionCandidateProofs

/-! Typed threshold execution frames, in source order, with the operands of
    each compiled addition and the checked terminal threshold. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Miniscript

theorem decode_pair_parts {flags : ScriptFlags} {aBytes bBytes : StackElement} {a b : Int}
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b)) :
    decodeScriptNum aBytes flags.minimalData maxArithmeticScriptNumBytes = .ok a ∧
    decodeScriptNum bBytes flags.minimalData maxArithmeticScriptNumBytes = .ok b := by
  unfold decodeBinaryScriptNums at decoded
  cases da : decodeScriptNum aBytes flags.minimalData maxArithmeticScriptNumBytes <;>
    cases db : decodeScriptNum bBytes flags.minimalData maxArithmeticScriptNumBytes <;>
    simp [da, db, bind, Except.bind, pure, Except.pure] at decoded
  rcases decoded with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem add_single_inv {input alt output outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_ADD] input alt flags ctx (.success output outAlt)) :
    outAlt = alt ∧ ∃ first second rest a b,
      input = first :: second :: rest ∧
      decodeScriptNum first flags.minimalData maxArithmeticScriptNumBytes = .ok a ∧
      decodeScriptNum second flags.minimalData maxArithmeticScriptNumBytes = .ok b ∧
      output = scriptNum (a + b) :: rest := by
  cases run with
  | add first second a b rest script alt flags ctx outcome decoded final =>
    cases final with
    | empty => exact ⟨rfl, first, second, rest, a, b, rfl, (decode_pair_parts decoded).1,
        (decode_pair_parts decoded).2, rfl⟩
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => simp [Opcode.isUpgradeableNop] at upgradable

theorem add_order_inv {saved result : StackElement} {order : BaseWOutputOrder}
    {rest alt output outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.op .OP_ADD] (order.outputs saved result ++ rest) alt flags ctx (.success output outAlt)) :
    outAlt = alt ∧ ∃ a b,
      decodeScriptNum saved flags.minimalData maxArithmeticScriptNumBytes = .ok a ∧
      decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok b ∧
      output = scriptNum (a + b) :: rest := by
  obtain ⟨altEq, first, second, tail, a, b, eq, da, db, out⟩ := add_single_inv run
  cases order <;> simp only [BaseWOutputOrder.outputs, List.cons_append,
    List.nil_append, List.cons.injEq] at eq
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨altEq, a, b, da, db, out⟩
  · rcases eq with ⟨rfl, rfl, rfl⟩
    exact ⟨altEq, b, a, db, da, by simpa [Int.add_comm] using out⟩

/-- Each node retains the actual W child run, its own consumed main-stack
prefix, its output order, and both decoded ADD operands. -/
inductive TailRunTrace (flags : ScriptFlags) (ctx : TxContext) (alt : Stack) :
    List CoreFragment → StackElement → Stack → StackElement → Stack → Prop where
  | nil (acc : StackElement) (rest : Stack) : TailRunTrace flags ctx alt [] acc rest acc rest
  | cons {child : CoreFragment} {children : List CoreFragment}
      {acc result final : StackElement} {tail rest : Stack}
      (args : Stack) (order : BaseWOutputOrder) (a b : Int)
      (run : Eval (compile child) (acc :: (args ++ tail)) alt flags ctx
        (.success (order.outputs acc result ++ tail) alt))
      (decodeAcc : decodeScriptNum acc flags.minimalData maxArithmeticScriptNumBytes = .ok a)
      (decodeChild : decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok b)
      (next : TailRunTrace flags ctx alt children (scriptNum (a + b)) tail final rest) :
      TailRunTrace flags ctx alt (child :: children) acc (args ++ tail) final rest

theorem TailRunTrace.input_frame {flags : ScriptFlags} {ctx : TxContext} {alt : Stack}
    {children : List CoreFragment} {acc final : StackElement} {input rest : Stack}
    (trace : TailRunTrace flags ctx alt children acc input final rest) :
    ∃ args, input = args ++ rest := by
  induction trace with
  | nil => exact ⟨[], rfl⟩
  | cons args _ _ _ _ _ _ _ ih =>
    obtain ⟨tailArgs, rfl⟩ := ih
    exact ⟨args ++ tailArgs, by simp [List.append_assoc]⟩

theorem typed_thresh_tail_inv {children : List CoreFragment} {types : List MiniType}
    (typed : HasTypeList .tapscript children types) (shape : thresholdRestTypes types)
    (wf : CoreFragment.allWellFormed .tapscript children)
    {acc : StackElement} {input alt output outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compileThreshTail children) (acc :: input) alt flags ctx (.success output outAlt)) :
    outAlt = alt ∧ ∃ final rest, output = final :: rest ∧
      TailRunTrace flags ctx alt children acc input final rest := by
  cases typed with
  | nil =>
    have eq := Eval.result_unique run (Eval.done (stack := acc :: input) (altStack := alt))
    cases eq
    exact ⟨rfl, acc, input, rfl, .nil _ _⟩
  | @cons child ty children types headTyped tailTyped =>
    have combined : Eval (compile child ++ ([.op .OP_ADD] ++ compileThreshTail children))
        (acc :: input) alt flags ctx (.success output outAlt) := by
      simpa [compileThreshTail, compileThreshTailWithKeyHash, compile, List.append_assoc] using run
    obtain ⟨beforeAdd, childAlt, childRun, laterRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow child) combined
    obtain ⟨altEq, childEffect⟩ := refinedBaseTypeGuarantee_of_hasType headTyped wf.1 _ _ _ _ _ childRun
    subst childAlt
    have tyEq : ty = ⟨.W, ty.mods⟩ := by
      cases ty with
      | mk base mods => simp only [thresholdRestTypes] at shape; simp only; rw [shape.1]
    rw [tyEq] at childEffect
    obtain ⟨args, tail, saved, result, order, inputEq, outputEq⟩ := childEffect.w_inv
    obtain ⟨rfl, stackEq⟩ := List.cons.inj inputEq
    obtain ⟨afterAdd, addAlt, addRun, restRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (.atom (by simp [NonConditional])) laterRun
    rw [outputEq] at addRun
    obtain ⟨altEq, a, b, da, db, added⟩ := add_order_inv addRun
    subst addAlt
    rw [added] at restRun
    obtain ⟨altEq, final, rest, resultEq, trace⟩ := typed_thresh_tail_inv tailTyped shape.2.2.2 wf.2 restRun
    refine ⟨altEq, final, rest, resultEq, ?_⟩
    rw [stackEq]
    exact .cons args order a b (by rw [stackEq, outputEq] at childRun; exact childRun) da db trace
termination_by sizeOf children

theorem push_equal_truth_inv {k : Nat} {acc top : StackElement}
    {tail rest alt outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx (.success (top :: rest) outAlt))
    (truth : castToBool top = true) :
    acc = scriptNat k ∧ top = trueElement ∧ rest = tail ∧ outAlt = alt := by
  by_cases eq : scriptNum (k : Int) = acc
  · have canonical : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx
        (.success (trueElement :: tail) alt) :=
      Eval.pushNum _ _ _ _ _ _ _ (Eval.equal_true _ _ _ [] _ _ _ _ eq Eval.done)
    obtain ⟨stackEq, altEq⟩ := ExecResult.success.inj (Eval.result_unique run canonical)
    obtain ⟨rfl, rfl⟩ := List.cons.inj stackEq
    exact ⟨eq.symm, rfl, rfl, altEq⟩
  · have canonical : Eval [.pushNum k, .op .OP_EQUAL] (acc :: tail) alt flags ctx
        (.success (falseElement :: tail) alt) :=
      Eval.pushNum _ _ _ _ _ _ _ (Eval.equal_false _ _ _ [] _ _ _ _ eq Eval.done)
    have stackEq := (ExecResult.success.inj (Eval.result_unique run canonical)).1
    have topEq := (List.cons.inj stackEq).1
    rw [topEq] at truth
    simp [castToBool, falseElement] at truth

/-- A complete accepted threshold run retains the first B child and every
W-tail child, the actual ADD decodes, and the terminal byte equality. -/
theorem typed_threshold_run_inv {k : Nat} {children : List CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    {input rest alt outAlt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.thresh k children)) input alt flags ctx (.success (top :: rest) outAlt))
    (truth : castToBool top = true) :
    outAlt = alt ∧ top = trueElement ∧
    ∃ first remaining firstMods types args firstRest value,
      children = first :: remaining ∧
      HasType .tapscript first ⟨.B, firstMods⟩ ∧ firstMods.d = true ∧ firstMods.u = true ∧
      HasTypeList .tapscript remaining types ∧ thresholdRestTypes types ∧
      input = args ++ firstRest ∧
      Eval (compile first) (args ++ firstRest) alt flags ctx (.success (value :: firstRest) alt) ∧
      TailRunTrace flags ctx alt remaining value firstRest (scriptNat k) rest := by
  cases typed with
  | @thresh k first remaining firstMods types firstTyped firstD firstU tailTyped tailShape positive atMost =>
    have combined : Eval (compile first ++ (compileThreshTail remaining ++ [.pushNum k, .op .OP_EQUAL]))
        input alt flags ctx (.success (top :: rest) outAlt) := by
      simpa [compile, compileWithKeyHash, compileThreshWithKeyHash, compileThreshTail, List.append_assoc] using run
    obtain ⟨mid, midAlt, firstRun, tailRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compile_balancedControlFlow first) combined
    obtain ⟨altEq, effect⟩ := refinedBaseTypeGuarantee_of_hasType firstTyped wf.2.1.1 _ _ _ _ _ firstRun
    subst midAlt
    obtain ⟨args, firstRest, value, inputEq, outputEq, _⟩ := effect.b_inv
    obtain ⟨last, lastAlt, addsRun, equalRun⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success (compileThreshTail_balancedControlFlow remaining) tailRun
    rw [outputEq] at addsRun
    obtain ⟨altEq, final, finalRest, finalEq, trace⟩ := typed_thresh_tail_inv tailTyped tailShape wf.2.1.2 addsRun
    subst lastAlt
    rw [finalEq] at equalRun
    obtain ⟨rfl, rfl, rfl, altEq⟩ := push_equal_truth_inv equalRun truth
    refine ⟨altEq, rfl, first, remaining, firstMods, types, args, firstRest, value,
      rfl, firstTyped, firstD, firstU, tailTyped, tailShape, inputEq, ?_, trace⟩
    rw [inputEq, outputEq] at firstRun
    exact firstRun

/-- The trace also records exactly how the whole witness precedes the
preserved suffix, in serialized reverse-runtime order. -/
theorem threshold_witness_frame {k : Nat} {children : List CoreFragment} {mods : CorrectnessModifiers}
    (typed : HasType .tapscript (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript)
    {consumed : Witness} {rest alt : Stack} {top : StackElement} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile (.thresh k children)) (consumed.toInitialStack ++ rest) alt flags ctx
      (.success (top :: rest) alt)) (truth : castToBool top = true) :
    ∃ first remaining firstMods types firstArgs tailArgs value,
      children = first :: remaining ∧
      HasType .tapscript first ⟨.B, firstMods⟩ ∧ firstMods.d = true ∧ firstMods.u = true ∧
      HasTypeList .tapscript remaining types ∧ thresholdRestTypes types ∧
      consumed = tailArgs.reverse ++ firstArgs.reverse ∧
      Eval (compile first) (firstArgs ++ (tailArgs ++ rest)) alt flags ctx
        (.success (value :: (tailArgs ++ rest)) alt) ∧
      TailRunTrace flags ctx alt remaining value (tailArgs ++ rest) (scriptNat k) rest := by
  obtain ⟨_, _, first, remaining, firstMods, types, firstArgs, firstRest, value,
    eq, ft, fd, fu, tt, ts, inputEq, firstRun, trace⟩ := typed_threshold_run_inv typed wf run truth
  obtain ⟨tailArgs, rfl⟩ := trace.input_frame
  have witnessEq : consumed = tailArgs.reverse ++ firstArgs.reverse := by
    have runtimeEq : consumed.toInitialStack = firstArgs ++ tailArgs := by
      apply List.append_cancel_right
      simpa [List.append_assoc] using inputEq
    simpa [Witness.toInitialStack] using congrArg List.reverse runtimeEq
  exact ⟨first, remaining, firstMods, types, firstArgs, tailArgs, value,
    eq, ft, fd, fu, tt, ts, witnessEq, firstRun, trace⟩

theorem threshold_candidate_guard {k : Nat} {children : List CoreFragment}
    (wf : (CoreFragment.thresh k children).WellFormed .tapscript) :
    candidateThresholdValid k children.length := by
  exact ⟨by have := wf.1.1; omega, wf.1.2, ArithmeticScriptNatSafe.of_lt wf.2.2.2⟩


end LeanMiniscript.Extraction.TapscriptWitness
