import LeanMiniscript.Extraction.TapscriptUnitOutputs

/-! The truth values in a typed threshold execution count to its checked threshold. -/

namespace LeanMiniscript.Extraction.TapscriptWitness

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

variable {sc : ScriptContext}

private theorem decode_false_zero4 {operand : StackElement} {minimal : Bool} {value : Int}
    (decoded : decodeScriptNum operand minimal maxArithmeticScriptNumBytes = .ok value)
    (falsehood : castToBool operand = false) : value = 0 := by
  have bound : operand.size ≤ 4 := by
    by_cases bounded : operand.size ≤ 4
    · exact bounded
    · have large : operand.size > 4 := by omega
      simp [decodeScriptNum, maxArithmeticScriptNumBytes, large] at decoded
  rcases operand with ⟨data⟩
  have repr : (⟨data⟩ : ByteArray) = ⟨data.toList.toArray⟩ := by simp
  generalize bytesEq : data.toList = bytes at repr
  rw [repr] at decoded falsehood bound
  change bytes.length ≤ 4 at bound
  change decodeScriptNum ⟨bytes.toArray⟩ minimal 4 = .ok value at decoded
  rcases bytes with _ | ⟨a, tail⟩
  · simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨b, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    have lastFalse := falsehood
    by_cases lastZero : a = 0
    · subst a
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : a = 128 := lastFalse lastZero
      subst a
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨c, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, lastFalse⟩
    by_cases lastZero : b = 0
    · subst b
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : b = 128 := lastFalse lastZero
      subst b
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨d, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, rfl, lastFalse⟩
    by_cases lastZero : c = 0
    · subst c
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : c = 128 := lastFalse lastZero
      subst c
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  rcases tail with _ | ⟨e, tail⟩
  · simp [castToBool, ByteArray.size, List.zipIdx] at falsehood
    rcases falsehood with ⟨rfl, rfl, rfl, lastFalse⟩
    by_cases lastZero : d = 0
    · subst d
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
    · have lastSign : d = 128 := lastFalse lastZero
      subst d
      cases minimal <;> simpa [decodeScriptNum, ByteArray.size, scriptNumIsMinimal, scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux] using decoded.symm
  simp at bound

theorem decoded_unit_count {value : StackElement} {n : Int} {minimal : Bool}
    (decoded : decodeScriptNum value minimal maxArithmeticScriptNumBytes = .ok n)
    (unit : castToBool value = true → value = trueElement) :
    n = (castToBool value).toNat := by
  cases truth : castToBool value with
  | false => simpa [truth] using decode_false_zero4 decoded truth
  | true =>
    have valueEq := unit truth
    rw [valueEq] at decoded
    have one : decodeScriptNum trueElement minimal maxArithmeticScriptNumBytes = .ok (1 : Int) := by
      exact decodeScriptNum_scriptNat_of_lt (n := 1) (by decide) minimal
    have eq := Except.ok.inj (decoded.symm.trans one)
    simpa [truth] using eq

theorem threshold_rest_member_type {children : List CoreFragment} {types : List MiniType}
    (typed : HasTypeList sc children types) (shape : thresholdRestTypes types) :
    ∀ child ∈ children, ∃ cm, HasType sc child ⟨.W, cm⟩ ∧ cm.d = true ∧ cm.u = true := by
  cases typed with
  | nil => simp
  | @cons first ty children types headTyped tailTyped =>
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · have tyEq : ty = ⟨.W, ty.mods⟩ := by
        cases ty with
        | mk base mods => simp only [thresholdRestTypes] at shape; simp only; rw [shape.1]
      exact ⟨ty.mods, tyEq ▸ headTyped, shape.2.1, shape.2.2.1⟩
    · exact threshold_rest_member_type tailTyped shape.2.2.2 child member
termination_by sizeOf children

private theorem decoded_size {value : StackElement} {n : Int} {minimal : Bool}
    (decoded : decodeScriptNum value minimal maxArithmeticScriptNumBytes = .ok n) :
    value.size ≤ maxScriptElementSize := by
  unfold decodeScriptNum at decoded
  split at decoded
  · contradiction
  · change ¬ value.size > 4 at ‹¬ _›
    change value.size ≤ 520
    omega

private theorem nat_boundary_decode {n : Nat} {value : Int} {minimal : Bool}
    (bound : n ≤ maxArithmeticScriptNatExclusive)
    (decoded : decodeScriptNum (scriptNat n) minimal maxArithmeticScriptNumBytes = .ok value) :
    n < maxArithmeticScriptNatExclusive ∧ value = n := by
  have strict : n < maxArithmeticScriptNatExclusive := by
    by_cases lt : n < maxArithmeticScriptNatExclusive
    · exact lt
    · have eq : n = maxArithmeticScriptNatExclusive := by omega
      subst n
      have oversized : (scriptNat maxArithmeticScriptNatExclusive).size > maxArithmeticScriptNumBytes := by decide
      simp [decodeScriptNum, oversized] at decoded
  exact ⟨strict, Except.ok.inj (decoded.symm.trans (decodeScriptNum_scriptNat_of_lt strict minimal))⟩

theorem TailRunTrace.initial_decode {flags : ScriptFlags} {ctx : TxContext} {alt : Stack}
    {children : List CoreFragment} {acc final : StackElement} {input rest : Stack} {k : Nat}
    (trace : TailRunTrace flags ctx alt children acc input final rest)
    (finalEq : final = scriptNat k) (bound : k < maxArithmeticScriptNatExclusive) :
    ∃ n, decodeScriptNum acc flags.minimalData maxArithmeticScriptNumBytes = .ok n := by
  cases trace with
  | nil => exact ⟨k, finalEq ▸ decodeScriptNum_scriptNat_of_lt bound flags.minimalData⟩
  | cons _ _ a _ _ da _ _ => exact ⟨a, da⟩

/-- Actual truth choices attached to the original indexed execution trace. -/
inductive TailTruths {flags : ScriptFlags} {ctx : TxContext} {alt : Stack} :
    {children : List CoreFragment} → {acc final : StackElement} → {input rest : Stack} →
    TailRunTrace flags ctx alt children acc input final rest → List Bool → Prop where
  | nil (acc : StackElement) (rest : Stack) : TailTruths (.nil acc rest) []
  | cons {child : CoreFragment} {children : List CoreFragment} {acc result final : StackElement}
      {tail rest args : Stack} {order : BaseWOutputOrder} {a b : Int}
      {run : Eval (compile child) (acc :: (args ++ tail)) alt flags ctx (.success (order.outputs acc result ++ tail) alt)}
      {da : decodeScriptNum acc flags.minimalData maxArithmeticScriptNumBytes = .ok a}
      {db : decodeScriptNum result flags.minimalData maxArithmeticScriptNumBytes = .ok b}
      {next : TailRunTrace flags ctx alt children (scriptNum (a + b)) tail final rest} {truths : List Bool}
      (observed : TailTruths next truths) :
      TailTruths (.cons args order a b run da db next) (castToBool result :: truths)

theorem tail_truths_exist {flags : ScriptFlags} {ctx : TxContext} {alt : Stack}
    {children : List CoreFragment} {acc final : StackElement} {input rest : Stack}
    (trace : TailRunTrace flags ctx alt children acc input final rest) : ∃ truths, TailTruths trace truths := by
  induction trace with
  | nil acc rest => exact ⟨[], .nil acc rest⟩
  | cons args order a b run da db next ih =>
    obtain ⟨truths, observed⟩ := ih
    exact ⟨_, .cons (run := run) (da := da) (db := db) observed⟩

private theorem tail_truths_count {env : SatEnv} {flags : ScriptFlags}
    {children : List CoreFragment} {acc final : StackElement} {input rest : Stack}
    {trace : TailRunTrace flags env.txCtx [] children acc input final rest} {truths : List Bool} {k : Nat}
    (observed : TailTruths trace truths) (finalEq : final = scriptNat k)
    (kbound : k < maxArithmeticScriptNatExclusive) (version : ModeledContextVersion sc env.txCtx)
    (units : ∀ child ∈ children, UnitWIn sc child)
    (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (count : Nat) (countBound : count < maxArithmeticScriptNatExclusive)
    (decoded : decodeScriptNum acc flags.minimalData maxArithmeticScriptNumBytes = .ok (count : Int)) :
    count + (truths.map Bool.toNat).sum = k := by
  induction observed generalizing count with
  | nil =>
    rw [finalEq, decodeScriptNum_scriptNat_of_lt kbound flags.minimalData] at decoded
    have eq := Int.ofNat.inj (Except.ok.inj decoded).symm
    simpa using eq
  | @cons child children acc result final tail rest args order a b run da db next truths observed ih =>
    have childBound : ∀ item ∈ acc :: (Witness.toInitialStack args.reverse ++ tail), item.size ≤ maxScriptElementSize := by
      intro item member
      simp only [Witness.toInitialStack, List.reverse_reverse, List.mem_cons] at member
      rcases member with rfl | member
      · exact decoded_size da
      · exact bounded item member
    have unit := units child (by simp) env flags args.reverse acc result tail order version childBound
      (by simpa [Witness.toInitialStack] using run)
    have bEq := decoded_unit_count db unit
    have aEq : a = (count : Int) := Except.ok.inj (da.symm.trans decoded)
    have sumEq : a + b = ((count + (castToBool result).toNat : Nat) : Int) := by
      rw [aEq, bEq]
      simp
    obtain ⟨nextN, nextDecoded⟩ := TailRunTrace.initial_decode next finalEq kbound
    rw [sumEq] at nextDecoded
    have nextLe : count + (castToBool result).toNat ≤ maxArithmeticScriptNatExclusive := by
      cases castToBool result <;> simp <;> omega
    obtain ⟨nextBound, nextEq⟩ := nat_boundary_decode nextLe nextDecoded
    rw [nextEq] at nextDecoded
    have answer := ih finalEq (fun c h => units c (by simp [h]))
      (fun item h => bounded item (List.mem_append_right _ h))
      (count + (castToBool result).toNat) nextBound (by simpa [sumEq] using nextDecoded)
    simpa [List.sum_cons, Nat.add_assoc] using answer

private theorem allWF_member {children : List CoreFragment}
    (wf : CoreFragment.allWellFormed sc children) {child : CoreFragment}
    (member : child ∈ children) : child.WellFormed sc := by
  induction children with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact wf.1
    · exact ih wf.2 member

/-- The B first child and typed W tail normalize their actual decoded outputs
without an execution or witness-equality induction assumption. -/
theorem threshold_trace_truth_count {first : CoreFragment} {children : List CoreFragment}
    {cm : CorrectnessModifiers} {types : List MiniType} {env : SatEnv} {flags : ScriptFlags}
    {firstArgs tailArgs rest : Stack} {value : StackElement} {k : Nat}
    (firstTyped : HasType sc first ⟨.B, cm⟩) (firstUnit : cm.u = true)
    (firstWF : first.WellFormed sc)
    (tailTyped : HasTypeList sc children types) (shape : thresholdRestTypes types)
    (tailWF : CoreFragment.allWellFormed sc children)
    (version : ModeledContextVersion sc env.txCtx) (kbound : k < maxArithmeticScriptNatExclusive)
    (bounded : ∀ item ∈ firstArgs ++ (tailArgs ++ rest), item.size ≤ maxScriptElementSize)
    (firstRun : Eval (compile first) (firstArgs ++ (tailArgs ++ rest)) [] flags env.txCtx
      (.success (value :: (tailArgs ++ rest)) []))
    {trace : TailRunTrace flags env.txCtx [] children value (tailArgs ++ rest) (scriptNat k) rest}
    {truths : List Bool} (observed : TailTruths trace truths) :
    ((castToBool value :: truths).map Bool.toNat).sum = k := by
  obtain ⟨n, decoded⟩ := TailRunTrace.initial_decode trace rfl kbound
  have firstNorm := decoded_unit_count decoded (unitB_of_hasType firstTyped firstWF firstUnit env flags _ _ _ version bounded firstRun)
  rw [firstNorm] at decoded
  have countBound : (castToBool value).toNat < maxArithmeticScriptNatExclusive := by
    cases castToBool value <;> decide
  have units : ∀ child ∈ children, UnitWIn sc child := by
    intro child member
    obtain ⟨wm, wt, _wd, wu⟩ := threshold_rest_member_type tailTyped shape child member
    exact unitW_of_hasType wt (allWF_member tailWF member) wu
  have result := tail_truths_count observed rfl kbound version units
    (fun item h => bounded item (List.mem_append_right _ h)) _ countBound decoded
  simpa using result

/-- A child run keeps its actual truth value and the witness prefix it consumed.
    A W row also keeps its bounded accumulator and the compiler's output order. -/
inductive ExecutedRow (env : SatEnv) (flags : ScriptFlags) (child : CoreFragment)
    (block : Witness) (rest : Stack) (top : StackElement) : BaseType → Prop
  | b (run : Eval (compile child) (block.toInitialStack ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) : ExecutedRow env flags child block rest top .B
  | w (saved : StackElement) (order : BaseWOutputOrder) (size : saved.size ≤ maxScriptElementSize)
      (run : Eval (compile child) (saved :: (block.toInitialStack ++ rest)) [] flags env.txCtx
        (.success (order.outputs saved top ++ rest) [])) : ExecutedRow env flags child block rest top .W

inductive ExecutedRows (env : SatEnv) (flags : ScriptFlags) :
    List BaseType → List CoreFragment → List Bool → List Witness → Prop
  | nil : ExecutedRows env flags [] [] [] []
  | cons {base child block rest top bases children bits blocks}
      (row : ExecutedRow env flags child block rest top base)
      (bounded : ∀ item ∈ block.toInitialStack ++ rest, item.size ≤ maxScriptElementSize)
      (tail : ExecutedRows env flags bases children bits blocks) :
      ExecutedRows env flags (base :: bases) (child :: children) (castToBool top :: bits) (block :: blocks)

private theorem tail_executed_rows {env : SatEnv} {flags : ScriptFlags} {children acc input final rest}
    {trace : TailRunTrace flags env.txCtx [] children acc input final rest} {bits}
    (observed : TailTruths trace bits) (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize) :
    ∃ blocks, ExecutedRows env flags (List.replicate children.length .W) children bits blocks ∧
      input = (blocks.map Witness.toInitialStack).flatten ++ rest := by
  induction observed with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons child children acc result final tail rest args order a b run da db next bits observed ih =>
    obtain ⟨blocks, layout, wire⟩ := ih (fun item h => bounded item (List.mem_append_right _ h))
    refine ⟨args.reverse :: blocks, .cons (.w acc order (decoded_size da)
      (by simpa [Witness.toInitialStack] using run)) (by simpa [Witness.toInitialStack] using bounded) layout, ?_⟩
    simp [Witness.toInitialStack, List.append_assoc, ← wire]

private theorem count_true_eq_sum (bits : List Bool) : bits.count true = (bits.map Bool.toNat).sum := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [ih, Nat.add_comm]

/-- In an accepted threshold execution, exactly k child runs return true. The
    input witness is the concatenation of those actual child frames in wire order. -/
theorem threshold_executed_rows {env : SatEnv} {flags : ScriptFlags} {k children mods consumed rest top}
    (typed : HasType sc (.thresh k children) ⟨.B, mods⟩)
    (wf : (CoreFragment.thresh k children).WellFormed sc)
    (version : ModeledContextVersion sc env.txCtx)
    (bounded : ∀ item ∈ Witness.toInitialStack consumed ++ rest, item.size ≤ maxScriptElementSize)
    (run : Eval (compile (.thresh k children)) (Witness.toInitialStack consumed ++ rest) [] flags env.txCtx
      (.success (top :: rest) [])) (truth : castToBool top = true) :
    ∃ first tail bits blocks, children = first :: tail ∧
      ExecutedRows env flags (.B :: List.replicate tail.length .W) children bits blocks ∧
      bits.count true = k ∧ consumed.toInitialStack = (blocks.map Witness.toInitialStack).flatten := by
  obtain ⟨first, tail, cm, types, firstArgs, tailArgs, value, rfl, ft, fd, fu, tt, ts, wire, rx, trace⟩ :=
    threshold_witness_frame typed wf run truth
  have allBound : ∀ item ∈ firstArgs ++ (tailArgs ++ rest), item.size ≤ maxScriptElementSize := by
    simpa [wire, Witness.toInitialStack, List.append_assoc] using bounded
  obtain ⟨bits, observed⟩ := tail_truths_exist trace
  obtain ⟨blocks, rows, stacked⟩ := tail_executed_rows observed (fun item h => allBound item (List.mem_append_right _ h))
  have tailEq := List.append_cancel_right stacked
  have quota := threshold_trace_truth_count ft fu wf.2.1.1 tt ts wf.2.1.2 version wf.2.2.2 allBound rx observed
  refine ⟨first, tail, _, firstArgs.reverse :: blocks, rfl, .cons (.b (by simpa [Witness.toInitialStack] using rx))
    (by simpa [Witness.toInitialStack] using allBound) rows, (count_true_eq_sum _).trans quota, ?_⟩
  simp [wire, Witness.toInitialStack, tailEq]

end LeanMiniscript.Extraction.TapscriptWitness
