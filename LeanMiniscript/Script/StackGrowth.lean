import LeanMiniscript.Script.RuntimeErasure
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-- Decoding the variable-size multisignature frame only removes stack items. -/
private theorem decodeCheckMultiSigOperandsFor_rest_length_le
    {flags : ScriptFlags} {ctx : TxContext} {stack : Stack}
    {operands : CheckMultiSigOperands}
    (decoded : decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands) :
    operands.rest.length ≤ stack.length := by
  unfold decodeCheckMultiSigOperandsFor at decoded
  split at decoded
  · contradiction
  · unfold decodeCheckMultiSigOperands at decoded
    split at decoded <;> simp only [bind, Except.bind] at decoded
    · contradiction
    · repeat' (split at decoded <;> try simp only [bind, Except.bind] at decoded)
      all_goals simp_all
      all_goals subst operands
      · exact Nat.zero_le _
      · rename_i _ _ _ keyFrame _ _ _ _ signatureFrame
        have keyLength := congrArg List.length keyFrame
        have signatureLength := congrArg List.length signatureFrame
        simp only [List.length_drop, List.length_cons] at keyLength signatureLength
        dsimp only
        omega

private theorem selectConditionalTail_stackGrowthAllowance
    (script : Script) (depth : Nat) (selected : Bool) (tail : Script)
    (projected : selectConditionalTail depth selected script = some tail) :
    stackGrowthAllowance tail ≤ stackGrowthAllowance script := by
  induction script generalizing depth selected tail with
  | nil => simp [selectConditionalTail] at projected
  | cons element rest ih =>
      have kept (nextDepth : Nat)
          (mapped : (selectConditionalTail nextDepth selected rest).map
            (fun suffix => if selected then element :: suffix else suffix) = some tail) :
          stackGrowthAllowance tail ≤ stackGrowthAllowance (element :: rest) := by
        cases result : selectConditionalTail nextDepth selected rest with
        | none => simp [result] at mapped
        | some suffix =>
            have bound := ih nextDepth selected suffix result
            simp only [result, Option.map_some, Option.some.injEq] at mapped
            subst tail
            cases selected <;> simp [stackGrowthAllowance] at * <;> omega
      cases element with
      | pushData data => exact kept depth projected
      | pushNum number => exact kept depth projected
      | op opcode =>
          cases opcode <;> cases depth <;> simp only [selectConditionalTail] at projected
          all_goals first
          | exact kept _ projected
          | simpa [stackGrowthAllowance, ScriptElement.stackGrowthAllowance] using
              ih _ _ _ projected
          | cases projected; simp [stackGrowthAllowance, ScriptElement.stackGrowthAllowance]

private theorem conditional_select_stackGrowthAllowance
    {script : Script} {frame : ConditionalFrame}
    (split : splitConditional script = some frame) (selected : Bool) :
    stackGrowthAllowance (frame.select selected) ≤ stackGrowthAllowance script := by
  apply selectConditionalTail_stackGrowthAllowance script 0 selected (frame.select selected)
  simp [selectConditionalTail_eq, split]

/-- Successful execution grows the combined main/alt stack by at most the sum
    of source opcode allowances. This holds for every modeled Script,
    independently of typing, initial stack bounds, and cryptographic results. -/
theorem Eval.stackGrowth_le_allowance
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval script stack alt flags ctx (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + stackGrowthAllowance script := by
  generalize resultEq : ExecResult.success finalStack finalAlt = result at evaluated
  induction evaluated
  case if_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  case notif_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  all_goals cases resultEq
  all_goals simp_all only [List.length_cons, true_implies,
    stackGrowthAllowance, ScriptElement.stackGrowthAllowance]
  all_goals try omega
  case roll.refl =>
    rename_i operand top index rest alt script flags ctx decoded tail ih
    have removed := List.length_eraseIdx_le (top :: rest) index
    simp only [List.length_cons] at removed
    omega
  case checkmultisig_success.refl =>
    rename_i stack operands script alt flags ctx decoded checked dummy tail ih
    have remaining := decodeCheckMultiSigOperandsFor_rest_length_le decoded
    omega
  case checkmultisigverify_success.refl =>
    rename_i stack operands script alt flags ctx decoded checked dummy tail ih
    have remaining := decodeCheckMultiSigOperandsFor_rest_length_le decoded
    omega
  case checkmultisig_failure.refl =>
    rename_i stack operands script alt flags ctx decoded checked nullfail dummy tail ih
    have remaining := decodeCheckMultiSigOperandsFor_rest_length_le decoded
    omega
  case if_execute.refl =>
    rename_i top rest alt script frame flags ctx split minimal tail ih
    have shorter := conditional_select_stackGrowthAllowance split (castToBool top)
    omega
  case notif_execute.refl =>
    rename_i top rest alt script frame flags ctx split minimal tail ih
    have shorter := conditional_select_stackGrowthAllowance split (!castToBool top)
    omega

/-- The instruction-count bound follows when every source element has a
    one-item allowance. -/
theorem Eval.stackGrowth
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval script stack alt flags ctx (.success finalStack finalAlt))
    (oneItem : OneItemGrowth script) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length := by
  have growth := evaluated.stackGrowth_le_allowance
  have bound := stackGrowthAllowance_le_length script oneItem
  omega

/-- Source-order success inherits the opcode-weighted bound through erasure. -/
theorem RuntimeEval.stackGrowth_le_allowance
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (evaluated : RuntimeEval script
      { stack := stack, altStack := alt, weight := weight } flags ctx
      (.success finalStack finalAlt finalWeight)) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + stackGrowthAllowance script :=
  evaluated.erase_success.stackGrowth_le_allowance

/-- Executable runtime success satisfies the weighted bound under the existing
    oracle refinement contract. -/
theorem evaluateWithRuntimeLimits_stackGrowth_le_allowance
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + stackGrowthAllowance script :=
  (evaluateWithRuntimeLimits_eval_success agreement success).stackGrowth_le_allowance

/-- Source-order success inherits the instruction-count bound when source
    elements have one-item allowances, starting with no open conditional. -/
theorem RuntimeEval.stackGrowth
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (evaluated : RuntimeEval script
      { stack := stack, altStack := alt, weight := weight } flags ctx
      (.success finalStack finalAlt finalWeight))
    (oneItem : OneItemGrowth script) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length :=
  evaluated.erase_success.stackGrowth oneItem

/-- Executable runtime success satisfies the instruction-count bound for
    one-item source elements when the oracle refines the model. This does not assert that execution
    succeeds or that intermediate stacks stay below this final-state bound. -/
theorem evaluateWithRuntimeLimits_stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight)
    (oneItem : OneItemGrowth script) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length :=
  (evaluateWithRuntimeLimits_eval_success agreement success).stackGrowth oneItem

end LeanMiniscript.Script
