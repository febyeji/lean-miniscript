import LeanMiniscript.Script.RuntimeErasure

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

/-- Successful execution grows the combined main/alt stack by at most one
    item per source instruction. This bound holds for every modeled Script,
    independently of typing, initial stack bounds, and cryptographic results. -/
theorem Eval.stackGrowth
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval script stack alt flags ctx (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length := by
  generalize resultEq : ExecResult.success finalStack finalAlt = result at evaluated
  induction evaluated
  case if_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  case notif_unbalanced =>
    rename_i top rest alt script flags ctx selectedResult split minimal selected ih
    cases selectedResult <;> simp_all [finishUnclosedConditional]
  all_goals cases resultEq
  all_goals simp_all only [List.length_cons, List.length_nil, true_implies]
  all_goals try omega
  case checkmultisig_success.refl =>
    rename_i stack operands script alt flags ctx decoded checked dummy tail ih
    have remaining := decodeCheckMultiSigOperandsFor_rest_length_le decoded
    omega
  case checkmultisig_failure.refl =>
    rename_i stack operands script alt flags ctx decoded checked nullfail dummy tail ih
    have remaining := decodeCheckMultiSigOperandsFor_rest_length_le decoded
    omega
  case if_execute.refl =>
    rename_i top rest alt script frame flags ctx split minimal tail ih
    have shorter := ConditionalFrame.select_length_lt split (castToBool top)
    omega
  case notif_execute.refl =>
    rename_i top rest alt script frame flags ctx split minimal tail ih
    have shorter := ConditionalFrame.select_length_lt split (!castToBool top)
    omega

/-- The source-order model inherits the same growth bound through success
    erasure, starting with no open conditional. -/
theorem RuntimeEval.stackGrowth
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (evaluated : RuntimeEval script
      { stack := stack, altStack := alt, weight := weight } flags ctx
      (.success finalStack finalAlt finalWeight)) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length :=
  evaluated.erase_success.stackGrowth

/-- Executable runtime success satisfies the growth bound whenever the oracle
    agrees with the abstract semantics. This does not assert that execution
    succeeds or that intermediate stacks stay below this final-state bound. -/
theorem evaluateWithRuntimeLimits_stackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (success : evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
      .success finalStack finalAlt finalWeight) :
    finalStack.length + finalAlt.length ≤ stack.length + alt.length + script.length :=
  (evaluateWithRuntimeLimits_eval_success agreement success).stackGrowth

end LeanMiniscript.Script
