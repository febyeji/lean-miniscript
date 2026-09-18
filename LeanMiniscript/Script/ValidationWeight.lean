import LeanMiniscript.Script.RuntimeLimits

namespace LeanMiniscript.Script

/-- Script-path material, with witness arguments in wire (bottom-first) order.
    Annex, when present, must begin with 0x50. This type does not validate the
    control-block commitment to the spent Taproot output. -/
structure TapscriptWitness where
  arguments : List ByteArray
  scriptBytes : ByteArray
  controlBlock : ByteArray
  annex : Option ByteArray := none
  deriving Repr

def TapscriptWitness.fullWitness (witness : TapscriptWitness) : List ByteArray :=
  witness.arguments ++ [witness.scriptBytes, witness.controlBlock] ++ witness.annex.toList

/-- Initial Tapscript limits apply only to arguments, after script/control and
    annex removal. Count precedes element size, as in Core's ExecuteWitnessScript.
    OP_SUCCESSx is outside the modeled AST, so no success bypass is represented. -/
def checkTapscriptInitialStack (arguments : List ByteArray) : Except ScriptError Unit :=
  if arguments.length > maxStackSize then .error .stackSize
  else if arguments.any (fun item => item.size > maxScriptElementSize) then .error .pushSize
  else .ok ()

theorem checkTapscriptInitialStack_ok_iff (arguments : List ByteArray) :
    checkTapscriptInitialStack arguments = .ok () ↔
      arguments.length ≤ maxStackSize ∧
        ∀ item ∈ arguments, item.size ≤ maxScriptElementSize := by
  unfold checkTapscriptInitialStack
  split
  · rename_i tooMany
    simp [Nat.not_le.mpr tooMany]
  · simp_all [List.any_eq_true, Nat.not_lt]

/-- Bind parsed script-path metadata, check initial arguments, then execute in
    source order with signature weight, runtime stack and push-size limits. -/
def evaluateTapscript (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    WeightedResult :=
  if ctx.sigVersion ≠ .tapscript then .failure .badOpcode
  else if !(match serializeScript script with
    | .ok bytes => bytes.data == witness.scriptBytes.data
    | .error _ => false) then .failure .tapscriptWitnessScript
  else if witness.annex.any (fun bytes => bytes.size == 0 || bytes[0]! != 0x50) then
    .failure .tapscriptAnnex
  else
    match checkTapscriptInitialStack witness.arguments with
    | .error error => .failure error
    | .ok () =>
      match ctx.taproot with
      | none => evaluateWithRuntimeLimits oracle script witness.arguments.reverse [] flags ctx
            (initialValidationWeight witness.fullWitness)
      | some hashContext =>
          -- The full witness supplies annex and leaf bytes, not caller hints.
          -- The modeled AST has no CODESEPARATOR, so none has executed.
          let bound := { hashContext with
            annex := witness.annex
            spendPath := .scriptPath witness.scriptBytes 0xc0 4294967295 }
          match TxContext.fromTaproot bound .tapscript with
          | .error _ => .failure .schnorrSigHashType
          | .ok signingCtx => evaluateWithRuntimeLimits oracle script
              witness.arguments.reverse [] flags signingCtx
              (initialValidationWeight witness.fullWitness)

/-- Successful full-witness execution certifies both initial argument limits. -/
theorem evaluateTapscript_initialStack
    {oracle : CryptoOracle} {script : Script} {witness : TapscriptWitness}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (success : evaluateTapscript oracle script witness flags ctx = .success stack alt weight) :
    witness.arguments.length ≤ maxStackSize ∧
      ∀ item ∈ witness.arguments, item.size ≤ maxScriptElementSize := by
  apply (checkTapscriptInitialStack_ok_iff witness.arguments).mp
  cases checked : checkTapscriptInitialStack witness.arguments with
  | ok value => cases value; rfl
  | error error =>
      simp only [evaluateTapscript, checked] at success
      repeat' first | contradiction | split at success

/-- Successful full-witness execution respects the final combined stack bound
    and every source push's size, independently of the cryptographic oracle. -/
theorem evaluateTapscript_runtimeBounds
    {oracle : CryptoOracle} {script : Script} {witness : TapscriptWitness}
    {flags : ScriptFlags} {ctx : TxContext} {stack alt : Stack} {weight : Nat}
    (success : evaluateTapscript oracle script witness flags ctx = .success stack alt weight) :
    stack.length + alt.length ≤ maxStackSize ∧
      ∀ element ∈ script, element.pushSize ≤ maxScriptElementSize := by
  have initial : witness.arguments.reverse.length + ([] : Stack).length ≤ maxStackSize := by
    simpa using (evaluateTapscript_initialStack success).1
  unfold evaluateTapscript at success
  repeat' first
    | contradiction
    | exact evaluateWithRuntimeLimits_bounds initial success
    | split at success
  all_goals dsimp only at success
  all_goals repeat' first
    | contradiction
    | exact evaluateWithRuntimeLimits_bounds initial success
    | split at success

/-- Full-witness metadata binding and transaction-derived hashing preserve
    oracle refinement at the Tapscript execution entry point. -/
theorem evaluateTapscript_eq_model
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    evaluateTapscript oracle script witness flags ctx =
      evaluateTapscript CryptoOracle.model script witness flags ctx := by
  have compute (script : Script) (stack alt : Stack) (flags : ScriptFlags)
      (ctx : TxContext) (weight : Nat) :
      evaluateWithRuntimeLimits oracle script stack alt flags ctx weight =
        evaluateWithRuntimeLimits CryptoOracle.model script stack alt flags ctx weight :=
    evaluateWithRuntimeLimits_eq_model agreement script stack alt flags ctx weight
  unfold evaluateTapscript
  repeat' first | rfl | split
  all_goals try dsimp only
  all_goals repeat' first | rfl | split
  all_goals apply compute

end LeanMiniscript.Script
