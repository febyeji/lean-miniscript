import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Extraction.BitcoinCoreFixtures

namespace LeanMiniscript.Script

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ⟨#[]⟩, sigVersion := .tapscript }
private def oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)
private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩
private def run (script : Script) (stack : Stack := []) (alt : Stack := [])
    (weight : Nat := 50) : WeightedResult :=
  evaluateWithRuntimeLimits oracle script stack alt {} ctx weight
private def errorIs (error : ScriptError) : WeightedResult → Bool
  | .failure actual => actual == error
  | _ => false
private def successIs (stack alt : Stack) (weight : Nat) : WeightedResult → Bool
  | .success actual actualAlt remaining => actual = stack && actualAlt = alt && remaining == weight
  | _ => false

-- Active data and numeric pushes use the byte-size boundary, not script size.
example : successIs [bytes 520] [] 50 (run [.pushData (bytes 520)]) = true := by native_decide
example : errorIs .pushSize (run [.pushData (bytes 521)]) = true := by native_decide
example : successIs [scriptNum (2 ^ (8 * 519))] [] 50
    (run [.pushNum (2 ^ (8 * 519))]) = true := by native_decide
example : errorIs .pushSize (run [.pushNum (2 ^ (8 * 520))]) = true := by native_decide

-- The combined count is checked after every opcode, before a later reduction.
private def stack999 := List.replicate 999 trueElement
private def stack1000 := List.replicate 1000 trueElement
example : successIs stack1000 [] 50 (run [.pushNum 1] stack999) = true := by native_decide
example : errorIs .stackSize (run [.pushNum 1, .op .OP_VERIFY] stack1000) = true := by native_decide
example : errorIs .stackSize (run [.op .OP_DUP] stack1000) = true := by native_decide
example : errorIs .stackSize (run [.op .OP_IFDUP] stack1000) = true := by native_decide
example : errorIs .stackSize (run [.op .OP_SIZE] stack1000) = true := by native_decide
example : successIs (falseElement :: stack999) [] 50
    (run [.op .OP_IFDUP] (falseElement :: stack999)) = true := by native_decide
example : errorIs .stackSize (run [.pushNum 1] stack999 [trueElement]) = true := by native_decide
example : successIs stack999 [trueElement] 50
    (run [.op .OP_TOALTSTACK] stack1000) = true := by native_decide
example : successIs stack1000 [] 50
    (run [.op .OP_FROMALTSTACK] stack999 [trueElement]) = true := by native_decide
example : errorIs .pushSize (run [.pushData (bytes 521)] stack1000) = true := by native_decide

-- Both executed and skipped oversized pushes fail when their source is visited.
example : errorIs .pushSize (run
    [.op .OP_IF, .pushData (bytes 521), .op .OP_ENDIF, .pushNum 1]
    [falseElement]) = true := by native_decide
example : successIs [trueElement] [] 50 (run
    [.op .OP_IF, .pushData (bytes 520), .op .OP_ENDIF, .pushNum 1]
    [falseElement]) = true := by native_decide
example : errorIs .pushSize (run
    [.op .OP_IF, .op .OP_IF, .pushData (bytes 521), .op .OP_ENDIF, .op .OP_ENDIF]
    [falseElement]) = true := by native_decide
example : errorIs .pushSize (run
    [.op .OP_IF, .pushNum 1, .op .OP_ELSE, .pushNum 1,
     .op .OP_ELSE, .pushData (bytes 521), .op .OP_ENDIF]
    [falseElement]) = true := by native_decide
example : errorIs .pushSize (run
    [.op .OP_NOTIF, .pushData (bytes 521), .op .OP_ENDIF]
    [trueElement]) = true := by native_decide
example : errorIs .pushSize (run
    [.op .OP_IF, .pushNum (2 ^ (8 * 520)), .op .OP_ENDIF]
    [falseElement]) = true := by native_decide

-- Source-order precedence: no eager scan may hide an earlier execution error.
example : errorIs .verify (run [.pushNum 0, .op .OP_VERIFY, .pushData (bytes 521)]) = true := by native_decide
example : errorIs .verify (run
    [.op .OP_IF, .pushNum 0, .op .OP_VERIFY, .op .OP_ELSE,
     .pushData (bytes 521), .op .OP_ENDIF] [trueElement]) = true := by native_decide
example : errorIs .pushSize (run
    [.op .OP_IF, .pushData (bytes 521), .op .OP_ELSE,
     .pushNum 0, .op .OP_VERIFY, .op .OP_ENDIF] [falseElement]) = true := by native_decide
example : errorIs .tapscriptMinimalIf
    (run [.op .OP_IF, .pushData (bytes 521)] [bytes 2]) = true := by native_decide
example : errorIs .stackUnderflow (run [.op .OP_IF, .pushData (bytes 521)]) = true := by native_decide
example : errorIs .unbalancedConditional (run [.op .OP_ELSE, .pushData (bytes 521)]) = true := by native_decide
example : errorIs .pushSize (run [.op .OP_IF, .pushData (bytes 521)] [falseElement]) = true := by native_decide
example : errorIs .verify (run
    [.op .OP_IF, .pushNum 0, .op .OP_VERIFY, .pushData (bytes 521)] [trueElement]) = true := by native_decide
example : errorIs .unbalancedConditional (run [.op .OP_IF, .pushNum 1] [falseElement]) = true := by native_decide

-- Inactive control flow never consumes values or spends signature weight.
example : successIs [trueElement] [] 0 (run
    [.op .OP_IF, .op .OP_IF, .op .OP_CHECKSIG, .op .OP_ELSE,
     .op .OP_CHECKSIGADD, .op .OP_ENDIF, .op .OP_ENDIF, .pushNum 1]
    [falseElement] [] 0) = true := by native_decide
example : successIs [trueElement, trueElement] [] 50 (run
    [.op .OP_IF, .pushNum 1, .op .OP_ELSE, .pushNum 0,
     .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF] [trueElement]) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run
    [.op .OP_CHECKSIG, .pushData (bytes 521)] [bytes 32, bytes 64] [] 49) = true := by native_decide
example : successIs [trueElement] [] 0 (run [.op .OP_CHECKSIG] [bytes 32, bytes 64] [] 50) = true := by native_decide
example : successIs [falseElement] [] 0 (run [.op .OP_CHECKSIG] [bytes 32, falseElement] [] 0) = true := by native_decide

-- Full-witness acceptance uses the runtime checker; initial limits still win.
private def witness (script : Script) (args : Stack) : TapscriptWitness :=
  { arguments := args, scriptBytes := (serializeScript script).toOption.getD ByteArray.empty,
    controlBlock := bytes 33 }
private def fullRun (script : Script) (args : Stack := []) : WeightedResult :=
  evaluateTapscript oracle script (witness script args) {} ctx
example : errorIs .stackSize (fullRun [.pushNum 1, .op .OP_VERIFY] stack1000) = true := by native_decide
example : errorIs .pushSize (fullRun
    [.op .OP_IF, .pushData (bytes 521), .op .OP_ENDIF] [falseElement]) = true := by native_decide
example : errorIs .stackSize (fullRun [.pushData (bytes 521)]
    (List.replicate 1001 trueElement)) = true := by native_decide

-- Exact source text of the pinned Core PUSH_SIZE rows (the repeated literal
-- is compacted here). These two BASE-mode comparisons supplement, but do not
-- broaden, the conservative core_fixture_audit support classification.
private def corePayload := "'" ++ String.ofList (List.replicate 521 'b') ++ "'"
private def corePushRows : List (String × String) :=
  [("NOP", corePayload), ("0", "IF " ++ corePayload ++ " ENDIF 1")]
private def compareCorePushRow (sources : String × String) : Bool :=
  match LeanMiniscript.Extraction.parseCoreScriptSource sources.1,
      LeanMiniscript.Extraction.parseCoreScriptSource sources.2 with
  | .ok input, .ok output =>
      let baseCtx := { ctx with sigVersion := .base }
      match evaluateWithRuntimeLimits oracle input [] [] {} baseCtx 50 with
      | .failure _ => false
      | .success stack _ weight =>
          match evaluateWithRuntimeLimits oracle output stack [] {} baseCtx weight with
          | .failure error => LeanMiniscript.Extraction.coreScriptErrorTag error == "PUSH_SIZE"
          | _ => false
  | _, _ => false
example : corePushRows.all compareCorePushRow = true := by native_decide

-- Differential traversal regression: every program of up to four instructions
-- over this ten-element alphabet, with four small initial stacks. No resource
-- limit can be reached here, so both control-flow algorithms must agree,
-- including malformed/unclosed conditionals and runtime-error precedence.
private def smallAlphabet : List ScriptElement :=
  [.pushNum 0, .pushNum 1, .op .OP_IF, .op .OP_NOTIF, .op .OP_ELSE,
   .op .OP_ENDIF, .op .OP_VERIFY, .op .OP_DUP,
   .op .OP_TOALTSTACK, .op .OP_FROMALTSTACK]
private def smallPrograms : Nat → List Script
  | 0 => [[]]
  | n + 1 => [] :: smallAlphabet.flatMap (fun head => (smallPrograms n).map (head :: ·))
private def smallStacks : List Stack :=
  [[], [falseElement], [trueElement], [trueElement, falseElement]]
example : (smallPrograms 4).all (fun script => smallStacks.all (fun stack =>
    decide (run script stack =
      evaluateWithValidationWeight oracle script stack [] {} ctx 50))) = true := by native_decide

end LeanMiniscript.Script
