import LeanMiniscript.Extraction.EquivalenceObligations

/-! BASE and witness-v0 operation counting in the typed step and in Core's raw
executor. -/

namespace LeanMiniscript.Script.OperationCountExamples

open LeanMiniscript.Extraction

private def witnessCtx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ⟨#[]⟩, sigVersion := .witnessV0 }
private def tapscriptCtx : TxContext := { witnessCtx with sigVersion := .tapscript }
private def oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)
private def counted (count : Nat) (stack : Stack := []) (conditions : List Bool := []) :
    RuntimeState :=
  { stack := stack, altStack := [], conditions := conditions, weight := 0,
    operationCount := count }
private def countAfter (result : Except ScriptError RuntimeState) : Except ScriptError Nat :=
  result.map RuntimeState.operationCount

-- The 201st operation runs; the 202nd fails before OP_NOP executes.
example : countAfter (runtimeStep oracle (.op .OP_NOP) (counted 200) {} witnessCtx) = .ok 201 := by
  native_decide
example : countAfter (runtimeStep oracle (.op .OP_NOP) (counted 201) {} witnessCtx) =
    .error .opCount := by decide

-- Tapscript has no operation limit, and pushes never count.
example : countAfter (runtimeStep oracle (.op .OP_NOP) (counted 201) {} tapscriptCtx) = .ok 201 := by
  native_decide
example : countAfter (runtimeStep oracle (.pushNum 1) (counted 201) {} witnessCtx) = .ok 201 := by
  native_decide

-- An active multisig adds its key count before reading the rest of its frame:
-- 180 + 1 + 20 keys reaches the missing keys, 181 + 1 + 20 exceeds 201.
example : countAfter (runtimeStep oracle (.op .OP_CHECKMULTISIG) (counted 180 [scriptNum 20]) {}
    witnessCtx) = .error .stackUnderflow := by native_decide
example : countAfter (runtimeStep oracle (.op .OP_CHECKMULTISIG) (counted 181 [scriptNum 20]) {}
    witnessCtx) = .error .opCount := by decide
example : countAfter (runtimeStep oracle (.op .OP_CHECKMULTISIGVERIFY)
    (counted 181 [scriptNum 20]) {} witnessCtx) = .error .opCount := by decide

-- An inactive multisig charges only itself.
example : countAfter (runtimeStep oracle (.op .OP_CHECKMULTISIG)
    (counted 181 [scriptNum 20] [false]) {} witnessCtx) = .ok 182 := by native_decide

-- Whole scripts start at zero: 201 opcodes pass and 202 fail outside Tapscript.
private def nops (count : Nat) : Script := List.replicate count (.op .OP_NOP) ++ [.pushNum 1]
private def run (script : Script) (ctx : TxContext) : WeightedResult :=
  evaluateWithRuntimeLimits oracle script [] [] {} ctx 0
example : run (nops 201) witnessCtx = .success [trueElement] [] 0 := by native_decide
example : run (nops 202) witnessCtx = .failure .opCount := by native_decide
example : run (nops 202) tapscriptCtx = .success [trueElement] [] 0 := by native_decide

-- Core's raw executor gives the same results on the serialized bytes.
private def nopBytes (count : Nat) : ByteArray := ⟨(Array.replicate count 0x61).push 0x51⟩
private def core (count : Nat) : Except CoreVerificationError Stack :=
  executeCoreScript {} witnessCtx (fun _ _ => oracle)
    { scriptBytes := nopBytes count, sigVersion := .witnessV0 }
example : core 201 = .ok [trueElement] := by native_decide
example : core 202 = .error (.script .opCount) := by native_decide

end LeanMiniscript.Script.OperationCountExamples
