import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Extraction.RefInterp

namespace LeanMiniscript.Script

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ⟨#[]⟩, sigVersion := .tapscript }
private def flags : ScriptFlags := {}
private def oracle : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
  (fun _ _ _ => true)
private def key : ByteArray := ⟨Array.replicate 32 2⟩
private def signature : ByteArray := ⟨Array.replicate 64 3⟩
private def unknownKey : ByteArray := ⟨#[2]⟩
private def resultIs (expected : Stack) (weight : Nat) : WeightedResult → Bool
  | .success stack alt remaining => stack = expected && alt = [] && remaining == weight
  | _ => false
private def errorIs (expected : ScriptError) : WeightedResult → Bool
  | .failure error => error == expected
  | _ => false
private def run (script : Script) (stack : Stack) (weight : Nat) : WeightedResult :=
  evaluateWithValidationWeight oracle script stack [] flags ctx weight

example : errorIs .tapscriptMinimalIf
    (evaluateWithValidationWeight oracle
      [.op .OP_IF, .pushNum 1, .op .OP_ENDIF]
      [nonMinimalTruthyElement] [] { flags with minimalIf := false } ctx 0) = true := by
  native_decide

example : Bitcoin.compactSize 252 = [252] := by native_decide
example : Bitcoin.compactSize 253 = [253, 253, 0] := by native_decide
example : Bitcoin.compactSize 65535 = [253, 255, 255] := by native_decide
example : Bitcoin.compactSize 65536 = [254, 0, 0, 1, 0] := by native_decide
example : Bitcoin.compactSize 4294967296 = [255, 0, 0, 0, 0, 1, 0, 0, 0] := by native_decide
example : (Bitcoin.serializeWitness []).data.toList = [0] := by native_decide
example : (Bitcoin.serializeWitness [falseElement, trueElement]).data.toList = [2, 0, 1, 1] := by native_decide
example : (Bitcoin.serializeWitness (List.replicate 253 falseElement)).size = 256 := by native_decide
example : (Bitcoin.serializeWitness [⟨Array.replicate 253 0⟩]).size = 257 := by native_decide

-- Empty signatures and exact budget exhaustion are permitted.
example : resultIs [trueElement] 0 (run [.op .OP_CHECKSIG] [key, signature] 50) = true := by native_decide
example : resultIs [falseElement] 0 (run [.op .OP_CHECKSIG] [key, falseElement] 0) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run [.op .OP_CHECKSIG] [key, signature] 49) = true := by native_decide
-- Unknown public-key versions cost the same amount.
example : resultIs [trueElement] 0 (run [.op .OP_CHECKSIG] [unknownKey, trueElement] 50) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run [.op .OP_CHECKSIG] [unknownKey, trueElement] 49) = true := by native_decide
-- Weight precedes key, size, policy and cryptographic errors.
example : errorIs .tapscriptValidationWeight (run [.op .OP_CHECKSIG] [falseElement, trueElement] 0) = true := by native_decide
example : errorIs .tapscriptEmptyPubkey (run [.op .OP_CHECKSIG] [falseElement, trueElement] 50) = true := by native_decide
example : errorIs .schnorrSigSize (run [.op .OP_CHECKSIG] [key, trueElement] 50) = true := by native_decide
example : errorIs .tapscriptEmptyPubkey (run [.op .OP_CHECKSIG] [falseElement, falseElement] 0) = true := by native_decide
example : errorIs .tapscriptValidationWeight
  (evaluateWithValidationWeight oracle [.op .OP_CHECKSIG] [unknownKey, signature] []
    { flags with discourageUpgradablePubKeyType := true } ctx 0) = true := by native_decide
-- Arity and CHECKSIGADD's four-byte numeric checks precede charging.
example : errorIs .stackUnderflow (run [.op .OP_CHECKSIG] [key] 0) = true := by native_decide
example : errorIs .scriptNumOverflow
  (run [.op .OP_CHECKSIGADD] [key, ⟨#[0, 0, 0, 0, 0]⟩, signature] 0) = true := by native_decide
example : errorIs .scriptNumNonMinimal
  (run [.op .OP_CHECKSIGADD] [key, ⟨#[0]⟩, signature] 0) = true := by native_decide
example : resultIs [scriptNum 2] 0
  (run [.op .OP_CHECKSIGADD] [key, trueElement, signature] 50) = true := by native_decide
example : resultIs [trueElement] 0
  (run [.op .OP_CHECKSIGADD] [key, trueElement, falseElement] 0) = true := by native_decide
-- Legacy execution has no BIP342 debit; unavailable opcodes retain priority.
example : resultIs [falseElement] 0
  (evaluateWithValidationWeight oracle [.op .OP_CHECKSIG] [unknownKey, trueElement] []
    { flags with strictEncoding := false, nullFail := false }
    { ctx with sigVersion := .base } 0) = true := by native_decide
example : errorIs .badOpcode
  (evaluateWithValidationWeight oracle [.op .OP_CHECKSIGADD] [] [] flags
    { ctx with sigVersion := .witnessV0 } 0) = true := by native_decide
-- Consecutive checks share state instead of resetting their budget.
private def twice : Script := [.op .OP_CHECKSIG, .op .OP_TOALTSTACK, .op .OP_CHECKSIG]
example : errorIs .tapscriptValidationWeight
  (run twice [key, signature, key, signature] 99) = true := by native_decide
example : (match run twice [key, signature, key, signature] 100 with
  | .success [top] [saved] 0 => top = trueElement && saved = trueElement
  | _ => false) = true := by native_decide
-- Skipped, nested and duplicate-ELSE branches do not spend validation weight.
example : resultIs [trueElement] 0 (run
  [.op .OP_IF, .op .OP_CHECKSIG, .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF]
  [falseElement] 0) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run
  [.op .OP_IF, .op .OP_CHECKSIG, .op .OP_ENDIF]
  [trueElement, key, signature] 0) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run
  [.op .OP_IF, .op .OP_CHECKSIG] [trueElement, key, signature] 0) = true := by native_decide
example : errorIs .unbalancedConditional (run
  [.op .OP_IF, .pushNum 1] [trueElement] 0) = true := by native_decide

example : resultIs [trueElement] 0 (run
  [.op .OP_IF, .op .OP_IF, .op .OP_CHECKSIG, .op .OP_ENDIF,
    .op .OP_ELSE, .pushNum 1, .op .OP_ENDIF]
  [falseElement] 0) = true := by native_decide
example : errorIs .tapscriptValidationWeight (run
  [.op .OP_IF, .op .OP_CHECKSIG, .op .OP_ELSE, .pushNum 0,
    .op .OP_ELSE, .op .OP_CHECKSIG, .op .OP_ENDIF]
  [trueElement, key, signature, key, signature] 50) = true := by native_decide

private def witness : TapscriptWitness :=
  { arguments := [signature], scriptBytes := ⟨#[32]⟩ ++ key ++ ⟨#[0xac]⟩,
    controlBlock := ⟨Array.replicate 33 0⟩ }
-- Count + (length + signature) + (length + script) + (length + control block).
example : initialValidationWeight witness.fullWitness = 185 := by native_decide
example : resultIs [trueElement] 135
  (evaluateTapscript oracle [.pushData key, .op .OP_CHECKSIG] witness flags ctx) = true := by native_decide
example : initialValidationWeight
  ({ witness with annex := some ⟨#[0x50, 0]⟩ }).fullWitness = 188 := by native_decide
example : errorIs .tapscriptAnnex
  (evaluateTapscript oracle [.pushData key, .op .OP_CHECKSIG]
    { witness with annex := some ⟨#[0]⟩ } flags ctx) = true := by native_decide
example : errorIs .tapscriptWitnessScript
  (evaluateTapscript oracle [.pushNum 1] witness flags ctx) = true := by native_decide
-- Reusing one short signature can actually exhaust a full-witness budget.
private def reused : Script := List.replicate 3 [.op .OP_DUP, .pushData unknownKey,
  .op .OP_CHECKSIG, .op .OP_VERIFY] |>.flatten
private def reusedWitness : TapscriptWitness :=
  { arguments := [trueElement], scriptBytes := ⟨#[0x76, 0x52, 0xac, 0x69,
      0x76, 0x52, 0xac, 0x69, 0x76, 0x52, 0xac, 0x69]⟩,
    controlBlock := ⟨Array.replicate 33 0⟩ }
example : initialValidationWeight reusedWitness.fullWitness = 100 := by native_decide
example : errorIs .tapscriptValidationWeight
  (evaluateTapscript oracle reused reusedWitness flags ctx) = true := by native_decide
example : resultIs [trueElement] 1 (evaluateTapscript oracle reused
  { reusedWitness with annex := some ⟨Array.replicate 50 0x50⟩ } flags ctx) = true := by native_decide

-- Logical checks use the abstract model without assuming any crypto result.
example : WeightedEval [.pushNum 1] [] [] flags ctx 50 (.success [trueElement] [] 50) := by
  exact .step rfl rfl (.pushNum 1 [] [] [] flags ctx _ (.empty _ _ _ _))
    (.empty _ _ _ _ _)
example : WeightedEval [.op .OP_CHECKSIG] [key, signature] [] flags ctx 49
    (.failure .tapscriptValidationWeight) := by
  exact .chargeError rfl (by
    simp [prepareValidationWeight, ctx, debitValidationWeight, signature, validationWeightPerSigop]
    native_decide)
example : LeanMiniscript.Miniscript.TapscriptAccepts [.pushNum 1]
    { arguments := [], scriptBytes := ⟨#[0x51]⟩, controlBlock := ⟨Array.replicate 33 0⟩ }
    flags ctx := by
  refine ⟨rfl, trueElement, [], 87, ?_, by native_decide⟩
  native_decide

end LeanMiniscript.Script
