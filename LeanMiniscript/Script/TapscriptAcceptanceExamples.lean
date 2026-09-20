import LeanMiniscript.Miniscript.Acceptance

namespace LeanMiniscript.Script

open LeanMiniscript.Miniscript

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := by
  intro a b
  cases a <;> cases b
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · rename_i x y
    exact decidable_of_iff (x = y) (by simp)

/-! Boundary regressions for the modeled (no OP_SUCCESSx) Tapscript subset.
Order and Core error tags follow ExecuteWitnessScript at Core commit
9be056a8a72b624dae9623b2f7bded92c2a21c91. These are local regressions, not
additional rows from the external Core differential suite. -/

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ⟨#[]⟩, sigVersion := .tapscript }
private def oracle : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩
private def witness (script : Script) (arguments : List ByteArray) : TapscriptWitness :=
  { arguments := arguments
    scriptBytes := (serializeScript script).toOption.getD ByteArray.empty
    controlBlock := bytes 33 }
private def run (script : Script) (arguments : List ByteArray) : Except ScriptError Nat :=
  checkTapscriptAcceptance oracle script (witness script arguments) {} ctx

-- Boundary values are inclusive. With no opcodes, the initial stack survives.
example : checkTapscriptInitialStack (List.replicate 1000 (bytes 520)) = .ok () := by native_decide
example : run [] [bytes 520] = .ok (initialValidationWeight (witness [] [bytes 520]).fullWitness) := by native_decide
example : run [] [bytes 521] = .error .pushSize := by native_decide
example : run [] (List.replicate 1001 trueElement) = .error .stackSize := by native_decide
-- Count wins over an oversized element; both precede opcode and final errors.
example : run [.pushNum 0, .op .OP_VERIFY] (List.replicate 1001 (bytes 521)) =
    .error .stackSize := by native_decide
example : run [.pushNum 0, .op .OP_VERIFY] [bytes 521] = .error .pushSize := by native_decide
-- Every argument is inspected, including the bottom of the serialized witness.
example : run [] [bytes 521, trueElement] = .error .pushSize := by native_decide
example : run [] [trueElement, bytes 521] = .error .pushSize := by native_decide

-- Metadata is not an argument: a long script, control block and annex do not
-- consume the argument count or incur the initial 520-byte restriction.
private def consumeThousand : Script := List.replicate 1000 (.op .OP_VERIFY) ++ [.pushNum 1]
private def metadataWitness : TapscriptWitness :=
  { witness consumeThousand (List.replicate 1000 trueElement) with
    controlBlock := bytes (33 + 32 * 128)
    annex := some (⟨#[0x50]⟩ ++ bytes 520) }
example : checkTapscriptAcceptance oracle consumeThousand metadataWitness {} ctx =
    .ok (initialValidationWeight metadataWitness.fullWitness) := by native_decide

-- Execution errors precede final checks. CLEANSTACK precedes EVAL_FALSE.
example : run [.op .OP_VERIFY] [falseElement] = .error .verify := by native_decide
example : run [] [] = .error .cleanStack := by native_decide
example : run [] [trueElement, falseElement] = .error .cleanStack := by native_decide
example : run [] [trueElement, trueElement] = .error .cleanStack := by native_decide
example : run [] [falseElement] = .error .evalFalse := by native_decide
example : run [] [⟨#[0x80]⟩] = .error .evalFalse := by native_decide
example : run [] [⟨#[0, 0x80]⟩] = .error .evalFalse := by native_decide
-- Truth is CastToBool, not equality with the canonical one byte.
example : run [] [⟨#[2]⟩] = .ok 88 := by native_decide
-- Only the main stack is subject to the final singleton requirement.
example : run [.pushNum 1, .op .OP_TOALTSTACK, .pushNum 1] [] = .ok 89 := by native_decide

-- Tapscript MINIMALIF is a signature-version rule, independent of the
-- witness-v0 policy flag.
example : checkTapscriptAcceptance oracle [.pushNum 1] (witness [.pushNum 1] [])
    { minimalIf := false } ctx = .ok 87 := by native_decide
example : checkTapscriptAcceptance oracle
    [.op .OP_IF, .pushNum 1, .op .OP_ENDIF]
    (witness [.op .OP_IF, .pushNum 1, .op .OP_ENDIF]
      [nonMinimalTruthyElement])
    { minimalIf := false } ctx = .error .tapscriptMinimalIf := by
  native_decide
example : checkTapscriptAcceptance oracle [.pushNum 1] (witness [.pushNum 1] [])
    { minimalData := false } ctx = .error .tapscriptFlags := by native_decide
-- Metadata and execution-version errors remain distinct from initial limits.
example : checkTapscriptAcceptance oracle [.pushNum 1] (witness [] [bytes 521]) {} ctx =
    .error .tapscriptWitnessScript := by native_decide
example : checkTapscriptAcceptance oracle []
    { witness [] [bytes 521] with annex := some ByteArray.empty } {} ctx =
    .error .tapscriptAnnex := by native_decide
example : checkTapscriptAcceptance oracle [] (witness [] [bytes 521]) {}
    { ctx with sigVersion := .witnessV0 } = .error .badOpcode := by native_decide

end LeanMiniscript.Script
