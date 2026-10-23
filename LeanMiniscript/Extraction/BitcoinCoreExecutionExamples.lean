import LeanMiniscript.Extraction.BitcoinCoreExecutionProofs

namespace LeanMiniscript.Extraction.BitcoinCoreExecutionExamples

open LeanMiniscript.Script LeanMiniscript.Miniscript

private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩

private def flags : CoreVerificationFlags :=
  { checkLockTimeVerify := true, checkSequenceVerify := true }

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty }

-- These callbacks isolate execution and budget behavior from cryptography.
private def oracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)

private def encoded (script : Script) : ByteArray :=
  (serializeScript script).toOption.getD ByteArray.empty

private def request (script : Script) (stack : Stack) (weight : Nat) : CoreScriptExecutionRequest :=
  { scriptBytes := encoded script, stack := stack, validationWeight := weight,
    sigVersion := .tapscript }

private def raw (script : Script) (stack : Stack := []) (weight : Nat := 50)
    (verificationFlags : CoreVerificationFlags := flags) : Except CoreVerificationError Stack :=
  executeCoreScript verificationFlags ctx (fun _ _ => oracle) (request script stack weight)

private def typed (script : Script) (stack : Stack := []) (weight : Nat := 50) :
    Except CoreVerificationError Stack :=
  coreRuntimeResult (evaluateWithRuntimeLimits oracle script stack [] flags.script
    (coreTapscriptContext ctx (request script stack weight)) weight)

private def conditional : Script :=
  compileConcrete (.or_i (.c (.pk_k (.ofBytes (bytes 32)))) .one)

-- Compilation, conditional execution, signature failure order and an inactive
-- signature branch exercise both sides of the new equality boundary.
example : CoreTapscriptEncoding (encoded conditional) 0 conditional := by native_decide

example : raw conditional [trueElement, bytes 64] 50 = .ok [trueElement] ∧
    typed conditional [trueElement, bytes 64] 50 = .ok [trueElement] ∧
    raw conditional [trueElement, bytes 64] 49 = .error (.script .tapscriptValidationWeight) ∧
    typed conditional [trueElement, bytes 64] 49 = .error (.script .tapscriptValidationWeight) ∧
    raw conditional [ByteArray.empty] 0 = .ok [trueElement] ∧
    typed conditional [ByteArray.empty] 0 = .ok [trueElement] := by native_decide

private def pushes : Script :=
  [.pushData ByteArray.empty, .pushData ⟨#[1]⟩, .pushData ⟨#[16]⟩,
   .pushData ⟨#[0x81]⟩, .pushData ⟨#[0]⟩, .pushData ⟨#[0x80]⟩,
   .pushNum 17, .pushNum 128, .pushNum (-128), .pushData (bytes 75)]

example : CoreTapscriptEncoding (encoded pushes) 0 pushes ∧ raw pushes = typed pushes := by
  native_decide

-- The certificate detects nonminimal encodings, truncation, trailing bytes
-- and opcodes outside the typed AST before any execution is considered.
example : ¬ CoreTapscriptEncoding ⟨#[0x4c, 1, 1]⟩ 0 [.pushData ⟨#[1]⟩] ∧
    ¬ CoreTapscriptEncoding ⟨#[2, 1]⟩ 0 [.pushData ⟨#[1]⟩] ∧
    ¬ CoreTapscriptEncoding ⟨#[0x51, 0x51]⟩ 0 [.pushNum 1] ∧
    ¬ CoreTapscriptEncoding ⟨#[0xab]⟩ 0 [.op .OP_NOP] ∧
    ¬ CoreTapscriptEncoding ⟨#[0x50]⟩ 0 [.op .OP_NOP] := by native_decide

private def oversized : Script :=
  [.pushNum 0, .op .OP_IF, .pushData (bytes 521), .op .OP_ENDIF]

-- The general certificate supports PUSHDATA2, including a push that fails
-- the runtime size limit even inside an inactive branch.
example : CoreTapscriptEncoding (encoded oversized) 0 oversized ∧
    raw oversized = .error (.script .pushSize) ∧
    typed oversized = .error (.script .pushSize) := by native_decide

example : raw [.pushNum 1] (List.replicate 1000 trueElement) = .error (.script .stackSize) ∧
    typed [.pushNum 1] (List.replicate 1000 trueElement) = .error (.script .stackSize) ∧
    raw [.pushNum 1, .op .OP_IF] = .error (.script .unbalancedConditional) ∧
    typed [.pushNum 1, .op .OP_IF] = .error (.script .unbalancedConditional) := by native_decide

-- Tapscript omits the legacy 201-operation limit.
example : raw (.pushNum 1 :: List.replicate 202 (.op .OP_NOP)) = .ok [trueElement] ∧
    typed (.pushNum 1 :: List.replicate 202 (.op .OP_NOP)) = .ok [trueElement] := by native_decide

-- Timelock activation is a necessary premise: the raw executor can treat
-- disabled CLTV as a NOP, while the typed runtime always checks it.
example : raw [.pushNum 1, .op .OP_CHECKLOCKTIMEVERIFY] [] 50
      { flags with checkLockTimeVerify := false } = .ok [trueElement] ∧
    typed [.pushNum 1, .op .OP_CHECKLOCKTIMEVERIFY] = .error (.script .checkLockTimeVerify) := by
  native_decide

end LeanMiniscript.Extraction.BitcoinCoreExecutionExamples
