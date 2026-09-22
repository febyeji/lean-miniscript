import LeanMiniscript.Script.Codec.VerificationProofs

namespace LeanMiniscript.Script

local instance codecExecResultDecidableEq : DecidableEq ExecResult := by
  intro first second
  cases first <;> cases second <;>
    simp only [ExecResult.success.injEq, ExecResult.failure.injEq, reduceCtorEq] <;>
    infer_instance

local instance codecExceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := by
  intro first second
  cases first <;> cases second <;>
    simp only [Except.ok.injEq, Except.error.injEq, reduceCtorEq] <;>
    infer_instance

/-! Concrete executions after encoding and decoding, including AST-changing
pushes, conditional error precedence, resource limits and final acceptance. -/

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty,
    sigVersion := .tapscript }

private def oracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)

private def decoded (script : Script) : Option Script := do
  let bytes ← (serializeScript script).toOption
  (deserializeScript bytes).toOption

private def run (script : Script) (stack : Stack := []) : Option ExecResult :=
  (decoded script).map (fun script => evaluate oracle script stack [] {} ctx)

private def runLimited (script : Script) (stack : Stack := [])
    (alt : Stack := []) (weight : Nat := 50) : Option WeightedResult :=
  (decoded script).map (fun script =>
    evaluateWithRuntimeLimits oracle script stack alt {} ctx weight)

private def bytes (size : Nat) : ByteArray := ⟨Array.replicate size 1⟩

private def changingPushes : Script :=
  [.pushData ByteArray.empty, .pushData ⟨#[1]⟩, .pushData ⟨#[16]⟩,
   .pushData ⟨#[0x81]⟩, .pushNum 17, .pushNum 128, .pushNum (-128),
   .pushData ⟨#[0x80]⟩, .pushData ⟨#[0]⟩]

-- Negative zero and a one-byte zero remain byte vectors; numeric pushes retain
-- their sign bytes, and dedicated numeric opcodes recover identical stack data.
example : run changingPushes = some (.success
    [⟨#[0]⟩, ⟨#[0x80]⟩, scriptNum (-128), scriptNum 128, scriptNum 17,
     scriptNum (-1), scriptNum 16, scriptNum 1, ByteArray.empty] []) := by
  native_decide

private def nestedBranches : Script :=
  [.pushData ⟨#[1]⟩, .op .OP_IF,
   .pushData ByteArray.empty, .op .OP_NOTIF, .pushNum 17, .op .OP_ENDIF,
   .op .OP_ELSE, .pushNum 99,
   .op .OP_ELSE, .pushData ⟨#[16]⟩, .op .OP_TOALTSTACK, .op .OP_ENDIF]

example : run nestedBranches = some (.success [scriptNum 17] [scriptNum 16]) := by
  native_decide

example : runLimited nestedBranches =
    some (.success [scriptNum 17] [scriptNum 16] 50) := by
  native_decide

-- An active failure precedes EOF's missing-ENDIF error.
example : run [.pushData ⟨#[1]⟩, .op .OP_IF,
    .pushData ByteArray.empty, .op .OP_VERIFY] = some (.failure .verify) := by
  native_decide

example : run [.pushData ⟨#[1]⟩, .op .OP_IF, .pushNum 17] =
    some (.failure .unbalancedConditional) := by
  native_decide

example : runLimited [.pushData ⟨#[1]⟩, .op .OP_IF,
    .pushData ByteArray.empty, .op .OP_VERIFY] = some (.failure .verify) := by
  native_decide

-- Source-order size checks include inactive branches.
example : runLimited [.pushData ByteArray.empty, .op .OP_IF,
    .pushData (bytes 521), .op .OP_ENDIF, .pushData ⟨#[1]⟩] =
    some (.failure .pushSize) := by
  native_decide

example : runLimited [.pushData ByteArray.empty, .op .OP_IF,
    .pushData (bytes 520), .op .OP_ENDIF, .pushData ⟨#[1]⟩] =
    some (.success [trueElement] [] 50) := by
  native_decide

example : runLimited [.pushData ⟨#[1]⟩, .op .OP_VERIFY]
    (List.replicate 1000 trueElement) = some (.failure .stackSize) := by
  native_decide

-- A one-byte upgradeable public key succeeds after one nonempty-signature debit.
example : runLimited [.pushData ⟨#[1]⟩, .op .OP_CHECKSIG]
    [trueElement] [] 50 = some (.success [trueElement] [] 0) := by
  native_decide

example : runLimited [.pushData ⟨#[1]⟩, .op .OP_CHECKSIG]
    [trueElement] [] 49 = some (.failure .tapscriptValidationWeight) := by
  native_decide

private def witness : TapscriptWitness :=
  { arguments := [], scriptBytes := ⟨#[0x51]⟩, controlBlock := bytes 33 }

-- The recovered pushNum AST still binds to the original pushData's witness.
example : (decoded [.pushData ⟨#[1]⟩]).map (fun script =>
    evaluateTapscript oracle script witness {} ctx) =
    some (.success [trueElement] [] (initialValidationWeight witness.fullWitness)) := by
  native_decide

example : (decoded [.pushData ByteArray.empty]).map (fun script =>
    evaluateTapscript oracle script witness {} ctx) =
    some (.failure .tapscriptWitnessScript) := by
  native_decide

-- Final acceptance keeps the remaining budget and distinguishes false results.
example : (decoded [.pushData ⟨#[1]⟩]).map (fun script =>
    Miniscript.checkTapscriptAcceptance oracle script witness {} ctx) =
    some (.ok (initialValidationWeight witness.fullWitness)) := by
  native_decide

example : (decoded [.pushData ByteArray.empty]).map (fun script =>
    Miniscript.checkTapscriptAcceptance oracle script
      { witness with scriptBytes := ⟨#[0]⟩ } {} ctx) = some (.error .evalFalse) := by
  native_decide

end LeanMiniscript.Script
