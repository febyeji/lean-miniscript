/-
  LeanMiniscript.Script.BigStep
  ==========================
  Big-step evaluation semantics for Bitcoin Script.

  Defines `Eval : Script → Stack → ScriptFlags → TxContext → ExecResult → Prop`
  as an inductive relation for reasoning about script execution.

  References:
  - Atzei et al. (FC 2018) used a similar big-step/denotational approach
  - See also: docs/decisions/02-semantics-style.md
-/

import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-- Big-step evaluation relation.
    `Eval script stack flags ctx result` means executing `script` starting
    with `stack` in context `ctx` produces `result`. -/
inductive Eval : Script → Stack → ScriptFlags → TxContext → ExecResult → Prop where
  -- Base case
  | empty : (stack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      Eval [] stack flags ctx (.success stack)

  -- Data push
  | pushData : (data : StackElement) → (rest : Script) → (stack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval rest (data :: stack) flags ctx result →
      Eval (.pushData data :: rest) stack flags ctx result

  | pushNum : (n : Int) → (numBytes : StackElement) → (rest : Script) →
      (stack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval rest (numBytes :: stack) flags ctx result →
      Eval (.pushNum n :: rest) stack flags ctx result

  -- OP_CHECKSIG: pubkey on top, sig below (Bitcoin Core convention)
  | checksig_success : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = true →
      Eval script (trueElement :: rest) flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) flags ctx result

  | checksig_failure : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = false →
      Eval script (falseElement :: rest) flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) flags ctx result

  -- OP_EQUAL
  | equal_true : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      a = b →
      Eval script (trueElement :: rest) flags ctx result →
      Eval (.op .OP_EQUAL :: script) (a :: b :: rest) flags ctx result

  | equal_false : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      a ≠ b →
      Eval script (falseElement :: rest) flags ctx result →
      Eval (.op .OP_EQUAL :: script) (a :: b :: rest) flags ctx result

  -- OP_EQUALVERIFY
  | equalverify_success : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      a = b →
      Eval script rest flags ctx result →
      Eval (.op .OP_EQUALVERIFY :: script) (a :: b :: rest) flags ctx result

  | equalverify_failure : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      a ≠ b →
      Eval (.op .OP_EQUALVERIFY :: script) (a :: b :: rest) flags ctx
        (.failure "EQUALVERIFY failed")

  -- OP_VERIFY
  | verify_success : (top : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      castToBool top = true →
      Eval script rest flags ctx result →
      Eval (.op .OP_VERIFY :: script) (top :: rest) flags ctx result

  | verify_failure : (top : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      castToBool top = false →
      Eval (.op .OP_VERIFY :: script) (top :: rest) flags ctx
        (.failure "VERIFY failed")

  -- OP_DUP
  | dup : (x : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (x :: x :: rest) flags ctx result →
      Eval (.op .OP_DUP :: script) (x :: rest) flags ctx result

  -- OP_HASH160
  | op_hash160 : (x : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (hash160 x :: rest) flags ctx result →
      Eval (.op .OP_HASH160 :: script) (x :: rest) flags ctx result

  -- OP_BOOLOR
  | boolor : (a b : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (boolToElement (castToBool a || castToBool b) :: rest)
        flags ctx result →
      Eval (.op .OP_BOOLOR :: script) (a :: b :: rest) flags ctx result

  -- OP_BOOLAND
  | booland : (a b : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (boolToElement (castToBool a && castToBool b) :: rest)
        flags ctx result →
      Eval (.op .OP_BOOLAND :: script) (a :: b :: rest) flags ctx result

  -- OP_IF/OP_ELSE/OP_ENDIF (structural model for compiled Miniscript)
  | if_true : (top : StackElement) → (rest : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool top = true →
      Eval (thenBranch ++ after) rest flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) flags ctx result

  | if_false : (top : StackElement) → (rest : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool top = false →
      Eval (elseBranch ++ after) rest flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) flags ctx result

  -- OP_SWAP
  | swap : (a b : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (b :: a :: rest) flags ctx result →
      Eval (.op .OP_SWAP :: script) (a :: b :: rest) flags ctx result

  -- OP_0NOTEQUAL
  | zeroNotEqual : (x : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (boolToElement (castToBool x) :: rest) flags ctx result →
      Eval (.op .OP_0NOTEQUAL :: script) (x :: rest) flags ctx result

  -- OP_IFDUP
  | ifdup_true : (x : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool x = true →
      Eval script (x :: x :: rest) flags ctx result →
      Eval (.op .OP_IFDUP :: script) (x :: rest) flags ctx result

  | ifdup_false : (x : StackElement) → (rest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool x = false →
      Eval script (x :: rest) flags ctx result →
      Eval (.op .OP_IFDUP :: script) (x :: rest) flags ctx result

  -- OP_SIZE
  | size : (x : StackElement) → (sizeBytes : StackElement) → (rest : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (sizeBytes :: x :: rest) flags ctx result →
      Eval (.op .OP_SIZE :: script) (x :: rest) flags ctx result

  -- Sequential composition
  | seq : (s1 s2 : Script) → (stack : Stack) → (midStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval s1 stack flags ctx (.success midStack) →
      Eval s2 midStack flags ctx result →
      Eval (s1 ++ s2) stack flags ctx result

end LeanMiniscript.Script
