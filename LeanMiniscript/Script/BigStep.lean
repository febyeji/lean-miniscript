/-
  LeanMiniscript.Script.BigStep
  ==========================
  Big-step evaluation semantics for Bitcoin Script.

  Defines `Eval : Script -> Stack -> Stack -> ScriptFlags -> TxContext ->
  ExecResult -> Prop` as an inductive relation for reasoning about script
  execution. The two stack arguments are the main stack and alt stack.

  References:
  - Atzei et al. (FC 2018) used a similar big-step/denotational approach
  - See also: docs/decisions/02-semantics-style.md
-/

import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

/-- Big-step evaluation relation.
    `Eval script stack altStack flags ctx result` means executing `script`
    starting with main stack `stack` and alternate stack `altStack` in context
    `ctx` produces `result`. -/
inductive Eval : Script → Stack → Stack → ScriptFlags → TxContext → ExecResult → Prop where
  -- Base case
  | empty : (stack altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      Eval [] stack altStack flags ctx (.success stack altStack)

  -- Data push
  | pushData : (data : StackElement) → (rest : Script) →
      (stack altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval rest (data :: stack) altStack flags ctx result →
      Eval (.pushData data :: rest) stack altStack flags ctx result

  | pushNum : (n : Int) → (rest : Script) →
      (stack altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval rest (scriptNum n :: stack) altStack flags ctx result →
      Eval (.pushNum n :: rest) stack altStack flags ctx result

  -- OP_CHECKSIG: pubkey on top, sig below (Bitcoin Core convention)
  | checksig_success : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = true →
      Eval script (trueElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result

  | checksig_failure : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = false →
      Eval script (falseElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result

  -- OP_EQUAL
  | equal_true : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      a = b →
      Eval script (trueElement :: rest) altStack flags ctx result →
      Eval (.op .OP_EQUAL :: script) (a :: b :: rest) altStack flags ctx result

  | equal_false : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      a ≠ b →
      Eval script (falseElement :: rest) altStack flags ctx result →
      Eval (.op .OP_EQUAL :: script) (a :: b :: rest) altStack flags ctx result

  -- OP_EQUALVERIFY
  | equalverify_success : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      a = b →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_EQUALVERIFY :: script) (a :: b :: rest) altStack flags ctx result

  | equalverify_failure : (a b : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      a ≠ b →
      Eval (.op .OP_EQUALVERIFY :: script) (a :: b :: rest) altStack flags ctx
        (.failure "EQUALVERIFY failed")

  -- OP_VERIFY
  | verify_success : (top : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      castToBool top = true →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx result

  | verify_failure : (top : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      castToBool top = false →
      Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx
        (.failure "VERIFY failed")

  -- OP_CHECKSEQUENCEVERIFY
  | checksequenceverify_success : (n : Nat) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      sequenceSatisfied n ctx →
      Eval script (scriptNat n :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSEQUENCEVERIFY :: script) (scriptNat n :: rest)
        altStack flags ctx result

  | checksequenceverify_failure : (n : Nat) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      ¬ sequenceSatisfied n ctx →
      Eval (.op .OP_CHECKSEQUENCEVERIFY :: script) (scriptNat n :: rest)
        altStack flags ctx (.failure "CHECKSEQUENCEVERIFY failed")

  -- OP_CHECKLOCKTIMEVERIFY
  | checklocktimeverify_success : (n : Nat) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      locktimeSatisfied n ctx →
      Eval script (scriptNat n :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script) (scriptNat n :: rest)
        altStack flags ctx result

  | checklocktimeverify_failure : (n : Nat) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      ¬ locktimeSatisfied n ctx →
      Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script) (scriptNat n :: rest)
        altStack flags ctx (.failure "CHECKLOCKTIMEVERIFY failed")

  -- OP_DUP
  | dup : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (x :: x :: rest) altStack flags ctx result →
      Eval (.op .OP_DUP :: script) (x :: rest) altStack flags ctx result

  -- OP_SHA256
  | op_sha256 : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (sha256 x :: rest) altStack flags ctx result →
      Eval (.op .OP_SHA256 :: script) (x :: rest) altStack flags ctx result

  -- OP_HASH256
  | op_hash256 : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (hash256 x :: rest) altStack flags ctx result →
      Eval (.op .OP_HASH256 :: script) (x :: rest) altStack flags ctx result

  -- OP_RIPEMD160
  | op_ripemd160 : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (ripemd160 x :: rest) altStack flags ctx result →
      Eval (.op .OP_RIPEMD160 :: script) (x :: rest) altStack flags ctx result

  -- OP_HASH160
  | op_hash160 : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (hash160 x :: rest) altStack flags ctx result →
      Eval (.op .OP_HASH160 :: script) (x :: rest) altStack flags ctx result

  -- OP_BOOLOR
  | boolor : (a b : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (boolToElement (castToBool a || castToBool b) :: rest)
        altStack flags ctx result →
      Eval (.op .OP_BOOLOR :: script) (a :: b :: rest) altStack flags ctx result

  -- OP_BOOLAND
  | booland : (a b : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (boolToElement (castToBool a && castToBool b) :: rest)
        altStack flags ctx result →
      Eval (.op .OP_BOOLAND :: script) (a :: b :: rest) altStack flags ctx result

  -- OP_IF/OP_NOTIF/OP_ELSE/OP_ENDIF
  -- Structural model for compiled Miniscript control-flow blocks.
  | if_true : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = true →
      Eval (thenBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | if_false : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = false →
      Eval (elseBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | if_else_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      flags.minimalIf = true →
      minimalIfArg top = false →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx (.failure "MINIMALIF failed")

  | if_no_else_true : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = true →
      Eval (thenBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | if_no_else_false : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = false →
      Eval after rest altStack flags ctx result →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | if_no_else_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      flags.minimalIf = true →
      minimalIfArg top = false →
      Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx (.failure "MINIMALIF failed")

  | notif_true : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = true →
      Eval (elseBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | notif_false : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = false →
      Eval (thenBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | notif_else_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch elseBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      flags.minimalIf = true →
      minimalIfArg top = false →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++
            elseBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx (.failure "MINIMALIF failed")

  | notif_no_else_true : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = true →
      Eval after rest altStack flags ctx result →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | notif_no_else_false : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      minimalIfSatisfied flags top →
      castToBool top = false →
      Eval (thenBranch ++ after) rest altStack flags ctx result →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx result

  | notif_no_else_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (thenBranch after : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      flags.minimalIf = true →
      minimalIfArg top = false →
      Eval ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ENDIF] ++ after)
           (top :: rest) altStack flags ctx (.failure "MINIMALIF failed")

  -- OP_SWAP
  | swap : (a b : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (b :: a :: rest) altStack flags ctx result →
      Eval (.op .OP_SWAP :: script) (a :: b :: rest) altStack flags ctx result

  -- OP_TOALTSTACK
  | toAltStack : (x : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script rest (x :: altStack) flags ctx result →
      Eval (.op .OP_TOALTSTACK :: script) (x :: rest) altStack flags ctx result

  -- OP_FROMALTSTACK
  | fromAltStack : (x : StackElement) → (stack altRest : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (x :: stack) altRest flags ctx result →
      Eval (.op .OP_FROMALTSTACK :: script) stack (x :: altRest) flags ctx result

  -- OP_0NOTEQUAL
  | zeroNotEqual : (x : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (boolToElement (castToBool x) :: rest) altStack flags ctx result →
      Eval (.op .OP_0NOTEQUAL :: script) (x :: rest) altStack flags ctx result

  -- OP_IFDUP
  | ifdup_true : (x : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool x = true →
      Eval script (x :: x :: rest) altStack flags ctx result →
      Eval (.op .OP_IFDUP :: script) (x :: rest) altStack flags ctx result

  | ifdup_false : (x : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      castToBool x = false →
      Eval script (x :: rest) altStack flags ctx result →
      Eval (.op .OP_IFDUP :: script) (x :: rest) altStack flags ctx result

  -- OP_SIZE
  | size : (x : StackElement) → (rest altStack : Stack) →
      (script : Script) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      Eval script (scriptNat x.size :: x :: rest) altStack flags ctx result →
      Eval (.op .OP_SIZE :: script) (x :: rest) altStack flags ctx result

  -- Sequential composition
  | seq : (s1 s2 : Script) → (stack midStack altStack midAltStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval s1 stack altStack flags ctx (.success midStack midAltStack) →
      Eval s2 midStack midAltStack flags ctx result →
      Eval (s1 ++ s2) stack altStack flags ctx result

/-- A concrete non-minimal truthy IF argument fails when MINIMALIF is active. -/
theorem nonMinimalTruthy_if_else_minimalif_failure
    (rest altStack : Stack) (thenBranch elseBranch after : Script)
    (flags : ScriptFlags) (ctx : TxContext)
    (hflags : flags.minimalIf = true) :
    Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
          elseBranch ++ [.op .OP_ENDIF] ++ after)
         (nonMinimalTruthyElement :: rest) altStack flags ctx
         (.failure "MINIMALIF failed") := by
  exact Eval.if_else_minimalif_failure nonMinimalTruthyElement rest altStack
    thenBranch elseBranch after flags ctx
    hflags nonMinimalTruthyElement_not_minimalIfArg

/-- Without MINIMALIF, the same concrete non-minimal truthy IF argument selects
    the true branch. -/
theorem nonMinimalTruthy_if_else_relaxed_true
    (rest altStack : Stack) (thenBranch elseBranch after : Script)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult)
    (hflags : flags.minimalIf = false)
    (hthen : Eval (thenBranch ++ after) rest altStack flags ctx result) :
    Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
          elseBranch ++ [.op .OP_ENDIF] ++ after)
         (nonMinimalTruthyElement :: rest) altStack flags ctx result := by
  exact Eval.if_true nonMinimalTruthyElement rest altStack thenBranch elseBranch after
    flags ctx result
    (Or.inl hflags) nonMinimalTruthyElement_truthy hthen

/-- Moving a stack element to the alt stack and immediately back preserves both
    stacks. -/
theorem toAltStack_fromAltStack_roundtrip
    (x : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    Eval [.op .OP_TOALTSTACK, .op .OP_FROMALTSTACK]
      (x :: stack) altStack flags ctx (.success (x :: stack) altStack) := by
  exact Eval.toAltStack x stack altStack [.op .OP_FROMALTSTACK] flags ctx _
    (Eval.fromAltStack x stack altStack [] flags ctx _
      (Eval.empty (x :: stack) altStack flags ctx))

end LeanMiniscript.Script
