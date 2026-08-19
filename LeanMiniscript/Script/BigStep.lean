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

  -- Fixed-arity opcode failure. Variable-arity CHECKMULTISIG and malformed
  -- operand encodings have their own semantic boundaries.
  | stack_underflow : (opcode : Opcode) → (required : Nat) →
      (script : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      opcode.fixedMainStackInputs? = some required →
      stack.length < required →
      Eval (.op opcode :: script) stack altStack flags ctx
        (.failure .stackUnderflow)

  -- OP_FROMALTSTACK consumes no main-stack input, but fails when the alternate
  -- stack is empty.
  | fromaltstack_underflow : (script : Script) → (stack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx
        (.failure .altStackUnderflow)

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

  -- OP_CHECKSIGADD: pubkey on top, accumulated count below, signature below that.
  | checksigadd_success : (pubkey sig : StackElement) → (count : Nat) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = true →
      Eval script (scriptNat (count + 1) :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: scriptNat count :: sig :: rest) altStack flags ctx result

  | checksigadd_failure : (pubkey sig : StackElement) → (count : Nat) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      checkSig sig pubkey ctx.sigHash = false →
      Eval script (scriptNat count :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: scriptNat count :: sig :: rest) altStack flags ctx result

  -- OP_CHECKMULTISIG: legacy dummy, k signatures, n public keys.
  | checkmultisig_success : (k n : Nat) → (dummy : StackElement) →
      (sigs pubkeys rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      sigs.length = k →
      pubkeys.length = n →
      nullDummySatisfied flags dummy →
      checkMultiSig sigs pubkeys ctx.sigHash = true →
      Eval script (trueElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script)
        (scriptNat n :: (pubkeys ++ scriptNat k :: dummy :: sigs ++ rest))
        altStack flags ctx result

  | checkmultisig_failure : (k n : Nat) → (dummy : StackElement) →
      (sigs pubkeys rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      sigs.length = k →
      pubkeys.length = n →
      nullDummySatisfied flags dummy →
      checkMultiSig sigs pubkeys ctx.sigHash = false →
      Eval script (falseElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script)
        (scriptNat n :: (pubkeys ++ scriptNat k :: dummy :: sigs ++ rest))
        altStack flags ctx result

  | checkmultisig_nulldummy_failure : (k n : Nat) → (dummy : StackElement) →
      (sigs pubkeys rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      sigs.length = k →
      pubkeys.length = n →
      ¬ nullDummySatisfied flags dummy →
      Eval (.op .OP_CHECKMULTISIG :: script)
        (scriptNat n :: (pubkeys ++ scriptNat k :: dummy :: sigs ++ rest))
        altStack flags ctx (.failure .nullDummy)

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
        (.failure .equalVerify)

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
        (.failure .verify)

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
        altStack flags ctx (.failure .checkSequenceVerify)

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
        altStack flags ctx (.failure .checkLockTimeVerify)

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

  -- OP_ADD
  | add : (a b : Nat) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (scriptNat (a + b) :: rest) altStack flags ctx result →
      Eval (.op .OP_ADD :: script) (scriptNat a :: scriptNat b :: rest)
        altStack flags ctx result

  -- OP_NUMEQUAL
  | numequal : (a b : Nat) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script (boolToElement (a == b) :: rest) altStack flags ctx result →
      Eval (.op .OP_NUMEQUAL :: script) (scriptNat a :: scriptNat b :: rest)
        altStack flags ctx result

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
           (top :: rest) altStack flags ctx (.failure .minimalIf)

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
           (top :: rest) altStack flags ctx (.failure .minimalIf)

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
           (top :: rest) altStack flags ctx (.failure .minimalIf)

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
           (top :: rest) altStack flags ctx (.failure .minimalIf)

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


/-- Evaluation composes over script concatenation. Keeping sequencing as a
    theorem avoids adding a non-opcode case to every induction over `Eval`. -/
theorem Eval.append
    {left right : Script} {stack midStack altStack midAltStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (leftEval : Eval left stack altStack flags ctx (.success midStack midAltStack))
    (rightEval : Eval right midStack midAltStack flags ctx result) :
    Eval (left ++ right) stack altStack flags ctx result := by
  generalize resultEq : ExecResult.success midStack midAltStack = leftResult at leftEval
  induction leftEval generalizing right result <;>
    cases resultEq <;>
    simp_all [List.append_assoc] <;>
    try grind [Eval]
  case if_true.refl =>
    rename_i top rest altStack thenBranch elseBranch after flags ctx
      minimal truthy _ ih
    simpa [List.append_assoc] using
      (Eval.if_true top rest altStack thenBranch elseBranch (after ++ right)
        flags ctx result minimal truthy (ih rightEval))
  case if_false.refl =>
    rename_i top rest altStack thenBranch elseBranch after flags ctx
      minimal falsey _ ih
    simpa [List.append_assoc] using
      (Eval.if_false top rest altStack thenBranch elseBranch (after ++ right)
        flags ctx result minimal falsey (ih rightEval))
  case if_no_else_true.refl =>
    rename_i top rest altStack thenBranch after flags ctx minimal truthy _ ih
    simpa [List.append_assoc] using
      (Eval.if_no_else_true top rest altStack thenBranch (after ++ right)
        flags ctx result minimal truthy (ih rightEval))
  case if_no_else_false.refl =>
    rename_i top rest altStack thenBranch after flags ctx minimal falsey _ ih
    simpa [List.append_assoc] using
      (Eval.if_no_else_false top rest altStack thenBranch (after ++ right)
        flags ctx result minimal falsey (ih rightEval))
  case notif_true.refl =>
    rename_i top rest altStack thenBranch elseBranch after flags ctx
      minimal truthy _ ih
    simpa [List.append_assoc] using
      (Eval.notif_true top rest altStack thenBranch elseBranch (after ++ right)
        flags ctx result minimal truthy (ih rightEval))
  case notif_false.refl =>
    rename_i top rest altStack thenBranch elseBranch after flags ctx
      minimal falsey _ ih
    simpa [List.append_assoc] using
      (Eval.notif_false top rest altStack thenBranch elseBranch (after ++ right)
        flags ctx result minimal falsey (ih rightEval))
  case notif_no_else_true.refl =>
    rename_i top rest altStack thenBranch after flags ctx minimal truthy _ ih
    simpa [List.append_assoc] using
      (Eval.notif_no_else_true top rest altStack thenBranch (after ++ right)
        flags ctx result minimal truthy (ih rightEval))
  case notif_no_else_false.refl =>
    rename_i top rest altStack thenBranch after flags ctx minimal falsey _ ih
    simpa [List.append_assoc] using
      (Eval.notif_no_else_false top rest altStack thenBranch (after ++ right)
        flags ctx result minimal falsey (ih rightEval))

/-! ## Proof-facing execution API

These lemmas keep unchanged scripts, stacks, flags, contexts, and results
implicit. Soundness proofs can compose execution steps without repeating the
full constructor argument list.
-/

/-- A fixed-arity opcode fails immediately when its main stack is too short. -/
theorem Eval.fixedArityStackUnderflow
    {opcode : Opcode} {required : Nat} {script : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (arity : opcode.fixedMainStackInputs? = some required)
    (underflow : stack.length < required) :
    Eval (.op opcode :: script) stack altStack flags ctx
      (.failure .stackUnderflow) :=
  .stack_underflow opcode required script stack altStack flags ctx arity underflow

/-- `OP_FROMALTSTACK` fails immediately when its alternate stack is empty. -/
theorem Eval.fromAltStackUnderflow
    {script : Script} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext} :
    Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx
      (.failure .altStackUnderflow) :=
  .fromaltstack_underflow script stack flags ctx

/-- Main-stack underflow cannot overlap a normal fixed-arity opcode rule. -/
theorem Eval.fixedArityStackUnderflow_result
    {opcode : Opcode} {required : Nat} {script : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (arity : opcode.fixedMainStackInputs? = some required)
    (underflow : stack.length < required)
    (evaluated : Eval (.op opcode :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?] <;>
    omega

/-- Empty-alt-stack failure cannot overlap normal `OP_FROMALTSTACK` execution. -/
theorem Eval.fromAltStack_empty_result
    {script : Script} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (evaluated : Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx result) :
    result = .failure .altStackUnderflow := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?] <;>
    omega

theorem Eval.done {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext} :
    Eval [] stack altStack flags ctx (.success stack altStack) :=
  .empty stack altStack flags ctx

theorem Eval.pushDataNext
    {data : StackElement} {rest : Script} {stack altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval rest (data :: stack) altStack flags ctx result) :
    Eval (.pushData data :: rest) stack altStack flags ctx result :=
  .pushData data rest stack altStack flags ctx result next

theorem Eval.checksigTrue
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSig sig pubkey ctx.sigHash = true)
    (next : Eval script (trueElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest)
      altStack flags ctx result :=
  .checksig_success pubkey sig rest script altStack flags ctx result checked next

theorem Eval.checksigFalse
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSig sig pubkey ctx.sigHash = false)
    (next : Eval script (falseElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest)
      altStack flags ctx result :=
  .checksig_failure pubkey sig rest script altStack flags ctx result checked next

theorem Eval.verifyTrue
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (truthy : castToBool top = true)
    (next : Eval script rest altStack flags ctx result) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx result :=
  .verify_success top rest script altStack flags ctx result truthy next

theorem Eval.verifyFalse
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (falsey : castToBool top = false) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx
      (.failure .verify) :=
  .verify_failure top rest script altStack flags ctx falsey

theorem Eval.toAltStackNext
    {x : StackElement} {rest altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script rest (x :: altStack) flags ctx result) :
    Eval (.op .OP_TOALTSTACK :: script) (x :: rest) altStack flags ctx result :=
  .toAltStack x rest altStack script flags ctx result next

theorem Eval.fromAltStackNext
    {x : StackElement} {stack altRest : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script (x :: stack) altRest flags ctx result) :
    Eval (.op .OP_FROMALTSTACK :: script) stack (x :: altRest) flags ctx result :=
  .fromAltStack x stack altRest script flags ctx result next

/-- A concrete non-minimal truthy IF argument fails when MINIMALIF is active. -/
theorem nonMinimalTruthy_if_else_minimalif_failure
    (rest altStack : Stack) (thenBranch elseBranch after : Script)
    (flags : ScriptFlags) (ctx : TxContext)
    (hflags : flags.minimalIf = true) :
    Eval ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
          elseBranch ++ [.op .OP_ENDIF] ++ after)
         (nonMinimalTruthyElement :: rest) altStack flags ctx
         (.failure .minimalIf) := by
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
