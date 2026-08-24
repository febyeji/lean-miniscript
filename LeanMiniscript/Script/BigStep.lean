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

  -- Numeric operand failures are terminal. Grouped rules use executable
  -- decoders so simultaneous malformed operands still select one error in
  -- Bitcoin Core's operand-evaluation order.
  | binary_scriptnum_failure : (opcode : Opcode) →
      (top belowTop : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      opcode.usesBinaryScriptNums = true →
      decodeBinaryScriptNums flags top belowTop = .error error →
      Eval (.op opcode :: script) (top :: belowTop :: rest) altStack flags ctx
        (.failure error)

  | unary_scriptnum_failure : (operand : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .error error →
      Eval (.op .OP_0NOTEQUAL :: script) (operand :: rest) altStack flags ctx
        (.failure error)

  | checksigadd_scriptnum_failure : (pubkey countBytes sig : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeScriptNum countBytes flags.minimalData maxArithmeticScriptNumBytes =
        .error error →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx
        (.failure error)

  | timelock_scriptnum_failure : (opcode : Opcode) →
      (operand : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      opcode.usesTimelockScriptNum = true →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes =
        .error error →
      Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
        (.failure error)

  | timelock_negative_failure : (opcode : Opcode) →
      (operand : StackElement) → (value : Int) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      opcode.usesTimelockScriptNum = true →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes =
        .ok value →
      value < 0 →
      Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
        (.failure .negativeLocktime)

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
  | checksigadd_success : (pubkey countBytes sig : StackElement) → (count : Int) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum countBytes flags.minimalData maxArithmeticScriptNumBytes =
        .ok count →
      checkSig sig pubkey ctx.sigHash = true →
      Eval script (scriptNum (count + 1) :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx result

  | checksigadd_failure : (pubkey countBytes sig : StackElement) → (count : Int) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum countBytes flags.minimalData maxArithmeticScriptNumBytes =
        .ok count →
      checkSig sig pubkey ctx.sigHash = false →
      Eval script (scriptNum count :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx result

  -- OP_CHECKMULTISIG: dynamically decoded counts, public keys, signatures, and
  -- the historical dummy argument. Decoder failures are terminal before the
  -- signature oracle is consulted.
  | checkmultisig_operand_failure : (stack : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      decodeCheckMultiSigOperands flags stack = .error error →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
        (.failure error)

  | checkmultisig_success : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeCheckMultiSigOperands flags stack = .ok operands →
      nullDummySatisfied flags operands.dummy →
      checkMultiSig operands.signatures operands.pubkeys ctx.sigHash = true →
      Eval script (trueElement :: operands.rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx result

  | checkmultisig_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeCheckMultiSigOperands flags stack = .ok operands →
      nullDummySatisfied flags operands.dummy →
      checkMultiSig operands.signatures operands.pubkeys ctx.sigHash = false →
      Eval script (falseElement :: operands.rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx result

  | checkmultisig_nulldummy_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      decodeCheckMultiSigOperands flags stack = .ok operands →
      ¬ nullDummySatisfied flags operands.dummy →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
        (.failure .nullDummy)

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
  | checksequenceverify_success : (operand : StackElement) → (n : Int) →
      (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes = .ok n →
      0 ≤ n →
      sequenceSatisfied n.toNat ctx →
      Eval script (operand :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSEQUENCEVERIFY :: script) (operand :: rest)
        altStack flags ctx result

  | checksequenceverify_failure : (operand : StackElement) → (n : Int) →
      (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes = .ok n →
      0 ≤ n →
      ¬ sequenceSatisfied n.toNat ctx →
      Eval (.op .OP_CHECKSEQUENCEVERIFY :: script) (operand :: rest)
        altStack flags ctx (.failure .checkSequenceVerify)

  -- OP_CHECKLOCKTIMEVERIFY
  | checklocktimeverify_success : (operand : StackElement) → (n : Int) →
      (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes = .ok n →
      0 ≤ n →
      locktimeSatisfied n.toNat ctx →
      Eval script (operand :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script) (operand :: rest)
        altStack flags ctx result

  | checklocktimeverify_failure : (operand : StackElement) → (n : Int) →
      (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      decodeScriptNum operand flags.minimalData maxTimelockScriptNumBytes = .ok n →
      0 ≤ n →
      ¬ locktimeSatisfied n.toNat ctx →
      Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script) (operand :: rest)
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
  | boolor : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement ((a != 0) || (b != 0)) :: rest)
        altStack flags ctx result →
      Eval (.op .OP_BOOLOR :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_BOOLAND
  | booland : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement ((a != 0) && (b != 0)) :: rest)
        altStack flags ctx result →
      Eval (.op .OP_BOOLAND :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_ADD
  | add : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (scriptNum (a + b) :: rest) altStack flags ctx result →
      Eval (.op .OP_ADD :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_NUMEQUAL
  | numequal : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (a == b) :: rest) altStack flags ctx result →
      Eval (.op .OP_NUMEQUAL :: script) (aBytes :: bBytes :: rest)
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
  | zeroNotEqual : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (boolToElement (value != 0) :: rest) altStack flags ctx result →
      Eval (.op .OP_0NOTEQUAL :: script) (operand :: rest)
        altStack flags ctx result

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

/-- A malformed operand terminates any ordinary binary numeric opcode before
    the remaining script executes. -/
theorem Eval.binaryScriptNumFailure
    {opcode : Opcode} {top belowTop : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError}
    (usesNumbers : opcode.usesBinaryScriptNums = true)
    (decoded : decodeBinaryScriptNums flags top belowTop = .error error) :
    Eval (.op opcode :: script) (top :: belowTop :: rest) altStack flags ctx
      (.failure error) :=
  .binary_scriptnum_failure opcode top belowTop rest script altStack flags ctx
    error usesNumbers decoded

/-- A malformed CLTV/CSV operand terminates evaluation before the timelock
    predicate is consulted. -/
theorem Eval.timelockScriptNumFailure
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .error error) :
    Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
      (.failure error) :=
  .timelock_scriptnum_failure opcode operand rest script altStack flags ctx
    error usesNumber decoded

/-- A malformed or incomplete legacy multisignature frame terminates before
    signature matching or NULLDUMMY validation. -/
theorem Eval.checkMultiSigOperandFailure
    {stack : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
    (decoded : decodeCheckMultiSigOperands flags stack = .error error) :
    Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      (.failure error) :=
  .checkmultisig_operand_failure stack script altStack flags ctx error decoded

/-- Main-stack underflow cannot overlap a normal fixed-arity opcode rule. -/
theorem Eval.fixedArityStackUnderflow_result
    {opcode : Opcode} {required : Nat} {script : Script}
    {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (arity : opcode.fixedMainStackInputs? = some required)
    (underflow : stack.length < required)
    (evaluated : Eval (.op opcode :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow := by
  cases opcode <;> cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- Empty-alt-stack failure cannot overlap normal `OP_FROMALTSTACK` execution. -/
theorem Eval.fromAltStack_empty_result
    {script : Script} {stack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (evaluated : Eval (.op .OP_FROMALTSTACK :: script) stack [] flags ctx result) :
    result = .failure .altStackUnderflow := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A decoder error cannot overlap a normal binary numeric execution rule. -/
theorem Eval.binaryScriptNumFailure_result
    {opcode : Opcode} {top belowTop : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesNumbers : opcode.usesBinaryScriptNums = true)
    (decoded : decodeBinaryScriptNums flags top belowTop = .error error)
    (evaluated : Eval (.op opcode :: script) (top :: belowTop :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases opcode <;> simp_all [Opcode.usesBinaryScriptNums]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A decoder error cannot overlap normal `OP_0NOTEQUAL` execution. -/
theorem Eval.unaryScriptNumFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxArithmeticScriptNumBytes = .error error)
    (evaluated : Eval (.op .OP_0NOTEQUAL :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A malformed CHECKSIGADD count fails before signature evaluation. -/
theorem Eval.checksigaddScriptNumFailure_result
    {pubkey countBytes sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {error : ScriptError} {result : ExecResult}
    (decoded : decodeScriptNum countBytes flags.minimalData
      maxArithmeticScriptNumBytes = .error error)
    (evaluated : Eval (.op .OP_CHECKSIGADD :: script)
      (pubkey :: countBytes :: sig :: rest) altStack flags ctx result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A legacy multisignature operand-decoder error cannot overlap a normal
    CHECKMULTISIG execution or NULLDUMMY failure. -/
theorem Eval.checkMultiSigOperandFailure_result
    {stack : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
    {result : ExecResult}
    (decoded : decodeCheckMultiSigOperands flags stack = .error error)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      result) :
    result = .failure error := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A decoded non-null dummy cannot overlap a normal CHECKMULTISIG execution. -/
theorem Eval.checkMultiSigNullDummyFailure_result
    {stack : Stack} {operands : CheckMultiSigOperands} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (decoded : decodeCheckMultiSigOperands flags stack = .ok operands)
    (invalidDummy : ¬ nullDummySatisfied flags operands.dummy)
    (evaluated : Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
      result) :
    result = .failure .nullDummy := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A decoder error cannot overlap normal CLTV/CSV execution or the separate
    negative-locktime failure. -/
theorem Eval.timelockScriptNumFailure_result
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .error error)
    (evaluated : Eval (.op opcode :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure error := by
  cases opcode <;> simp_all [Opcode.usesTimelockScriptNum]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A decoded negative timelock operand fails before either opcode consults
    its transaction-context predicate. -/
theorem Eval.timelockNegativeFailure_result
    {opcode : Opcode} {operand : StackElement} {rest : Stack}
    {script : Script} {altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {value : Int} {result : ExecResult}
    (usesNumber : opcode.usesTimelockScriptNum = true)
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (negative : value < 0)
    (evaluated : Eval (.op opcode :: script) (operand :: rest)
      altStack flags ctx result) :
    result = .failure .negativeLocktime := by
  cases opcode <;> simp_all [Opcode.usesTimelockScriptNum]
  all_goals
    cases evaluated <;>
      simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
        Opcode.usesTimelockScriptNum] <;>
      omega

/-- A nonnegative CSV operand that fails the BIP 68/112 context conditions
    cannot overlap CSV success or an earlier numeric failure. -/
theorem Eval.checkSequenceVerifyFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {value : Int} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (nonnegative : 0 ≤ value)
    (unsatisfied : ¬ sequenceSatisfied value.toNat ctx)
    (evaluated : Eval (.op .OP_CHECKSEQUENCEVERIFY :: script)
      (operand :: rest) altStack flags ctx result) :
    result = .failure .checkSequenceVerify := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
    omega

/-- A nonnegative CLTV operand that fails the BIP 65 context conditions cannot
    overlap CLTV success or an earlier numeric failure. -/
theorem Eval.checkLockTimeVerifyFailure_result
    {operand : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {value : Int} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData
      maxTimelockScriptNumBytes = .ok value)
    (nonnegative : 0 ≤ value)
    (unsatisfied : ¬ locktimeSatisfied value.toNat ctx)
    (evaluated : Eval (.op .OP_CHECKLOCKTIMEVERIFY :: script)
      (operand :: rest) altStack flags ctx result) :
    result = .failure .checkLockTimeVerify := by
  cases evaluated <;>
    simp_all [Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum] <;>
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
