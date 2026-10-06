import LeanMiniscript.Script.Conditional
import LeanMiniscript.Script.SignatureChecks

/-! Big-step evaluation relation for the modeled Script opcodes.
Composition, determinism and opcode lemmas are in BigStepProofs. -/

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

  -- OP_NOP
  | nop : (rest : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval rest stack altStack flags ctx result →
      Eval (.op .OP_NOP :: rest) stack altStack flags ctx result

  -- Upgradeable NOPs are permitted by consensus and can be discouraged by policy.
  | upgradeableNop : (opcode : Opcode) → (rest : Script) →
      (stack altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      opcode.isUpgradeableNop = true → flags.discourageUpgradableNops = false →
      Eval rest stack altStack flags ctx result →
      Eval (.op opcode :: rest) stack altStack flags ctx result

  | upgradeableNop_discouraged : (opcode : Opcode) → (rest : Script) →
      (stack altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      opcode.isUpgradeableNop = true → flags.discourageUpgradableNops = true →
      Eval (.op opcode :: rest) stack altStack flags ctx
        (.failure .discourageUpgradableNops)

  -- OP_RETURN fails as soon as it is executed.
  | opReturn : (rest : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      Eval (.op .OP_RETURN :: rest) stack altStack flags ctx (.failure .opReturn)

  -- Fixed-arity opcode failure. Variable-arity CHECKMULTISIG and malformed
  -- operand encodings have their own semantic boundaries.
  | stack_underflow : (opcode : Opcode) → (required : Nat) →
      (script : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      opcode.activeFixedMainStackInputs? ctx.sigVersion = some required →
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

  | stackindex_failure : (opcode : Opcode) →
      (operand top : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      opcode.usesStackIndex = true →
      decodeStackIndex flags operand (top :: rest).length = .error error →
      Eval (.op opcode :: script) (operand :: top :: rest) altStack flags ctx
        (.failure error)

  | within_scriptnum_failure : (upperBytes lowerBytes valueBytes : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .error error →
      Eval (.op .OP_WITHIN :: script) (upperBytes :: lowerBytes :: valueBytes :: rest)
        altStack flags ctx (.failure error)

  | not_scriptnum_failure : (operand : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .error error →
      Eval (.op .OP_NOT :: script) (operand :: rest) altStack flags ctx
        (.failure error)

  | unary_scriptnum_failure : (operand : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .error error →
      Eval (.op .OP_0NOTEQUAL :: script) (operand :: rest) altStack flags ctx
        (.failure error)

  | unaryArithmetic_scriptnum_failure : (opcode : Opcode) →
      (operand : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      opcode.usesUnaryArithmetic = true →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .error error →
      Eval (.op opcode :: script) (operand :: rest) altStack flags ctx
        (.failure error)

  | checksigadd_scriptnum_failure : (pubkey countBytes sig : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      ctx.sigVersion = .tapscript →
      decodeCheckSigAddCount flags ctx countBytes =
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

  -- Version-aware CHECKSIG results; encoding and crypto failures are terminal.
  | checksig_success : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true →
      Eval script (trueElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result

  | checksig_failure : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok false →
      Eval script (falseElement :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result

  | checksig_encoding_failure : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (error : ScriptError) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error error →
      Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx
        (.failure error)

  -- OP_CHECKSIGVERIFY performs the same checked signature operation, then
  -- consumes a successful result or terminates with its VERIFY-specific error.
  | checksigverify_success : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) → (result : ExecResult) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_CHECKSIGVERIFY :: script) (pubkey :: sig :: rest)
        altStack flags ctx result

  | checksigverify_failure : (pubkey sig : StackElement) → (rest : Stack) →
      (script : Script) → (altStack : Stack) → (flags : ScriptFlags) →
      (ctx : TxContext) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok false →
      Eval (.op .OP_CHECKSIGVERIFY :: script) (pubkey :: sig :: rest)
        altStack flags ctx (.failure .checkSigVerify)

  | checksigverify_encoding_failure : (pubkey sig : StackElement) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error error →
      Eval (.op .OP_CHECKSIGVERIFY :: script) (pubkey :: sig :: rest)
        altStack flags ctx (.failure error)

  -- CHECKSIGADD is unavailable before Tapscript, even on an empty stack.
  | checksigadd_unavailable : (stack : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      ctx.sigVersion ≠ .tapscript →
      Eval (.op .OP_CHECKSIGADD :: script) stack altStack flags ctx (.failure .badOpcode)

  | checksigadd_success : (pubkey countBytes sig : StackElement) → (count : Int) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeCheckSigAddCount flags ctx countBytes = .ok count →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true →
      Eval script (scriptNum (count + 1) :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx result

  | checksigadd_failure : (pubkey countBytes sig : StackElement) → (count : Int) →
      (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeCheckSigAddCount flags ctx countBytes = .ok count →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok false →
      Eval script (scriptNum count :: rest) altStack flags ctx result →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx result

  | checksigadd_encoding_failure : (pubkey countBytes sig : StackElement) →
      (count : Int) → (rest : Stack) → (script : Script) → (altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) → (error : ScriptError) →
      decodeCheckSigAddCount flags ctx countBytes = .ok count →
      checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error error →
      Eval (.op .OP_CHECKSIGADD :: script)
        (pubkey :: countBytes :: sig :: rest) altStack flags ctx (.failure error)

  -- OP_CHECKMULTISIG: dynamically decoded counts, public keys, signatures, and
  -- the historical dummy argument. Decoder failures are terminal before the
  -- signature oracle is consulted.
  | checkmultisig_operand_failure : (stack : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .error error →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
        (.failure error)

  | checkmultisig_encoding_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .error error →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx (.failure error)

  | checkmultisig_success : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok true →
      checkMultiSigDummy flags operands.dummy = .ok () →
      Eval script (trueElement :: operands.rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx result

  | checkmultisig_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok false →
      nullFailSatisfied flags operands.signatures →
      checkMultiSigDummy flags operands.dummy = .ok () →
      Eval script (falseElement :: operands.rest) altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx result

  | checkmultisig_nullfail_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok false →
      ¬ nullFailSatisfied flags operands.signatures →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
        (.failure .sigNullFail)

  | checkmultisig_dummy_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (checked : Bool) → (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok checked →
      (checked = true ∨ nullFailSatisfied flags operands.signatures) →
      checkMultiSigDummy flags operands.dummy = .error error →
      Eval (.op .OP_CHECKMULTISIG :: script) stack altStack flags ctx
        (.failure error)

  -- OP_CHECKMULTISIGVERIFY preserves CHECKMULTISIG's operand, encoding,
  -- NULLFAIL, and NULLDUMMY precedence, then consumes a successful result.
  | checkmultisigverify_operand_failure : (stack : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .error error →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx
        (.failure error)

  | checkmultisigverify_encoding_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .error error →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx
        (.failure error)

  | checkmultisigverify_success : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok true →
      checkMultiSigDummy flags operands.dummy = .ok () →
      Eval script operands.rest altStack flags ctx result →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx result

  | checkmultisigverify_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok false →
      nullFailSatisfied flags operands.signatures →
      checkMultiSigDummy flags operands.dummy = .ok () →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx
        (.failure .checkMultiSigVerify)

  | checkmultisigverify_nullfail_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok false →
      ¬ nullFailSatisfied flags operands.signatures →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx
        (.failure .sigNullFail)

  | checkmultisigverify_dummy_failure : (stack : Stack) →
      (operands : CheckMultiSigOperands) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (checked : Bool) → (error : ScriptError) →
      decodeCheckMultiSigOperandsFor flags ctx stack = .ok operands →
      checkMultiSigFor checkSig flags ctx
        operands.signatures operands.pubkeys = .ok checked →
      (checked = true ∨ nullFailSatisfied flags operands.signatures) →
      checkMultiSigDummy flags operands.dummy = .error error →
      Eval (.op .OP_CHECKMULTISIGVERIFY :: script) stack altStack flags ctx
        (.failure error)

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

  -- OP_DEPTH: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: push CScriptNum(stack.size()).getvch().
  | depth : (stack altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (scriptNat stack.length :: stack) altStack flags ctx result →
      Eval (.op .OP_DEPTH :: script) stack altStack flags ctx result

  -- OP_DROP
  | drop : (x : StackElement) → (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_DROP :: script) (x :: rest) altStack flags ctx result

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

  -- OP_1ADD
  | oneAdd : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (scriptNum (value + 1) :: rest) altStack flags ctx result →
      Eval (.op .OP_1ADD :: script) (operand :: rest) altStack flags ctx result

  -- OP_1SUB
  | oneSub : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (scriptNum (value - 1) :: rest) altStack flags ctx result →
      Eval (.op .OP_1SUB :: script) (operand :: rest) altStack flags ctx result

  -- OP_NEGATE
  | negate : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (scriptNum (-value) :: rest) altStack flags ctx result →
      Eval (.op .OP_NEGATE :: script) (operand :: rest) altStack flags ctx result

  -- OP_ABS
  | abs : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (scriptNum (if value < 0 then -value else value) :: rest) altStack flags ctx result →
      Eval (.op .OP_ABS :: script) (operand :: rest) altStack flags ctx result

  -- OP_SUB; the stack head is the right-hand operand.
  | sub : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (scriptNum (b - a) :: rest) altStack flags ctx result →
      Eval (.op .OP_SUB :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_NUMNOTEQUAL; the stack head is the right-hand operand.
  | numNotEqual : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (decide (a ≠ b)) :: rest) altStack flags ctx result →
      Eval (.op .OP_NUMNOTEQUAL :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_LESSTHAN; the stack head is the right-hand operand.
  | lessThan : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (decide (b < a)) :: rest) altStack flags ctx result →
      Eval (.op .OP_LESSTHAN :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_GREATERTHAN; the stack head is the right-hand operand.
  | greaterThan : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (decide (b > a)) :: rest) altStack flags ctx result →
      Eval (.op .OP_GREATERTHAN :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_LESSTHANOREQUAL; the stack head is the right-hand operand.
  | lessThanOrEqual : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (decide (b ≤ a)) :: rest) altStack flags ctx result →
      Eval (.op .OP_LESSTHANOREQUAL :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_GREATERTHANOREQUAL; the stack head is the right-hand operand.
  | greaterThanOrEqual : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (boolToElement (decide (b ≥ a)) :: rest) altStack flags ctx result →
      Eval (.op .OP_GREATERTHANOREQUAL :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_MIN
  | min : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (scriptNum (Min.min b a) :: rest) altStack flags ctx result →
      Eval (.op .OP_MIN :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  -- OP_MAX
  | max : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      Eval script (scriptNum (Max.max b a) :: rest) altStack flags ctx result →
      Eval (.op .OP_MAX :: script) (aBytes :: bBytes :: rest)
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

  -- OP_NUMEQUALVERIFY decodes both operands before comparing them.
  | numequalverify_success : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      (result : ExecResult) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      a = b →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_NUMEQUALVERIFY :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx result

  | numequalverify_failure : (aBytes bBytes : StackElement) → (a b : Int) →
      (rest : Stack) → (script : Script) →
      (altStack : Stack) → (flags : ScriptFlags) → (ctx : TxContext) →
      decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b) →
      a ≠ b →
      Eval (.op .OP_NUMEQUALVERIFY :: script) (aBytes :: bBytes :: rest)
        altStack flags ctx (.failure .numEqualVerify)

  -- OP_IF/OP_NOTIF/OP_ELSE/OP_ENDIF. The executable splitter makes the
  -- matching ENDIF and same-depth ELSE segments unique, including nesting.
  | if_execute : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (frame : ConditionalFrame) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      splitConditional script = some frame →
      minimalIfSatisfied flags ctx.sigVersion top →
      Eval (frame.select (castToBool top)) rest altStack flags ctx result →
      Eval (.op .OP_IF :: script) (top :: rest) altStack flags ctx result

  | notif_execute : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (frame : ConditionalFrame) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      splitConditional script = some frame →
      minimalIfSatisfied flags ctx.sigVersion top →
      Eval (frame.select (!castToBool top)) rest altStack flags ctx result →
      Eval (.op .OP_NOTIF :: script) (top :: rest) altStack flags ctx result

  | if_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      ¬ minimalIfSatisfied flags ctx.sigVersion top →
      Eval (.op .OP_IF :: script) (top :: rest) altStack flags ctx
        (.failure (minimalIfError ctx.sigVersion))

  | notif_minimalif_failure : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      ¬ minimalIfSatisfied flags ctx.sigVersion top →
      Eval (.op .OP_NOTIF :: script) (top :: rest) altStack flags ctx
        (.failure (minimalIfError ctx.sigVersion))

  | if_unbalanced : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (selectedResult : ExecResult) →
      splitConditional script = none →
      minimalIfSatisfied flags ctx.sigVersion top →
      Eval (selectUnclosedConditional script (castToBool top)) rest altStack
        flags ctx selectedResult →
      Eval (.op .OP_IF :: script) (top :: rest) altStack flags ctx
        (finishUnclosedConditional selectedResult)

  | notif_unbalanced : (top : StackElement) → (rest altStack : Stack) →
      (script : Script) → (flags : ScriptFlags) → (ctx : TxContext) →
      (selectedResult : ExecResult) →
      splitConditional script = none →
      minimalIfSatisfied flags ctx.sigVersion top →
      Eval (selectUnclosedConditional script (!castToBool top)) rest altStack
        flags ctx selectedResult →
      Eval (.op .OP_NOTIF :: script) (top :: rest) altStack flags ctx
        (finishUnclosedConditional selectedResult)

  | else_unbalanced : (script : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      Eval (.op .OP_ELSE :: script) stack altStack flags ctx
        (.failure .unbalancedConditional)

  | endif_unbalanced : (script : Script) → (stack altStack : Stack) →
      (flags : ScriptFlags) → (ctx : TxContext) →
      Eval (.op .OP_ENDIF :: script) stack altStack flags ctx
        (.failure .unbalancedConditional)

  -- OP_NIP: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: erase stack.end() - 2 after checking two inputs.
  | nip : (top discarded : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (top :: rest) altStack flags ctx result →
      Eval (.op .OP_NIP :: script) (top :: discarded :: rest) altStack flags ctx result

  -- OP_2DROP: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: pop twice after checking two inputs.
  | twoDrop : (top discarded : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script rest altStack flags ctx result →
      Eval (.op .OP_2DROP :: script) (top :: discarded :: rest) altStack flags ctx result

  -- OP_2DUP: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: copy stacktop(-2), then stacktop(-1), after checking two inputs.
  | twoDup : (top below : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (top :: below :: top :: below :: rest) altStack flags ctx result →
      Eval (.op .OP_2DUP :: script) (top :: below :: rest) altStack flags ctx result

  -- OP_3DUP: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: copy stacktop(-3), stacktop(-2), then stacktop(-1).
  | threeDup : (top second third : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (top :: second :: third :: top :: second :: third :: rest)
        altStack flags ctx result →
      Eval (.op .OP_3DUP :: script) (top :: second :: third :: rest) altStack flags ctx result

  -- OP_2OVER: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: copy stacktop(-4), then stacktop(-3), after checking four inputs.
  | twoOver : (top second third fourth : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (third :: fourth :: top :: second :: third :: fourth :: rest)
        altStack flags ctx result →
      Eval (.op .OP_2OVER :: script) (top :: second :: third :: fourth :: rest) altStack flags ctx result

  -- OP_OVER: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: copy stacktop(-2) after checking two inputs.
  | over : (top below : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (below :: top :: below :: rest) altStack flags ctx result →
      Eval (.op .OP_OVER :: script) (top :: below :: rest) altStack flags ctx result

  -- OP_PICK decodes its index after the fixed two-item check.
  | pick : (operand top : StackElement) → (index : Nat) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeStackIndex flags operand (top :: rest).length = .ok index →
      Eval script ((top :: rest)[index]?.getD ByteArray.empty :: (top :: rest))
        altStack flags ctx result →
      Eval (.op .OP_PICK :: script) (operand :: top :: rest) altStack flags ctx result

  -- OP_ROLL decodes its index after the fixed two-item check.
  | roll : (operand top : StackElement) → (index : Nat) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeStackIndex flags operand (top :: rest).length = .ok index →
      Eval script ((top :: rest)[index]?.getD ByteArray.empty :: (top :: rest).eraseIdx index)
        altStack flags ctx result →
      Eval (.op .OP_ROLL :: script) (operand :: top :: rest) altStack flags ctx result

  -- OP_TUCK: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: insert a copy of stacktop(-1) at stack.end() - 2 after checking two inputs.
  | tuck : (top below : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (top :: below :: top :: rest) altStack flags ctx result →
      Eval (.op .OP_TUCK :: script) (top :: below :: rest) altStack flags ctx result

  -- OP_ROT: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: rotate the top three items after checking arity.
  | rot : (top second third : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (third :: top :: second :: rest) altStack flags ctx result →
      Eval (.op .OP_ROT :: script) (top :: second :: third :: rest) altStack flags ctx result

  -- OP_2ROT: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: move stacktop(-6) and stacktop(-5) to the top after checking six inputs.
  | twoRot : (top second third fourth fifth sixth : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (fifth :: sixth :: top :: second :: third :: fourth :: rest) altStack flags ctx result →
      Eval (.op .OP_2ROT :: script) (top :: second :: third :: fourth :: fifth :: sixth :: rest) altStack flags ctx result

  -- OP_2SWAP: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: swap stacktop(-4) with stacktop(-2), then stacktop(-3) with stacktop(-1).
  | twoSwap : (top second third fourth : StackElement) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      Eval script (third :: fourth :: top :: second :: rest) altStack flags ctx result →
      Eval (.op .OP_2SWAP :: script) (top :: second :: third :: fourth :: rest) altStack flags ctx result

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

  -- OP_WITHIN: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: decode x, min, max, then test min <= x && x < max.
  | within : (upperBytes lowerBytes valueBytes : StackElement) →
      (upper lower value : Int) → (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .ok (upper, lower, value) →
      Eval script (boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest)
        altStack flags ctx result →
      Eval (.op .OP_WITHIN :: script) (upperBytes :: lowerBytes :: valueBytes :: rest)
        altStack flags ctx result

  -- OP_NOT: Core 9be056a8a72b624dae9623b2f7bded92c2a21c91,
  -- src/script/interpreter.cpp: decode CScriptNum, then replace with bn == 0.
  | op_not : (operand : StackElement) → (value : Int) →
      (rest altStack : Stack) → (script : Script) →
      (flags : ScriptFlags) → (ctx : TxContext) → (result : ExecResult) →
      decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
        .ok value →
      Eval script (boolToElement (value == 0) :: rest) altStack flags ctx result →
      Eval (.op .OP_NOT :: script) (operand :: rest) altStack flags ctx result

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

end LeanMiniscript.Script
