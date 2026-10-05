import LeanHash160
import LeanMiniscript.Bitcoin.Schnorr
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-- Cryptographic operations needed by the executable Script evaluator.

    The model oracle below preserves the abstract functions used by `Eval`.
    Executable callers can instead use `pureLeanHashes`, supplying separate ECDSA and Schnorr
    signature verification at the application boundary. Legacy
    multisignature matching and byte-error precedence stay in the evaluator. -/
structure CryptoOracle where
  sha256 : StackElement → StackElement
  hash256 : StackElement → StackElement
  ripemd160 : StackElement → StackElement
  hash160 : StackElement → StackElement
  checkSig : StackElement → StackElement → ByteArray → Bool
  checkSchnorrSig : StackElement → StackElement → ByteArray → Bool

namespace CryptoOracle

/-- The oracle whose operations are definitionally the abstract cryptographic
    functions used by the relational big-step semantics. -/
def model : CryptoOracle where
  sha256 := LeanMiniscript.Script.sha256
  hash256 := LeanMiniscript.Script.hash256
  ripemd160 := LeanMiniscript.Script.ripemd160
  hash160 := LeanMiniscript.Script.hash160
  checkSig := LeanMiniscript.Script.checkSig
  checkSchnorrSig := LeanMiniscript.Script.checkSchnorrSig

/-- Executable pure-Lean hashes paired with caller-supplied signature checks.

    A production signature implementation can be supplied through an FFI
    without coupling the proof-facing evaluator to one native library. -/
def pureLeanHashes
    (verifySignature : StackElement → StackElement → ByteArray → Bool)
    (verifySchnorrSignature : StackElement → StackElement → ByteArray → Bool :=
      fun _ _ _ => false) :
    CryptoOracle where
  sha256 := LeanHash160.SHA256.hash
  hash256 := fun bytes =>
    LeanHash160.SHA256.hash (LeanHash160.SHA256.hash bytes)
  ripemd160 := LeanHash160.RIPEMD160.hash
  hash160 := LeanHash160.hash160
  checkSig := verifySignature
  checkSchnorrSig := verifySchnorrSignature

/-- Pure-Lean hashes and executable BIP340 verification. ECDSA remains
caller-supplied and defaults to rejection. No unconditional `RefinesModel`
claim is made for this concrete cryptographic implementation. -/
def pureLeanSchnorr
    (verifyECDSA : StackElement → StackElement → ByteArray → Bool :=
      fun _ _ _ => false) : CryptoOracle :=
  pureLeanHashes verifyECDSA Bitcoin.Schnorr.verify

/-- Pointwise agreement with the abstract cryptographic boundary of `Eval`. -/
def RefinesModel (oracle : CryptoOracle) : Prop :=
  (∀ bytes, oracle.sha256 bytes = LeanMiniscript.Script.sha256 bytes) ∧
  (∀ bytes, oracle.hash256 bytes = LeanMiniscript.Script.hash256 bytes) ∧
  (∀ bytes, oracle.ripemd160 bytes = LeanMiniscript.Script.ripemd160 bytes) ∧
  (∀ bytes, oracle.hash160 bytes = LeanMiniscript.Script.hash160 bytes) ∧
  (∀ sig pubkey sigHash,
    oracle.checkSig sig pubkey sigHash =
      LeanMiniscript.Script.checkSig sig pubkey sigHash) ∧
  (∀ sig pubkey sigHash,
    oracle.checkSchnorrSig sig pubkey sigHash =
      LeanMiniscript.Script.checkSchnorrSig sig pubkey sigHash)

theorem model_refines : model.RefinesModel := by
  simp [RefinesModel, model]

end CryptoOracle

/-- Execute the modeled Script subset to a typed final result.

    The recursion follows the literal list tail for ordinary opcodes. A
    conditional recursively evaluates the selected branch segments and suffix;
    `ConditionalFrame.select_length_lt` supplies the strict decrease. -/
def evaluate (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    ExecResult :=
  match script with
  | [] => .success stack altStack
  | .pushData data :: rest =>
      evaluate oracle rest (data :: stack) altStack flags ctx
  | .pushNum value :: rest =>
      evaluate oracle rest (scriptNum value :: stack) altStack flags ctx
  | .op .OP_NOP :: rest =>
      evaluate oracle rest stack altStack flags ctx
  | .op .OP_IF :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if _minimal : minimalIfSatisfied flags ctx.sigVersion top then
            match _split : splitConditional rest with
            | none =>
                finishUnclosedConditional
                  (evaluate oracle
                    (selectUnclosedConditional rest (castToBool top)) stackRest
                    altStack flags ctx)
            | some frame =>
                evaluate oracle (frame.select (castToBool top)) stackRest
                  altStack flags ctx
          else
            .failure (minimalIfError ctx.sigVersion)
  | .op .OP_NOTIF :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if _minimal : minimalIfSatisfied flags ctx.sigVersion top then
            match _split : splitConditional rest with
            | none =>
                finishUnclosedConditional
                  (evaluate oracle
                    (selectUnclosedConditional rest (!castToBool top)) stackRest
                    altStack flags ctx)
            | some frame =>
                evaluate oracle (frame.select (!castToBool top)) stackRest
                  altStack flags ctx
          else
            .failure (minimalIfError ctx.sigVersion)
  | .op .OP_ELSE :: _ => .failure .unbalancedConditional
  | .op .OP_ENDIF :: _ => .failure .unbalancedConditional
  | .op .OP_IFDUP :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if castToBool top then
            evaluate oracle rest (top :: top :: stackRest) altStack flags ctx
          else
            evaluate oracle rest (top :: stackRest) altStack flags ctx
  | .op .OP_DEPTH :: rest =>
      evaluate oracle rest (scriptNat stack.length :: stack) altStack flags ctx
  | .op .OP_DROP :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | _ :: stackRest =>
          evaluate oracle rest stackRest altStack flags ctx
  | .op .OP_DUP :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (top :: top :: stackRest) altStack flags ctx
  | .op .OP_NIP :: rest =>
      match stack with
      | top :: _ :: stackRest =>
          evaluate oracle rest (top :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_2DROP :: rest =>
      match stack with
      | _ :: _ :: stackRest =>
          evaluate oracle rest stackRest altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_2DUP :: rest =>
      match stack with
      | top :: below :: stackRest =>
          evaluate oracle rest (top :: below :: top :: below :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_3DUP :: rest =>
      match stack with
      | top :: second :: third :: stackRest =>
          evaluate oracle rest (top :: second :: third :: top :: second :: third :: stackRest)
            altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_2OVER :: rest =>
      match stack with
      | top :: second :: third :: fourth :: stackRest =>
          evaluate oracle rest (third :: fourth :: top :: second :: third :: fourth :: stackRest)
            altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_OVER :: rest =>
      match stack with
      | top :: below :: stackRest =>
          evaluate oracle rest (below :: top :: below :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_PICK :: rest =>
      match stack with
      | operand :: top :: stackRest =>
          match decodeStackIndex flags operand (top :: stackRest).length with
          | .error error => .failure error
          | .ok index =>
              evaluate oracle rest
                ((top :: stackRest)[index]?.getD ByteArray.empty :: (top :: stackRest))
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_ROLL :: rest =>
      match stack with
      | operand :: top :: stackRest =>
          match decodeStackIndex flags operand (top :: stackRest).length with
          | .error error => .failure error
          | .ok index =>
              evaluate oracle rest
                ((top :: stackRest)[index]?.getD ByteArray.empty :: (top :: stackRest).eraseIdx index)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_TUCK :: rest =>
      match stack with
      | top :: below :: stackRest =>
          evaluate oracle rest (top :: below :: top :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_ROT :: rest =>
      match stack with
      | top :: second :: third :: stackRest =>
          evaluate oracle rest (third :: top :: second :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_2ROT :: rest =>
      match stack with
      | top :: second :: third :: fourth :: fifth :: sixth :: stackRest =>
          evaluate oracle rest (fifth :: sixth :: top :: second :: third :: fourth :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_2SWAP :: rest =>
      match stack with
      | top :: second :: third :: fourth :: stackRest =>
          evaluate oracle rest (third :: fourth :: top :: second :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_SWAP :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          evaluate oracle rest (belowTop :: top :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_TOALTSTACK :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest stackRest (top :: altStack) flags ctx
  | .op .OP_FROMALTSTACK :: rest =>
      match altStack with
      | [] => .failure .altStackUnderflow
      | top :: altRest =>
          evaluate oracle rest (top :: stack) altRest flags ctx
  | .op .OP_1ADD :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (scriptNum (value + 1) :: stackRest) altStack flags ctx
  | .op .OP_1SUB :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (scriptNum (value - 1) :: stackRest) altStack flags ctx
  | .op .OP_NEGATE :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (scriptNum (-value) :: stackRest) altStack flags ctx
  | .op .OP_ABS :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (scriptNum (if value < 0 then -value else value) :: stackRest) altStack flags ctx
  | .op .OP_SUB :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (scriptNum (b - a) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_NUMNOTEQUAL :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (decide (a ≠ b)) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_LESSTHAN :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (decide (b < a)) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_GREATERTHAN :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (decide (b > a)) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_LESSTHANOREQUAL :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (decide (b ≤ a)) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_GREATERTHANOREQUAL :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (decide (b ≥ a)) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_MIN :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (scriptNum (min b a) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_MAX :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (scriptNum (max b a) :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_ADD :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (scriptNum (a + b) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_BOOLAND :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest
                (boolToElement ((a != 0) && (b != 0)) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_BOOLOR :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest
                (boolToElement ((a != 0) || (b != 0)) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_WITHIN :: rest =>
      match stack with
      | upperBytes :: lowerBytes :: valueBytes :: stackRest =>
          match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
          | .error error => .failure error
          | .ok (upper, lower, value) =>
              evaluate oracle rest
                (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_NOT :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData
              maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (boolToElement (value == 0) :: stackRest)
                altStack flags ctx
  | .op .OP_0NOTEQUAL :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData
              maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              evaluate oracle rest (boolToElement (value != 0) :: stackRest)
                altStack flags ctx
  | .op .OP_EQUAL :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          if top = belowTop then
            evaluate oracle rest (trueElement :: stackRest) altStack flags ctx
          else
            evaluate oracle rest (falseElement :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_EQUALVERIFY :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          if top = belowTop then
            evaluate oracle rest stackRest altStack flags ctx
          else
            .failure .equalVerify
      | _ => .failure .stackUnderflow
  | .op .OP_NUMEQUAL :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              evaluate oracle rest (boolToElement (a == b) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_NUMEQUALVERIFY :: rest =>
      match stack with
      | top :: belowTop :: stackRest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) =>
              if a = b then
                evaluate oracle rest stackRest altStack flags ctx
              else
                .failure .numEqualVerify
      | _ => .failure .stackUnderflow
  | .op .OP_SHA256 :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (oracle.sha256 top :: stackRest) altStack flags ctx
  | .op .OP_HASH256 :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (oracle.hash256 top :: stackRest) altStack flags ctx
  | .op .OP_RIPEMD160 :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (oracle.ripemd160 top :: stackRest) altStack flags ctx
  | .op .OP_HASH160 :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (oracle.hash160 top :: stackRest) altStack flags ctx
  | .op .OP_CHECKSIG :: rest =>
      match stack with
      | pubkey :: sig :: stackRest =>
          match checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig pubkey with
          | .error error => .failure error
          | .ok checked =>
              evaluate oracle rest (boolToElement checked :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_CHECKSIGVERIFY :: rest =>
      match stack with
      | pubkey :: sig :: stackRest =>
          match checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig pubkey with
          | .error error => .failure error
          | .ok true => evaluate oracle rest stackRest altStack flags ctx
          | .ok false => .failure .checkSigVerify
      | _ => .failure .stackUnderflow
  | .op .OP_CHECKSIGADD :: rest =>
      if ctx.sigVersion ≠ .tapscript then .failure .badOpcode
      else match stack with
      | pubkey :: countBytes :: sig :: stackRest =>
          match decodeCheckSigAddCount flags ctx countBytes with
          | .error error => .failure error
          | .ok count =>
              match checkSigWithEncoding oracle.checkSig oracle.checkSchnorrSig flags ctx sig pubkey with
              | .error error => .failure error
              | .ok checked =>
                  evaluate oracle rest (scriptNum (count + if checked then 1 else 0) :: stackRest)
                    altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_CHECKMULTISIG :: rest =>
      match decodeCheckMultiSigOperandsFor flags ctx stack with
      | .error error => .failure error
      | .ok operands =>
          match checkMultiSigFor oracle.checkSig flags ctx
              operands.signatures operands.pubkeys with
          | .error error => .failure error
          | .ok checked =>
              if _allowed : checked = true ∨ nullFailSatisfied flags operands.signatures then
                match checkMultiSigDummy flags operands.dummy with
                | .error error => .failure error
                | .ok () =>
                    evaluate oracle rest (boolToElement checked :: operands.rest)
                      altStack flags ctx
              else
                .failure .sigNullFail
  | .op .OP_CHECKMULTISIGVERIFY :: rest =>
      match decodeCheckMultiSigOperandsFor flags ctx stack with
      | .error error => .failure error
      | .ok operands =>
          match checkMultiSigFor oracle.checkSig flags ctx
              operands.signatures operands.pubkeys with
          | .error error => .failure error
          | .ok checked =>
              if _allowed : checked = true ∨ nullFailSatisfied flags operands.signatures then
                match checkMultiSigDummy flags operands.dummy with
                | .error error => .failure error
                | .ok () =>
                    if checked then
                      evaluate oracle rest operands.rest altStack flags ctx
                    else
                      .failure .checkMultiSigVerify
              else
                .failure .sigNullFail
  | .op .OP_CHECKSEQUENCEVERIFY :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData
              maxTimelockScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              if value < 0 then
                .failure .negativeLocktime
              else if sequenceSatisfied value.toNat ctx then
                evaluate oracle rest (operand :: stackRest) altStack flags ctx
              else
                .failure .checkSequenceVerify
  | .op .OP_CHECKLOCKTIMEVERIFY :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: stackRest =>
          match decodeScriptNum operand flags.minimalData
              maxTimelockScriptNumBytes with
          | .error error => .failure error
          | .ok value =>
              if value < 0 then
                .failure .negativeLocktime
              else if locktimeSatisfied value.toNat ctx then
                evaluate oracle rest (operand :: stackRest) altStack flags ctx
              else
                .failure .checkLockTimeVerify
  | .op .OP_VERIFY :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if castToBool top then
            evaluate oracle rest stackRest altStack flags ctx
          else
            .failure .verify
  | .op .OP_SIZE :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (scriptNat top.size :: top :: stackRest)
            altStack flags ctx
termination_by script.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | have smaller := ConditionalFrame.select_length_lt _split (castToBool top)
      omega
    | have smaller := ConditionalFrame.select_length_lt _split (!castToBool top)
      omega
    | have smaller := selectUnclosedConditional_length_le rest (castToBool top)
      omega
    | have smaller := selectUnclosedConditional_length_le rest (!castToBool top)
      omega

/-- DEPTH pushes the main-stack length before continuing, for every oracle,
    flag set and transaction context. Existing stack elements retain their order. -/
theorem evaluate_depth_cons (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (.op .OP_DEPTH :: script) stack altStack flags ctx =
      evaluate oracle script (scriptNat stack.length :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact result of DEPTH includes the unchanged alternate stack. This is
    the resource-free evaluator; runtime stack limits are checked separately. -/
theorem evaluate_depth (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_DEPTH] stack altStack flags ctx =
      .success (scriptNat stack.length :: stack) altStack := by
  simp [evaluate]

/-- Dropping any byte vector preserves the continuation result and alternate
    stack, without decoding the dropped value or consulting the oracle. -/
theorem evaluate_drop_cons (oracle : CryptoOracle) (script : Script)
    (top : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_DROP :: script) (top :: stack) altStack flags ctx =
      evaluate oracle script stack altStack flags ctx := by
  simp [evaluate]

/-- An empty main stack fails before the continuation, regardless of alt stack. -/
theorem evaluate_drop_nil (oracle : CryptoOracle) (script : Script)
    (altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (.op .OP_DROP :: script) [] altStack flags ctx =
      .failure .stackUnderflow := by
  simp [evaluate]

/-- NIP passes the unchanged top item and lower stack to the continuation. -/
theorem evaluate_nip_cons (oracle : CryptoOracle) (script : Script)
    (top discarded : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_NIP :: script) (top :: discarded :: stack) altStack flags ctx =
      evaluate oracle script (top :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Zero or one main-stack item causes underflow before the suffix executes. -/
theorem evaluate_nip_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 2) :
    evaluate oracle (.op .OP_NIP :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete NIP result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_nip (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_NIP] stack altStack flags ctx =
      match stack with
      | top :: _ :: rest => .success (top :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩ <;> simp [evaluate]

/-- 2DROP passes the lower stack unchanged to the continuation. -/
theorem evaluate_twoDrop_cons (oracle : CryptoOracle) (script : Script)
    (top discarded : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_2DROP :: script) (top :: discarded :: stack) altStack flags ctx =
      evaluate oracle script stack altStack flags ctx := by
  simp [evaluate]

/-- Zero or one main-stack item causes underflow before the suffix executes. -/
theorem evaluate_twoDrop_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 2) :
    evaluate oracle (.op .OP_2DROP :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 2DROP result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_twoDrop (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_2DROP] stack altStack flags ctx =
      match stack with
      | _ :: _ :: rest => .success rest altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨discarded, rest⟩⟩ <;> simp [evaluate]

/-- 2DUP prepends an exact copy of the top pair before the continuation. -/
theorem evaluate_twoDup_cons (oracle : CryptoOracle) (script : Script)
    (top below : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_2DUP :: script) (top :: below :: stack) altStack flags ctx =
      evaluate oracle script (top :: below :: top :: below :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Zero or one main-stack item causes underflow before the suffix executes. -/
theorem evaluate_twoDup_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 2) :
    evaluate oracle (.op .OP_2DUP :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 2DUP result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_twoDup (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_2DUP] stack altStack flags ctx =
      match stack with
      | top :: below :: rest => .success (top :: below :: top :: below :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩ <;> simp [evaluate]

/-- 3DUP prepends an exact copy of the top three items before the continuation. -/
theorem evaluate_threeDup_cons (oracle : CryptoOracle) (script : Script)
    (top second third : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_3DUP :: script) (top :: second :: third :: stack)
        altStack flags ctx =
      evaluate oracle script (top :: second :: third :: top :: second :: third :: stack)
        altStack flags ctx := by
  simp [evaluate]

/-- Fewer than three main-stack items cause underflow before the suffix executes. -/
theorem evaluate_threeDup_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 3) :
    evaluate oracle (.op .OP_3DUP :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 3DUP result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_threeDup (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_3DUP] stack altStack flags ctx =
      match stack with
      | top :: second :: third :: rest =>
          .success (top :: second :: third :: top :: second :: third :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> simp [evaluate]

/-- 2OVER prepends copies of the third and fourth items before the continuation. -/
theorem evaluate_twoOver_cons (oracle : CryptoOracle) (script : Script)
    (top second third fourth : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_2OVER :: script) (top :: second :: third :: fourth :: stack)
        altStack flags ctx =
      evaluate oracle script (third :: fourth :: top :: second :: third :: fourth :: stack)
        altStack flags ctx := by
  simp [evaluate]

/-- Fewer than four main-stack items cause underflow before the suffix executes. -/
theorem evaluate_twoOver_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 4) :
    evaluate oracle (.op .OP_2OVER :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 2OVER result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_twoOver (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_2OVER] stack altStack flags ctx =
      match stack with
      | top :: second :: third :: fourth :: rest =>
          .success (third :: fourth :: top :: second :: third :: fourth :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;> simp [evaluate]

/-- OVER prepends an exact copy of the second item before the continuation. -/
theorem evaluate_over_cons (oracle : CryptoOracle) (script : Script)
    (top below : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_OVER :: script) (top :: below :: stack) altStack flags ctx =
      evaluate oracle script (below :: top :: below :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Zero or one main-stack item causes underflow before the suffix executes. -/
theorem evaluate_over_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 2) :
    evaluate oracle (.op .OP_OVER :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete OVER result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_over (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_OVER] stack altStack flags ctx =
      match stack with
      | top :: below :: rest => .success (below :: top :: below :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩ <;> simp [evaluate]

/-- TUCK inserts a copy of the top item beneath the top two before the continuation. -/
theorem evaluate_tuck_cons (oracle : CryptoOracle) (script : Script)
    (top below : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_TUCK :: script) (top :: below :: stack) altStack flags ctx =
      evaluate oracle script (top :: below :: top :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Zero or one main-stack item causes underflow before the suffix executes. -/
theorem evaluate_tuck_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 2) :
    evaluate oracle (.op .OP_TUCK :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete TUCK result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_tuck (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_TUCK] stack altStack flags ctx =
      match stack with
      | top :: below :: rest => .success (top :: below :: top :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨below, rest⟩⟩ <;> simp [evaluate]

/-- ROT moves the third item above the top two before any continuation. -/
theorem evaluate_rot_cons (oracle : CryptoOracle) (script : Script)
    (top second third : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_ROT :: script) (top :: second :: third :: stack) altStack flags ctx =
      evaluate oracle script (third :: top :: second :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Fewer than three main-stack items cause underflow before the suffix executes. -/
theorem evaluate_rot_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 3) :
    evaluate oracle (.op .OP_ROT :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete ROT result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_rot (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_ROT] stack altStack flags ctx =
      match stack with
      | top :: second :: third :: rest => .success (third :: top :: second :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> simp [evaluate]

/-- 2ROT moves the fifth and sixth items above the top four before any continuation. -/
theorem evaluate_twoRot_cons (oracle : CryptoOracle) (script : Script)
    (top second third fourth fifth sixth : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_2ROT :: script) (top :: second :: third :: fourth :: fifth :: sixth :: stack) altStack flags ctx =
      evaluate oracle script (fifth :: sixth :: top :: second :: third :: fourth :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Fewer than six main-stack items cause underflow before the suffix executes. -/
theorem evaluate_twoRot_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 6) :
    evaluate oracle (.op .OP_2ROT :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 2ROT result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_twoRot (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_2ROT] stack altStack flags ctx =
      match stack with
      | top :: second :: third :: fourth :: fifth :: sixth :: rest => .success (fifth :: sixth :: top :: second :: third :: fourth :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩ <;> simp [evaluate]

/-- 2SWAP exchanges the top two pairs before any continuation. -/
theorem evaluate_twoSwap_cons (oracle : CryptoOracle) (script : Script)
    (top second third fourth : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_2SWAP :: script) (top :: second :: third :: fourth :: stack) altStack flags ctx =
      evaluate oracle script (third :: fourth :: top :: second :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Fewer than four main-stack items cause underflow before the suffix executes. -/
theorem evaluate_twoSwap_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 4) :
    evaluate oracle (.op .OP_2SWAP :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- The complete 2SWAP result for arbitrary stacks, flags, context and oracle. -/
theorem evaluate_twoSwap (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_2SWAP] stack altStack flags ctx =
      match stack with
      | top :: second :: third :: fourth :: rest => .success (third :: fourth :: top :: second :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;> simp [evaluate]

/-- NOT decodes one Script number and passes a canonical boolean to the
    continuation. The four-byte and minimal-data checks precede that continuation. -/
theorem evaluate_not_cons (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_NOT :: script) (operand :: stack) altStack flags ctx =
      match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
      | .error error => .failure error
      | .ok value => evaluate oracle script (boolToElement (value == 0) :: stack)
          altStack flags ctx := by
  simp [evaluate]

/-- Successful decoding replaces just the operand for every continuation and oracle. -/
theorem evaluate_not_of_decode (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (value : Int) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) :
    evaluate oracle (.op .OP_NOT :: script) (operand :: stack) altStack flags ctx =
      evaluate oracle script (boolToElement (value == 0) :: stack) altStack flags ctx := by
  rw [evaluate_not_cons, decoded]

/-- Empty-main-stack failure precedes the continuation for every alternate stack. -/
theorem evaluate_not_nil (oracle : CryptoOracle) (script : Script)
    (altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (.op .OP_NOT :: script) [] altStack flags ctx =
      .failure .stackUnderflow := by
  simp [evaluate]

/-- A numeric decoder error is the terminal NOT result. -/
theorem evaluate_not_decode_failure (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) (error : ScriptError)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .error error) :
    evaluate oracle (.op .OP_NOT :: script) (operand :: stack) altStack flags ctx =
      .failure error := by
  rw [evaluate_not_cons, decoded]

/-- The complete single-NOT result, including underflow and numeric errors,
    holds for arbitrary stacks, flags, transaction context and oracle. -/
theorem evaluate_not (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_NOT] stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value => .success (boolToElement (value == 0) :: rest) altStack := by
  cases stack <;> simp [evaluate]

/-- WITHIN consumes the top-first triple (upper, lower, value), decodes value
    first, and passes one canonical half-open interval test to the continuation. -/
theorem evaluate_within_cons (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx =
      match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
      | .error error => .failure error
      | .ok (upper, lower, value) => evaluate oracle script
          (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- Three successful numeric decodings determine the exact continuation result. -/
theorem evaluate_within_of_decode (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (upper lower value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (valueDecoded : decodeScriptNum valueBytes flags.minimalData maxArithmeticScriptNumBytes =
      .ok value)
    (lowerDecoded : decodeScriptNum lowerBytes flags.minimalData maxArithmeticScriptNumBytes =
      .ok lower)
    (upperDecoded : decodeScriptNum upperBytes flags.minimalData maxArithmeticScriptNumBytes =
      .ok upper) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx =
      evaluate oracle script (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack)
        altStack flags ctx := by
  simp [evaluate_within_cons, decodeWithinScriptNums, valueDecoded, lowerDecoded, upperDecoded]
  rfl

/-- All three inputs are required before any numeric decode or continuation. -/
theorem evaluate_within_underflow (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (short : stack.length < 3) :
    evaluate oracle (.op .OP_WITHIN :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨upper, _ | ⟨lower, _ | ⟨value, rest⟩⟩⟩
  all_goals simp_all [evaluate]
  omega

/-- A WITHIN decoder error terminates execution before the suffix. -/
theorem evaluate_within_decode_failure (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .error error) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx = .failure error := by
  rw [evaluate_within_cons, decoded]

/-- The value decoder error wins over both bounds and the suffix. -/
theorem evaluate_within_value_failure (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (failed : decodeScriptNum valueBytes flags.minimalData maxArithmeticScriptNumBytes =
      .error error) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx = .failure error := by
  apply evaluate_within_decode_failure
  simp [decodeWithinScriptNums, failed]
  rfl

/-- After a valid value, a lower-bound decoder error wins over the upper bound. -/
theorem evaluate_within_lower_failure (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (value : Int) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (decoded : decodeScriptNum valueBytes flags.minimalData maxArithmeticScriptNumBytes = .ok value)
    (failed : decodeScriptNum lowerBytes flags.minimalData maxArithmeticScriptNumBytes =
      .error error) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx = .failure error := by
  apply evaluate_within_decode_failure
  simp [decodeWithinScriptNums, decoded, failed]
  rfl

/-- The upper bound is decoded after the value and lower bound, even if the
    already-decoded value lies below the lower bound. Its error stops the suffix. -/
theorem evaluate_within_upper_failure (oracle : CryptoOracle) (script : Script)
    (upperBytes lowerBytes valueBytes : StackElement) (lower value : Int) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (valueDecoded : decodeScriptNum valueBytes flags.minimalData maxArithmeticScriptNumBytes =
      .ok value)
    (lowerDecoded : decodeScriptNum lowerBytes flags.minimalData maxArithmeticScriptNumBytes =
      .ok lower)
    (failed : decodeScriptNum upperBytes flags.minimalData maxArithmeticScriptNumBytes =
      .error error) :
    evaluate oracle (.op .OP_WITHIN :: script)
        (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx = .failure error := by
  apply evaluate_within_decode_failure
  simp [decodeWithinScriptNums, valueDecoded, lowerDecoded, failed]
  rfl

/-- The complete resource-free WITHIN result for arbitrary stacks and oracle. -/
theorem evaluate_within (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_WITHIN] stack altStack flags ctx =
      match stack with
      | upperBytes :: lowerBytes :: valueBytes :: rest =>
          match decodeWithinScriptNums flags upperBytes lowerBytes valueBytes with
          | .error error => .failure error
          | .ok (upper, lower, value) =>
              .success (boolToElement (decide (lower ≤ value ∧ value < upper)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨upper, _ | ⟨lower, _ | ⟨value, rest⟩⟩⟩ <;> simp [evaluate]

/-- 1ADD decodes its input before evaluating the continuation. -/
theorem evaluate_oneAdd_cons (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_1ADD :: script) (operand :: stack) altStack flags ctx =
      match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
      | .error error => .failure error
      | .ok value => evaluate oracle script (scriptNum (value + 1) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_oneAdd (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_1ADD] stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value => .success (scriptNum (value + 1) :: rest) altStack := by
  cases stack <;> simp [evaluate]

/-- 1SUB decodes its input before evaluating the continuation. -/
theorem evaluate_oneSub_cons (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_1SUB :: script) (operand :: stack) altStack flags ctx =
      match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
      | .error error => .failure error
      | .ok value => evaluate oracle script (scriptNum (value - 1) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_oneSub (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_1SUB] stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value => .success (scriptNum (value - 1) :: rest) altStack := by
  cases stack <;> simp [evaluate]

/-- NEGATE decodes its input before evaluating the continuation. -/
theorem evaluate_negate_cons (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_NEGATE :: script) (operand :: stack) altStack flags ctx =
      match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
      | .error error => .failure error
      | .ok value => evaluate oracle script (scriptNum (-value) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_negate (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_NEGATE] stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value => .success (scriptNum (-value) :: rest) altStack := by
  cases stack <;> simp [evaluate]

/-- ABS decodes its input before evaluating the continuation. -/
theorem evaluate_abs_cons (oracle : CryptoOracle) (script : Script)
    (operand : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_ABS :: script) (operand :: stack) altStack flags ctx =
      match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
      | .error error => .failure error
      | .ok value => evaluate oracle script (scriptNum (if value < 0 then -value else value) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_abs (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_ABS] stack altStack flags ctx =
      match stack with
      | [] => .failure .stackUnderflow
      | operand :: rest =>
          match decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok value => .success (scriptNum (if value < 0 then -value else value) :: rest) altStack := by
  cases stack <;> simp [evaluate]

/-- SUB decodes the below-top operand before the top operand. -/
theorem evaluate_sub_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_SUB :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (scriptNum (b - a) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_sub (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_SUB] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (scriptNum (b - a) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- NUMNOTEQUAL decodes the below-top operand before the top operand. -/
theorem evaluate_numNotEqual_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_NUMNOTEQUAL :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (boolToElement (decide (a ≠ b)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_numNotEqual (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_NUMNOTEQUAL] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (boolToElement (decide (a ≠ b)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- LESSTHAN decodes the below-top operand before the top operand. -/
theorem evaluate_lessThan_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_LESSTHAN :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (boolToElement (decide (b < a)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_lessThan (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_LESSTHAN] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (boolToElement (decide (b < a)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- GREATERTHAN decodes the below-top operand before the top operand. -/
theorem evaluate_greaterThan_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_GREATERTHAN :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (boolToElement (decide (b > a)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_greaterThan (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_GREATERTHAN] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (boolToElement (decide (b > a)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- LESSTHANOREQUAL decodes the below-top operand before the top operand. -/
theorem evaluate_lessThanOrEqual_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_LESSTHANOREQUAL :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (boolToElement (decide (b ≤ a)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_lessThanOrEqual (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_LESSTHANOREQUAL] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (boolToElement (decide (b ≤ a)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- GREATERTHANOREQUAL decodes the below-top operand before the top operand. -/
theorem evaluate_greaterThanOrEqual_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_GREATERTHANOREQUAL :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (boolToElement (decide (b ≥ a)) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_greaterThanOrEqual (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_GREATERTHANOREQUAL] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (boolToElement (decide (b ≥ a)) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- MIN replaces two decoded operands with their canonical result before the suffix. -/
theorem evaluate_min_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_MIN :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (scriptNum (min b a) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_min (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_MIN] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (scriptNum (min b a) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- MAX replaces two decoded operands with their canonical result before the suffix. -/
theorem evaluate_max_cons (oracle : CryptoOracle) (script : Script)
    (top belowTop : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_MAX :: script) (top :: belowTop :: stack) altStack flags ctx =
      match decodeBinaryScriptNums flags top belowTop with
      | .error error => .failure error
      | .ok (a, b) => evaluate oracle script (scriptNum (max b a) :: stack) altStack flags ctx := by
  simp [evaluate]

/-- The exact single-instruction result includes underflow and decode failure. -/
theorem evaluate_max (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_MAX] stack altStack flags ctx =
      match stack with
      | top :: belowTop :: rest =>
          match decodeBinaryScriptNums flags top belowTop with
          | .error error => .failure error
          | .ok (a, b) => .success (scriptNum (max b a) :: rest) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩ <;> simp [evaluate]

/-- PICK consumes a valid depth and passes its resulting stack to the suffix. -/
theorem evaluate_pick_cons (oracle : CryptoOracle) (script : Script)
    (operand top : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_PICK :: script) (operand :: top :: stack) altStack flags ctx =
      match decodeStackIndex flags operand (top :: stack).length with
      | .error error => .failure error
      | .ok index => evaluate oracle script
          ((top :: stack)[index]?.getD ByteArray.empty :: (top :: stack)) altStack flags ctx := by
  simp [evaluate]

/-- The exact PICK result includes arity, numeric decoding, and depth errors. -/
theorem evaluate_pick (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_PICK] stack altStack flags ctx =
      match stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .failure error
          | .ok index => .success
              ((top :: rest)[index]?.getD ByteArray.empty :: (top :: rest)) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩ <;> simp [evaluate]

/-- ROLL consumes a valid depth and passes its resulting stack to the suffix. -/
theorem evaluate_roll_cons (oracle : CryptoOracle) (script : Script)
    (operand top : StackElement) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    evaluate oracle (.op .OP_ROLL :: script) (operand :: top :: stack) altStack flags ctx =
      match decodeStackIndex flags operand (top :: stack).length with
      | .error error => .failure error
      | .ok index => evaluate oracle script
          ((top :: stack)[index]?.getD ByteArray.empty :: (top :: stack).eraseIdx index) altStack flags ctx := by
  simp [evaluate]

/-- The exact ROLL result includes arity, numeric decoding, and depth errors. -/
theorem evaluate_roll (oracle : CryptoOracle) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    evaluate oracle [.op .OP_ROLL] stack altStack flags ctx =
      match stack with
      | operand :: top :: rest =>
          match decodeStackIndex flags operand (top :: rest).length with
          | .error error => .failure error
          | .ok index => .success
              ((top :: rest)[index]?.getD ByteArray.empty :: (top :: rest).eraseIdx index) altStack
      | _ => .failure .stackUnderflow := by
  rcases stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩ <;> simp [evaluate]

/-- PICK and ROLL check for an index and a selectable item before decoding. -/
theorem evaluate_stackIndex_underflow (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (indexed : opcode.usesStackIndex = true) (short : stack.length < 2) :
    evaluate oracle (.op opcode :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨operand, _ | ⟨top, rest⟩⟩
  all_goals try { simp at short; omega }
  all_goals cases opcode <;> simp_all [Opcode.usesStackIndex, evaluate]

/-- Numeric or depth errors terminate indexed stack operations before their suffix. -/
theorem evaluate_stackIndex_decode_failure (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (operand top : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (indexed : opcode.usesStackIndex = true)
    (decoded : decodeStackIndex flags operand (top :: stack).length = .error error) :
    evaluate oracle (.op opcode :: script) (operand :: top :: stack) altStack flags ctx =
      .failure error := by
  cases opcode <;> simp_all [Opcode.usesStackIndex, evaluate]

/-- Unary arithmetic checks its fixed arity before decoding or evaluating the suffix. -/
theorem evaluate_unaryArithmetic_underflow (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (unary : opcode.usesUnaryArithmetic = true) :
    evaluate oracle (.op opcode :: script) [] altStack flags ctx = .failure .stackUnderflow := by
  cases opcode <;> simp_all [Opcode.usesUnaryArithmetic, evaluate]

/-- A unary arithmetic decode error takes precedence over every continuation. -/
theorem evaluate_unaryArithmetic_decode_failure (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (operand : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (unary : opcode.usesUnaryArithmetic = true)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .error error) :
    evaluate oracle (.op opcode :: script) (operand :: stack) altStack flags ctx =
      .failure error := by
  cases opcode <;> simp_all [Opcode.usesUnaryArithmetic, evaluate]

/-- Every binary Script-number opcode checks both inputs before decoding either. -/
theorem evaluate_binaryScriptNums_underflow (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (binary : opcode.usesBinaryScriptNums = true) (short : stack.length < 2) :
    evaluate oracle (.op opcode :: script) stack altStack flags ctx =
      .failure .stackUnderflow := by
  rcases stack with _ | ⟨top, _ | ⟨belowTop, rest⟩⟩
  all_goals try { simp at short; omega }
  all_goals cases opcode <;> simp_all [Opcode.usesBinaryScriptNums, evaluate]

/-- Binary numeric decode failure takes precedence over every continuation. -/
theorem evaluate_binaryScriptNums_decode_failure (oracle : CryptoOracle) (opcode : Opcode)
    (script : Script) (top belowTop : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (error : ScriptError)
    (binary : opcode.usesBinaryScriptNums = true)
    (decoded : decodeBinaryScriptNums flags top belowTop = .error error) :
    evaluate oracle (.op opcode :: script) (top :: belowTop :: stack) altStack flags ctx =
      .failure error := by
  cases opcode <;> simp_all [Opcode.usesBinaryScriptNums, evaluate]

/-- An oracle agreeing with the abstract model computes the result of every
    relational `Eval` derivation. -/
theorem evaluate_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (evaluated : Eval script stack altStack flags ctx result) :
    evaluate oracle script stack altStack flags ctx = result := by
  have verifier : oracle.checkSig = LeanMiniscript.Script.checkSig :=
    funext fun sig => funext fun pubkey => funext fun hash =>
      agreement.2.2.2.2.1 sig pubkey hash
  have schnorrVerifier : oracle.checkSchnorrSig = LeanMiniscript.Script.checkSchnorrSig :=
    funext fun sig => funext fun pubkey => funext fun hash =>
      agreement.2.2.2.2.2 sig pubkey hash
  induction evaluated <;>
    simp_all [evaluate, CryptoOracle.RefinesModel,
      Opcode.activeFixedMainStackInputs?, Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesUnaryArithmetic, Opcode.usesStackIndex, Opcode.usesTimelockScriptNum, minimalIfSatisfied,
      boolToElement, decodeCheckSigAddCount] <;>
    try omega <;>
    try grind
  case stack_underflow =>
    rename_i opcode required rest stack alt flags ctx arity underflow
    cases opcode <;> cases stack <;>
      simp_all [evaluate] <;>
      try omega
    all_goals
      rename_i top stackTail
      cases stackTail <;> simp_all [evaluate] <;> try omega
    all_goals
      rename_i belowTop stackTail
      cases stackTail <;> simp_all [evaluate] <;> try omega
    all_goals
      rename_i third stackTail
      rcases stackTail with _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, tail⟩⟩⟩ <;>
        simp_all [evaluate] <;> omega
  case checksigadd_unavailable =>
    rename_i stack rest alt flags ctx unavailable
    cases stack <;> try simp_all [evaluate]
    rename_i pubkey tail
    cases tail <;> try simp_all [evaluate]
    rename_i countBytes tail
    cases tail <;> try simp_all [evaluate]
  case checksigadd_success =>
    split <;> simp_all
  case checksigadd_failure =>
    split <;> simp_all
  case checksigadd_encoding_failure =>
    split <;> simp_all
  case unaryArithmetic_scriptnum_failure =>
    rename_i opcode operand stackRest rest alt flags ctx error uses decoded
    cases opcode <;>
      simp_all only [Bool.false_eq_true]
    all_goals
      simp only [evaluate]
      rw [decoded]
  case stackindex_failure =>
    rename_i opcode operand top stackRest rest alt flags ctx error uses decoded
    cases opcode <;>
      simp_all only [Bool.false_eq_true]
    all_goals
      simp only [evaluate, List.length_cons, decoded]
  case binary_scriptnum_failure =>
    rename_i opcode top belowTop stackRest rest alt flags ctx error uses decoded
    cases opcode <;>
      simp_all only [Bool.false_eq_true]
    all_goals
      simp only [evaluate]
      rw [decoded]
  case timelock_scriptnum_failure =>
    rename_i opcode operand stackRest rest alt flags ctx error uses decoded
    cases opcode <;>
      simp_all only [Bool.false_eq_true]
    all_goals
      simp only [evaluate]
      rw [decoded]
  case timelock_negative_failure =>
    rename_i opcode operand value stackRest rest alt flags ctx uses decoded negative
    cases opcode <;>
      simp_all only [Bool.false_eq_true]
    all_goals
      simp only [evaluate]
      rw [decoded]
      simp [negative]
  case if_execute =>
    rename_i top stackRest alt rest frame flags ctx result split minimal next ih
    split <;> simp_all
  case notif_execute =>
    rename_i top stackRest alt rest frame flags ctx result split minimal next ih
    split <;> simp_all
  case if_unbalanced =>
    rename_i top stackRest alt rest flags ctx selectedResult split minimal next ih
    split <;> simp_all
  case notif_unbalanced =>
    rename_i top stackRest alt rest flags ctx selectedResult split minimal next ih
    split <;> simp_all

/-- The evaluator is sound for every oracle that agrees with the cryptographic
    boundary used by the relational semantics. -/
theorem evaluate_sound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) :
    Eval script stack altStack flags ctx
      (evaluate oracle script stack altStack flags ctx) := by
  rcases Eval.exists_result script stack altStack flags ctx with
    ⟨result, evaluated⟩
  rw [evaluate_eq_of_eval agreement evaluated]
  exact evaluated

/-- The model oracle's computed result is the unique relational result. -/
theorem evaluate_model_iff
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult} :
    Eval script stack altStack flags ctx result ↔
      evaluate CryptoOracle.model script stack altStack flags ctx = result := by
  constructor
  · exact evaluate_eq_of_eval CryptoOracle.model_refines
  · intro computed
    rw [← computed]
    exact evaluate_sound CryptoOracle.model_refines script stack altStack flags ctx

end LeanMiniscript.Script
