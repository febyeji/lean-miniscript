import LeanHash160
import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-- Cryptographic operations needed by the executable Script evaluator.

    The model oracle below preserves the abstract functions used by `Eval`.
    Executable callers can instead use `pureLeanHashes`, supplying signature
    verification at the application boundary. -/
structure CryptoOracle where
  sha256 : StackElement → StackElement
  hash256 : StackElement → StackElement
  ripemd160 : StackElement → StackElement
  hash160 : StackElement → StackElement
  checkSig : StackElement → StackElement → ByteArray → Bool
  checkMultiSig : List StackElement → List StackElement → ByteArray → Bool

namespace CryptoOracle

/-- The oracle whose operations are definitionally the abstract cryptographic
    functions used by the relational big-step semantics. -/
def model : CryptoOracle where
  sha256 := LeanMiniscript.Script.sha256
  hash256 := LeanMiniscript.Script.hash256
  ripemd160 := LeanMiniscript.Script.ripemd160
  hash160 := LeanMiniscript.Script.hash160
  checkSig := LeanMiniscript.Script.checkSig
  checkMultiSig := LeanMiniscript.Script.checkMultiSig

/-- Executable pure-Lean hashes paired with caller-supplied signature checks.

    A production signature implementation can be supplied through an FFI
    without coupling the proof-facing evaluator to one native library. -/
def pureLeanHashes
    (verifySignature : StackElement → StackElement → ByteArray → Bool)
    (verifyMultiSignature :
      List StackElement → List StackElement → ByteArray → Bool) :
    CryptoOracle where
  sha256 := LeanHash160.SHA256.hash
  hash256 := fun bytes =>
    LeanHash160.SHA256.hash (LeanHash160.SHA256.hash bytes)
  ripemd160 := LeanHash160.RIPEMD160.hash
  hash160 := LeanHash160.hash160
  checkSig := verifySignature
  checkMultiSig := verifyMultiSignature

/-- Pointwise agreement with the abstract cryptographic boundary of `Eval`. -/
def RefinesModel (oracle : CryptoOracle) : Prop :=
  (∀ bytes, oracle.sha256 bytes = LeanMiniscript.Script.sha256 bytes) ∧
  (∀ bytes, oracle.hash256 bytes = LeanMiniscript.Script.hash256 bytes) ∧
  (∀ bytes, oracle.ripemd160 bytes = LeanMiniscript.Script.ripemd160 bytes) ∧
  (∀ bytes, oracle.hash160 bytes = LeanMiniscript.Script.hash160 bytes) ∧
  (∀ sig pubkey sigHash,
    oracle.checkSig sig pubkey sigHash =
      LeanMiniscript.Script.checkSig sig pubkey sigHash) ∧
  (∀ signatures pubkeys sigHash,
    oracle.checkMultiSig signatures pubkeys sigHash =
      LeanMiniscript.Script.checkMultiSig signatures pubkeys sigHash)

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
          if _minimal : minimalIfSatisfied flags top then
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
            .failure .minimalIf
  | .op .OP_NOTIF :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          if _minimal : minimalIfSatisfied flags top then
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
            .failure .minimalIf
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
  | .op .OP_DUP :: rest =>
      match stack with
      | [] => .failure .stackUnderflow
      | top :: stackRest =>
          evaluate oracle rest (top :: top :: stackRest) altStack flags ctx
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
          let checked := oracle.checkSig sig pubkey ctx.sigHash
          evaluate oracle rest (boolToElement checked :: stackRest) altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_CHECKSIGADD :: rest =>
      match stack with
      | pubkey :: countBytes :: sig :: stackRest =>
          match decodeScriptNum countBytes flags.minimalData
              maxArithmeticScriptNumBytes with
          | .error error => .failure error
          | .ok count =>
              let increment := if oracle.checkSig sig pubkey ctx.sigHash then 1 else 0
              evaluate oracle rest (scriptNum (count + increment) :: stackRest)
                altStack flags ctx
      | _ => .failure .stackUnderflow
  | .op .OP_CHECKMULTISIG :: rest =>
      match decodeCheckMultiSigOperands flags stack with
      | .error error => .failure error
      | .ok operands =>
          if _dummy : nullDummySatisfied flags operands.dummy then
            let checked := oracle.checkMultiSig operands.signatures
              operands.pubkeys ctx.sigHash
            evaluate oracle rest (boolToElement checked :: operands.rest)
              altStack flags ctx
          else
            .failure .nullDummy
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

/-- An oracle agreeing with the abstract model computes the result of every
    relational `Eval` derivation. -/
theorem evaluate_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack altStack : Stack} {flags : ScriptFlags}
    {ctx : TxContext} {result : ExecResult}
    (evaluated : Eval script stack altStack flags ctx result) :
    evaluate oracle script stack altStack flags ctx = result := by
  induction evaluated <;>
    simp_all [evaluate, CryptoOracle.RefinesModel,
      Opcode.fixedMainStackInputs?, Opcode.usesBinaryScriptNums,
      Opcode.usesTimelockScriptNum, minimalIfSatisfied,
      nullDummySatisfied, boolToElement] <;>
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
      cases stackTail <;> simp_all [evaluate] <;> omega
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
