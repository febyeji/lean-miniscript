import LeanMiniscript.Script.CryptoOracle
import LeanMiniscript.Script.Conditional

/-! Executable branch-projection Script evaluator. Refinement and opcode lemmas are in EvaluatorProofs. -/

namespace LeanMiniscript.Script

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
  | .op .OP_NOP1 :: rest | .op .OP_NOP4 :: rest | .op .OP_NOP5 :: rest |
      .op .OP_NOP6 :: rest | .op .OP_NOP7 :: rest | .op .OP_NOP8 :: rest |
      .op .OP_NOP9 :: rest | .op .OP_NOP10 :: rest =>
      if flags.discourageUpgradableNops then .failure .discourageUpgradableNops
      else evaluate oracle rest stack altStack flags ctx
  | .op .OP_RETURN :: _ => .failure .opReturn
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

end LeanMiniscript.Script
