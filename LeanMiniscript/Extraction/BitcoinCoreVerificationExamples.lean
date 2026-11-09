import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Extraction.BitcoinCoreFixtures
import LeanMiniscript.Extraction.ScriptEquivalence

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

private def raw (source : String) : ByteArray :=
  (coreScriptSourceBytes source).toOption.getD ByteArray.empty

private def plainFlags : CoreVerificationFlags :=
  { script := {
      minimalIf := false
      minimalData := false
      nullDummy := false
      nullFail := false
      strictEncoding := false
      checkLockTimeVerify := false
      checkSequenceVerify := false } }

private def fixtureRun (sig pub : ByteArray) (flags : CoreVerificationFlags := plainFlags)
    (witness : List ByteArray := []) : Except CoreVerificationError Unit :=
  let fixture := coreFixtureTransaction sig pub 0
  let execute := executeCoreFixtureScript fixture flags
  verifyCoreScripts execute
    (fun witness version program isP2SH => verifyCoreWitnessProgram execute flags witness
      version program isP2SH (checkCoreFixtureKeyPath fixture)) flags sig pub witness

-- The typed reader reads SHA1 as the modeled opcode.
example : (match decodeTypedScript? ⟨#[0xa7]⟩ with
    | some [.op .OP_SHA1] => true
    | _ => false) = true := by
  native_decide

-- The typed reader keeps the opcode of a push that is not minimal.
example : (match decodeTypedScript? (raw "0x01 0x05") with
    | some [.nonminimalPush push] => push.opcode == 0x01 && push.data == ⟨#[0x05]⟩
    | _ => false) = true := by
  native_decide

private def typedRun (source : String) (minimalData : Bool) :
    Except CoreVerificationError Stack :=
  executeTypedScript { plainFlags with script := { plainFlags.script with minimalData } }
    coreFixtureTxContext (fun _ _ => CryptoOracle.pureLeanHashes (fun _ _ _ => false))
    { scriptBytes := raw source, sigVersion := .base }

-- MINIMALDATA rejects it only in an executed branch.
example : typedRun "0x01 0x05" false = .ok [⟨#[0x05]⟩] ∧
    typedRun "0x01 0x05" true = .error (.script .minimalData) ∧
    typedRun "0 IF 0x01 0x05 ENDIF 1" true = .ok [⟨#[0x01]⟩] := by
  native_decide

-- The typed reader reads a push GetOp cannot read as a `truncatedPush` of the
-- bytes from it to the end.
example : (match decodeTypedScript? ⟨#[0x01]⟩, decodeTypedScript? (raw "1 0x4d 0x0200 0x00") with
    | some [.truncatedPush push], some [.pushNum 1, .truncatedPush rest] =>
        push.bytes == ⟨#[0x01]⟩ && rest.bytes == ⟨#[0x4d, 0x02, 0x00, 0x00]⟩
    | _, _ => false) = true := by
  native_decide

-- Every script of one or two bytes that GetOp cannot read from its start, and
-- OP_PUSHDATA1, 2, or 4 followed by one to four 0xff bytes, has a typed reading.
example : ((List.range 256).flatMap (fun first =>
      ByteArray.mk #[first.toUInt8] :: (List.range 256).map fun second =>
        ByteArray.mk #[first.toUInt8, second.toUInt8]) ++
      [0x4c, 0x4d, 0x4e].flatMap (fun opcode => (List.range 4).map fun count =>
        ByteArray.mk (#[opcode] ++ Array.replicate (count + 1) 0xff))).all
    (fun bytes => match readCoreRawInstruction bytes 0 with
      | .ok _ => true
      | .error _ => (decodeTypedScript? bytes).isSome) = true := by
  native_decide

private def typedRunBytes (bytes : ByteArray) : Except CoreVerificationError Stack :=
  executeTypedScript plainFlags coreFixtureTxContext
    (fun _ _ => CryptoOracle.pureLeanHashes (fun _ _ _ => false))
    { scriptBytes := bytes, sigVersion := .base }

-- A truncated push fails with BAD_OPCODE in an unexecuted branch, and after 201
-- operations, which it does not add to.
example : typedRun "0 IF 0x4c" false = .error (.script .badOpcode) ∧
    typedRunBytes ⟨Array.replicate 201 0x61 ++ #[0x4c]⟩ = .error (.script .badOpcode) ∧
    typedRunBytes ⟨Array.replicate 202 0x61⟩ = .error (.script .opCount) := by
  native_decide

-- Raw execution supports SHA1 in BASE, witness-v0 and Tapscript.
example : ([SignatureVersion.base, .witnessV0, .tapscript]).all (fun version =>
    (executeCoreFixtureScript (coreFixtureTransaction ByteArray.empty ByteArray.empty 0)
      plainFlags { scriptBytes := raw "'abc' SHA1", sigVersion := version }).toOption ==
      some [⟨#[0xa9,0x99,0x3e,0x36,0x47,0x06,0x81,0x6a,0xba,0x3e,
        0x25,0x71,0x78,0x50,0xc2,0x6c,0x9c,0xd0,0xd8,0x9d]⟩]) = true := by
  native_decide

example : fixtureRun ByteArray.empty (raw "SHA1") = .error (.script .stackUnderflow) := by
  native_decide

example : fixtureRun ByteArray.empty (raw "0 IF SHA1 ENDIF 1") = .ok () := by native_decide

-- Disabled timelocks are NOPs even with the discourage-upgradable-NOPs flag.
example : fixtureRun ByteArray.empty (raw "CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY 1")
    { plainFlags with script := { plainFlags.script with discourageUpgradableNops := true } } =
      .ok () := by native_decide

example : fixtureRun ByteArray.empty (raw "CHECKLOCKTIMEVERIFY 1")
    { plainFlags with script := { plainFlags.script with checkLockTimeVerify := true } } = .error (.script .stackUnderflow) := by
  native_decide

example : fixtureRun ByteArray.empty (raw "CHECKSEQUENCEVERIFY 1")
    { plainFlags with script := { plainFlags.script with checkSequenceVerify := true } } = .error (.script .stackUnderflow) := by
  native_decide

-- FindAndDelete removes matching complete byte strings only at opcode boundaries.
example : coreFindAndDelete (raw "0x01ab 0xab 0x4c01ab") (raw "0xab") =
    (raw "0x01ab 0x4c01ab", 1) := by native_decide

example : coreFindAndDelete (raw "0x0101 0x0101 0x020101") (raw "0x0101") =
    (raw "0x020101", 2) := by native_decide

example : coreFindAndDelete (raw "0xab 0x4d01") (raw "0xab") =
    (raw "0x4d01", 1) := by native_decide

example : coreSignaturePush ⟨#[1]⟩ = ⟨#[1, 1]⟩ ∧
    coreSignaturePush ByteArray.empty = ⟨#[0]⟩ := by native_decide

private def traceCode (source expected : String) (version : SignatureVersion) : Bool :=
  match executeCoreScript plainFlags coreFixtureTxContext
      (fun _ scriptCode => CryptoOracle.pureLeanHashes (fun _ _ _ => scriptCode == raw expected))
      { scriptBytes := raw source, sigVersion := version } with
  | .ok [top] => castToBool top
  | _ => false

example : traceCode "CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
    "0x01bb CHECKSIG" .base = true := by native_decide

example : traceCode "CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
    "0x01aa 0x01bb CHECKSIG" .witnessV0 = true := by native_decide

example : traceCode "0 IF CODESEPARATOR ENDIF 0x01aa 0x01bb CHECKSIG"
    "0 IF CODESEPARATOR ENDIF 0x01bb CHECKSIG" .base = true := by native_decide

example : traceCode "CODESEPARATOR 0x01aa DROP CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
    "0x01bb CHECKSIG" .base = true := by native_decide

-- The typed reader reads OP_CODESEPARATOR with the offset just past it.
example : (match decodeTypedScript? (raw "1 CODESEPARATOR 2") with
    | some [.pushNum 1, .codeSeparator nextOffset, .pushNum 2] => nextOffset == 2
    | _ => false) = true := by
  native_decide

private def typedTraceCode (source expected : String) (version : SignatureVersion) : Bool :=
  match executeTypedScript plainFlags coreFixtureTxContext
      (fun _ scriptCode => CryptoOracle.pureLeanHashes (fun _ _ _ => scriptCode == raw expected))
      { scriptBytes := raw source, sigVersion := version } with
  | .ok [top] => castToBool top
  | _ => false

-- The typed executor cuts the script code at an executed OP_CODESEPARATOR,
-- in witness v0 without FindAndDelete, and a skipped one cuts nothing.
example : typedTraceCode "CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
    "0x01bb CHECKSIG" .base = true ∧
    typedTraceCode "CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
      "0x01aa 0x01bb CHECKSIG" .witnessV0 = true ∧
    typedTraceCode "0 IF CODESEPARATOR ENDIF 0x01aa 0x01bb CHECKSIG"
      "0 IF CODESEPARATOR ENDIF 0x01bb CHECKSIG" .base = true ∧
    typedTraceCode "CODESEPARATOR 0x01aa DROP CODESEPARATOR 0x01aa 0x01bb CHECKSIG"
      "0x01bb CHECKSIG" .base = true := by
  native_decide

private def typedRunConst (source : String) : Except CoreVerificationError Stack :=
  executeTypedScript { plainFlags with script := { plainFlags.script with
      constScriptCode := true } }
    coreFixtureTxContext (fun _ _ => CryptoOracle.pureLeanHashes (fun _ _ _ => false))
    { scriptBytes := raw source, sigVersion := .base }

-- Under BASE CONST_SCRIPTCODE the typed executor fails with
-- OP_CODESEPARATOR, in an unexecuted branch as well.
example : typedRunConst "CODESEPARATOR 1" = .error .opCodeSeparator ∧
    typedRunConst "0 IF CODESEPARATOR ENDIF 1" = .error .opCodeSeparator := by
  native_decide

-- OP_CODESEPARATOR counts as an operation outside Tapscript.
example : typedRunBytes ⟨Array.replicate 201 0x61 ++ #[0xab]⟩ = .error (.script .opCount) ∧
    typedRunBytes ⟨Array.replicate 200 0x61 ++ #[0xab]⟩ = .ok [] := by
  native_decide

-- Multisig deletes all original signatures before any key matching callback.
example : traceCode "0 0x01aa 0x01cc 2 0x01dd 0x01ee 2 CHECKMULTISIG"
    "0 2 0x01dd 0x01ee 2 CHECKMULTISIG" .base = true := by native_decide

example : fixtureRun ByteArray.empty (raw "0 IF CODESEPARATOR ENDIF 1")
    { plainFlags with script := { plainFlags.script with constScriptCode := true } } =
    .error .opCodeSeparator := by native_decide

example : fixtureRun ByteArray.empty (raw "0x01aa 0x01bb CHECKSIG")
    { plainFlags with
      script := { plainFlags.script with strictEncoding := true, constScriptCode := true } } =
    .error (.script .sigFindAndDelete) := by native_decide

private def p2sh (redeem : ByteArray) : ByteArray :=
  ⟨#[0xa9, 0x14]⟩ ++ LeanHash160.hash160 redeem ++ ⟨#[0x87]⟩

example : coreScriptIsPushOnly (raw "0x50") = true ∧
    coreScriptIsPushOnly (raw "0x4d") = false := by native_decide

example : fixtureRun (raw "RETURN") (raw "1")
    { plainFlags with sigPushOnly := true } = .error .sigPushOnly := by native_decide

example : fixtureRun (coreSignaturePush (raw "1")) (p2sh (raw "1"))
    { plainFlags with p2sh := true } = .ok () := by native_decide

example : fixtureRun (coreSignaturePush (raw "0")) (p2sh (raw "0"))
    { plainFlags with p2sh := true } = .error (.script .evalFalse) := by native_decide

example : fixtureRun (raw "NOP" ++ coreSignaturePush (raw "1")) (p2sh (raw "1"))
    { plainFlags with p2sh := true } = .error .sigPushOnly := by native_decide

-- A false scriptPubKey fails before the P2SH-specific push-only check.
example : fixtureRun (raw "NOP" ++ coreSignaturePush (raw "0")) (p2sh (raw "1"))
    { plainFlags with p2sh := true } = .error (.script .evalFalse) := by native_decide

example : fixtureRun (coreSignaturePush (raw "FROMALTSTACK")) (p2sh (raw "FROMALTSTACK"))
    { plainFlags with p2sh := true } = .error (.script .altStackUnderflow) := by native_decide

example : fixtureRun (raw "1 1") (raw "1") { plainFlags with cleanStack := true } =
    .error (.script .cleanStack) := by native_decide

example : fixtureRun (raw "1") (raw "1 DROP") { plainFlags with cleanStack := true }
    [ByteArray.empty] = .error .witnessUnexpected := by native_decide

-- Each script boundary resets its operation counter and alternate stack.
example : fixtureRun (raw "1 TOALTSTACK") (raw "FROMALTSTACK") =
    .error (.script .altStackUnderflow) := by native_decide

example : fixtureRun (raw "RETURN") (raw "0x4d") = .error (.script .opReturn) := by
  native_decide

end LeanMiniscript.Extraction
