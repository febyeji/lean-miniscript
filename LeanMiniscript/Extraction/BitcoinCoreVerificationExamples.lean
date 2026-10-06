import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Extraction.BitcoinCoreFixtures

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

private instance : DecidableEq (Except CoreVerificationError Unit) := fun a b => by
  cases a <;> cases b
  · rename_i first second
    exact decidable_of_iff (first = second)
      ⟨fun same => congrArg Except.error same, Except.error.inj⟩
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue (by congr)

private def raw (source : String) : ByteArray :=
  (coreScriptSourceBytes source).toOption.getD ByteArray.empty

private def plainFlags : CoreVerificationFlags :=
  { script := {
      minimalIf := false
      minimalData := false
      nullDummy := false
      nullFail := false
      strictEncoding := false } }

private def fixtureRun (sig pub : ByteArray) (flags : CoreVerificationFlags := plainFlags)
    (witness : List ByteArray := []) : Except CoreVerificationError Unit :=
  let fixture := coreFixtureTransaction sig pub 0
  let execute := executeCoreFixtureScript fixture flags
  verifyCoreScripts execute
    (fun witness version program isP2SH => verifyCoreWitnessProgram execute flags witness
      version program isP2SH (checkCoreFixtureKeyPath fixture)) flags sig pub witness

-- Raw execution supports SHA1 in BASE, witness-v0 and Tapscript without adding
-- fixture-only opcodes to the shared typed Script model.
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
    { plainFlags with checkLockTimeVerify := true } = .error (.script .stackUnderflow) := by
  native_decide

example : fixtureRun ByteArray.empty (raw "CHECKSEQUENCEVERIFY 1")
    { plainFlags with checkSequenceVerify := true } = .error (.script .stackUnderflow) := by
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
  match executeCoreScript plainFlags
      { version := 1, locktime := 0, sequence := 0xffffffff, sigHash := ByteArray.empty }
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

-- Multisig deletes all original signatures before any key matching callback.
example : traceCode "0 0x01aa 0x01cc 2 0x01dd 0x01ee 2 CHECKMULTISIG"
    "0 2 0x01dd 0x01ee 2 CHECKMULTISIG" .base = true := by native_decide

example : fixtureRun ByteArray.empty (raw "0 IF CODESEPARATOR ENDIF 1")
    { plainFlags with constScriptCode := true } = .error .opCodeSeparator := by native_decide

example : fixtureRun ByteArray.empty (raw "0x01aa 0x01bb CHECKSIG")
    { plainFlags with
      constScriptCode := true
      script := { plainFlags.script with strictEncoding := true } } =
    .error .sigFindAndDelete := by native_decide

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
