import LeanMiniscript.Extraction.BitcoinCoreFixtures

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-!
# Pinned Bitcoin Core Script fixture regressions

The JSON rows below are copied verbatim from
`src/test/data/script_tests.json` at `bitcoinCoreScriptTestsCommit`. They form a
small offline suite for the currently modeled opcode and failure subset. The
importer retains every row and reports unsupported semantics rather than
silently dropping them.
-/

private def rejectingOracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun _sig _pubkey _sigHash => false)
    (fun _signatures _pubkeys _sigHash => false)

private def coreOpcodeNameFixtures : List (String × Opcode) :=
  [("IF", .OP_IF), ("NOTIF", .OP_NOTIF), ("ELSE", .OP_ELSE),
   ("ENDIF", .OP_ENDIF), ("IFDUP", .OP_IFDUP), ("DUP", .OP_DUP),
   ("SWAP", .OP_SWAP), ("TOALTSTACK", .OP_TOALTSTACK),
   ("FROMALTSTACK", .OP_FROMALTSTACK), ("ADD", .OP_ADD),
   ("BOOLAND", .OP_BOOLAND), ("BOOLOR", .OP_BOOLOR),
   ("0NOTEQUAL", .OP_0NOTEQUAL), ("EQUAL", .OP_EQUAL),
   ("EQUALVERIFY", .OP_EQUALVERIFY), ("NUMEQUAL", .OP_NUMEQUAL),
   ("SHA256", .OP_SHA256), ("HASH256", .OP_HASH256),
   ("RIPEMD160", .OP_RIPEMD160), ("HASH160", .OP_HASH160),
   ("CHECKSIG", .OP_CHECKSIG), ("CHECKSIGADD", .OP_CHECKSIGADD),
   ("CHECKMULTISIG", .OP_CHECKMULTISIG),
   ("CHECKSEQUENCEVERIFY", .OP_CHECKSEQUENCEVERIFY),
   ("CHECKLOCKTIMEVERIFY", .OP_CHECKLOCKTIMEVERIFY),
   ("VERIFY", .OP_VERIFY), ("SIZE", .OP_SIZE)]

/-- Every modeled opcode has a Bitcoin Core fixture name. -/
example : ∀ opcode, ∃ name, (name, opcode) ∈ coreOpcodeNameFixtures := by
  intro opcode
  cases opcode <;> simp [coreOpcodeNameFixtures]

private def coreOpcodeMappingsAgree : Bool :=
  coreOpcodeNameFixtures.all fun (name, expected) =>
    let sourceMatch := opcodeFromCoreName? name == some expected
    let byteMatch :=
      match deserializeCoreScriptBytes ⟨#[opcodeByte expected]⟩ with
      | .ok [.op actual] => actual == expected
      | _ => false
    sourceMatch && byteMatch

/-- Text names and raw opcode bytes select the same modeled constructor. -/
example : coreOpcodeMappingsAgree = true := by
  native_decide

private def coreErrorTagFixtures : List (ScriptError × String) :=
  [(.stackUnderflow, "INVALID_STACK_OPERATION"),
   (.altStackUnderflow, "INVALID_ALTSTACK_OPERATION"),
   (.scriptNumOverflow, "SCRIPTNUM"),
   (.scriptNumNonMinimal, "SCRIPTNUM"),
   (.pubkeyCount, "PUBKEY_COUNT"),
   (.signatureCount, "SIG_COUNT"),
   (.negativeLocktime, "NEGATIVE_LOCKTIME"),
   (.nullDummy, "SIG_NULLDUMMY"),
   (.equalVerify, "EQUALVERIFY"),
   (.verify, "VERIFY"),
   (.checkSequenceVerify, "UNSATISFIED_LOCKTIME"),
   (.checkLockTimeVerify, "UNSATISFIED_LOCKTIME"),
   (.minimalIf, "MINIMALIF"),
   (.unbalancedConditional, "UNBALANCED_CONDITIONAL")]

/-- Every modeled evaluator failure has an explicit Bitcoin Core tag. -/
example : ∀ error, ∃ tag, (error, tag) ∈ coreErrorTagFixtures := by
  intro error
  cases error <;> simp [coreErrorTagFixtures]

private def coreErrorTagMappingsAgree : Bool :=
  coreErrorTagFixtures.all fun (error, expected) =>
    coreScriptErrorTag error == expected

example : coreErrorTagMappingsAgree = true := by
  native_decide

private def pinnedCoreFixtureJson : String := r#"
[
  ["Format is: [[wit..., amount]?, scriptSig, scriptPubKey, flags, expected_scripterror, ... comments]"
  ],
  ["1 2", "2 EQUALVERIFY 1 EQUAL", "P2SH,STRICTENC", "OK",
    "Similarly whitespace around and between symbols"],
  ["0x01 0x0b", "11 EQUAL", "P2SH,STRICTENC", "OK", "push 1 byte"],
  ["0x4c 0x01 0x07", "7 EQUAL", "P2SH,STRICTENC", "OK", "0x4c is OP_PUSHDATA1"],
  ["0x4d 0x0100 0x08", "8 EQUAL", "P2SH,STRICTENC", "OK", "0x4d is OP_PUSHDATA2"],
  ["0x4e 0x01000000 0x09", "9 EQUAL", "P2SH,STRICTENC", "OK", "0x4e is OP_PUSHDATA4"],
  ["1", "IF 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0 ELSE 1 ELSE 0 ENDIF", "P2SH,STRICTENC", "OK",
    "Multiple ELSE's are valid and executed inverts on each ELSE encountered"],
  ["1 0", "SWAP 1 EQUALVERIFY 0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "DUP 1 ADD 1 EQUALVERIFY 0 EQUAL", "P2SH,STRICTENC", "OK"],
  ["''",
    "SHA256 0x20 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 EQUAL",
    "P2SH,STRICTENC", "OK"],
  ["'a'",
    "SHA256 0x20 0xca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb EQUAL",
    "P2SH,STRICTENC", "OK"],
  ["'abcdefghijklmnopqrstuvwxyz'",
    "SHA256 0x20 0x71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73 EQUAL",
    "P2SH,STRICTENC", "OK"],
  ["''", "DUP HASH160 SWAP SHA256 RIPEMD160 EQUAL", "P2SH,STRICTENC", "OK"],
  ["''", "DUP HASH256 SWAP SHA256 SHA256 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "SHA256", "P2SH,STRICTENC", "OK"]
]
"#

private def fixtureTests : List CoreFixtureEntry → List CoreScriptTest :=
  List.filterMap fun
    | .comment _ => none
    | .test test => some test

private def pinnedFixtureCheck : Bool :=
  match parseCoreScriptTests pinnedCoreFixtureJson with
  | .error _ => false
  | .ok entries =>
      let tests := fixtureTests entries
      tests.length == 16 && tests.all fun test =>
        match checkCoreFixture rejectingOracle test with
        | .ok matched => matched
        | .error _ => false

/-- All checked-in positive rows import and match the executable evaluator. -/
example : pinnedFixtureCheck = true := by
  native_decide

private def pinnedCoreFailureFixtureJson : String := r#"
[
  ["", "", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["0", "VERIFY 1", "P2SH,STRICTENC", "VERIFY"],
  ["1", "SWAP", "P2SH,STRICTENC", "INVALID_STACK_OPERATION"],
  ["1", "FROMALTSTACK", "P2SH,STRICTENC", "INVALID_ALTSTACK_OPERATION"],
  ["0 1", "SWAP 1 EQUALVERIFY", "P2SH,STRICTENC", "EQUALVERIFY"],
  ["2147483648 1", "BOOLOR 1", "P2SH,STRICTENC", "SCRIPTNUM",
    "We cannot do BOOLOR on 5-byte integers (but we can still do IF etc)"],
  ["0x0100", "CHECKSEQUENCEVERIFY", "CHECKSEQUENCEVERIFY,MINIMALDATA",
    "SCRIPTNUM", "CSV fails if stack top is not minimally encoded"],
  ["1", "ENDIF", "P2SH,STRICTENC", "UNBALANCED_CONDITIONAL",
    "Malformed IF/ELSE/ENDIF sequence"],
  ["1", "IF 1", "P2SH,STRICTENC", "UNBALANCED_CONDITIONAL",
    "IF without ENDIF"],
  ["-1", "CHECKSEQUENCEVERIFY", "CHECKSEQUENCEVERIFY", "NEGATIVE_LOCKTIME",
    "CSV automatically fails if stack top is negative"],
  ["0", "CHECKSEQUENCEVERIFY", "CHECKSEQUENCEVERIFY", "UNSATISFIED_LOCKTIME",
    "CSV fails if stack top bit 1 << 31 is set and the tx version < 2"],
  ["0 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21",
    "21 CHECKMULTISIG 1", "P2SH,STRICTENC", "PUBKEY_COUNT",
    "nPubKeys > 20"],
  ["0 'sig' 1 0", "CHECKMULTISIG 1", "P2SH,STRICTENC", "SIG_COUNT",
    "nSigs > nPubKeys"]
]
"#

private def pinnedFailureFixtureCheck : Bool :=
  match parseCoreScriptTests pinnedCoreFailureFixtureJson with
  | .error _ => false
  | .ok entries =>
      let tests := fixtureTests entries
      tests.length == 13 && tests.all fun test =>
        match checkCoreFixture rejectingOracle test with
        | .ok matched => matched
        | .error _ => false

/-- Verbatim Core rejection rows match error class and final-false behavior. -/
example : pinnedFailureFixtureCheck = true := by
  native_decide

private def retainsDocumentationRow : Bool :=
  match parseCoreScriptTests pinnedCoreFixtureJson with
  | .ok (.comment _ :: _) => true
  | _ => false

/-- The positional JSON importer retains documentation rows. -/
example : retainsDocumentationRow = true := by
  native_decide

private def rawHexConcatenates : Bool :=
  match parseCoreScriptSource "0x02 0x01 0x00" with
  | .ok [.pushData bytes] => bytes == ⟨#[0x01, 0x00]⟩
  | _ => false

/-- Raw hex tokens concatenate serialized bytes before Script decoding. -/
example : rawHexConcatenates = true := by
  native_decide

private def quotedWhitespacePushes : Bool :=
  match parseCoreScriptSource "'hello world' SIZE 11 NUMEQUAL" with
  | .ok [.pushData bytes, .op .OP_SIZE, .pushNum 11, .op .OP_NUMEQUAL] =>
      bytes == "hello world".toUTF8
  | _ => false

/-- Quoted fixture strings may contain whitespace within one data push. -/
example : quotedWhitespacePushes = true := by
  native_decide

private def rejectsDrop : Bool :=
  match parseCoreScriptSource "1 DROP" with
  | .error (.unsupportedToken "DROP") => true
  | _ => false

/-- An opcode outside the modeled 27-opcode subset is reported by token. -/
example : rejectsDrop = true := by
  native_decide

private def rejectsTruncatedPush : Bool :=
  match parseCoreScriptSource "0x02 0x01" with
  | .error (.truncatedPushData 0 2 1) => true
  | _ => false

/-- Truncated raw pushes retain the byte offset and missing payload length. -/
example : rejectsTruncatedPush = true := by
  native_decide

private def rejectsNonMinimalPush : Bool :=
  let test : CoreScriptTest := {
    witness := none
    scriptSigSource := "0x4c 0x01 0x07"
    scriptPubKeySource := "7 EQUAL"
    flagSource := "MINIMALDATA"
    expectedError := "OK"
    comments := []
  }
  match prepareCoreFixture test with
  | .error .nonMinimalPushEncoding => true
  | _ => false

/-- MINIMALDATA is accepted only when the original raw push encoding is
    minimal. -/
example : rejectsNonMinimalPush = true := by
  native_decide

private def acceptsMinimalDataFixture : Bool :=
  let test : CoreScriptTest := {
    witness := none
    scriptSigSource := "7"
    scriptPubKeySource := "7 EQUAL"
    flagSource := "MINIMALDATA"
    expectedError := "OK"
    comments := []
  }
  match checkCoreFixture rejectingOracle test with
  | .ok matched => matched
  | .error _ => false

/-- A canonical push remains executable when MINIMALDATA is active. -/
example : acceptsMinimalDataFixture = true := by
  native_decide

private def rejectsUnmodeledFlag : Bool :=
  let test : CoreScriptTest := {
    witness := none
    scriptSigSource := "1"
    scriptPubKeySource := ""
    flagSource := "CLEANSTACK"
    expectedError := "OK"
    comments := []
  }
  match prepareCoreFixture test with
  | .error (.unsupportedFlag "CLEANSTACK") => true
  | _ => false

/-- Unmodeled verification flags are never ignored by the importer. -/
example : rejectsUnmodeledFlag = true := by
  native_decide

private def p2shFixture : CoreScriptTest where
  witness := none
  scriptSigSource := ""
  scriptPubKeySource :=
    "HASH160 0x14 0x0000000000000000000000000000000000000000 EQUAL"
  flagSource := "P2SH,STRICTENC"
  expectedError := "OK"
  comments := []

private def classifiesP2SH : Bool :=
  match prepareCoreFixture p2shFixture with
  | .error .p2shEvaluation => true
  | _ => false

/-- P2SH evaluation is not silently approximated by ordinary Script execution. -/
example : classifiesP2SH = true := by
  native_decide

private def signatureFixture : CoreScriptTest where
  witness := none
  scriptSigSource := "0 0"
  scriptPubKeySource := "CHECKSIG"
  flagSource := "STRICTENC"
  expectedError := "OK"
  comments := []

private def classifiesSignature : Bool :=
  match prepareCoreFixture signatureFixture with
  | .error .signatureOpcode => true
  | _ => false

/-- Signature fixtures wait for a concrete secp256k1-backed oracle. -/
example : classifiesSignature = true := by
  native_decide

private def negativeFixture : CoreScriptTest where
  witness := none
  scriptSigSource := ""
  scriptPubKeySource := "VERIFY"
  flagSource := "P2SH,STRICTENC"
  expectedError := "INVALID_STACK_OPERATION"
  comments := []

private def matchesExpectedError : Bool :=
  match checkCoreFixture rejectingOracle negativeFixture with
  | .ok matched => matched
  | .error _ => false

/-- Failure rows compare their expected Core tag with the modeled error. -/
example : matchesExpectedError = true := by
  native_decide

private def activeUnclosedBranchFixture : CoreScriptTest where
  witness := none
  scriptSigSource := "0 1"
  scriptPubKeySource := "IF VERIFY"
  flagSource := "P2SH,STRICTENC"
  expectedError := "VERIFY"
  comments := ["active runtime error precedes missing ENDIF"]

private def inactiveUnclosedBranchFixture : CoreScriptTest where
  witness := none
  scriptSigSource := "0 0"
  scriptPubKeySource := "IF VERIFY"
  flagSource := "P2SH,STRICTENC"
  expectedError := "UNBALANCED_CONDITIONAL"
  comments := ["inactive VERIFY is skipped before missing ENDIF"]

private def matchesUnclosedBranchErrorPrecedence : Bool :=
  [activeUnclosedBranchFixture, inactiveUnclosedBranchFixture].all fun test =>
    match checkCoreFixture rejectingOracle test with
    | .ok matched => matched
    | .error _ => false

/-- The fixture pipeline preserves Bitcoin Core's EOF error precedence for
    active and inactive code inside an unclosed conditional. -/
example : matchesUnclosedBranchErrorPrecedence = true := by
  native_decide

private def nullDummyFixture : CoreScriptTest where
  witness := none
  scriptSigSource := "1 0 0"
  scriptPubKeySource := "CHECKMULTISIG"
  flagSource := "NULLDUMMY"
  expectedError := "SIG_NULLDUMMY"
  comments := []

private def matchesNullDummyError : Bool :=
  match checkCoreFixture rejectingOracle nullDummyFixture with
  | .ok matched => matched
  | .error _ => false

/-- NULLDUMMY fails before the signature oracle is consulted. -/
example : matchesNullDummyError = true := by
  native_decide

private def classifiesWitnessRow : Bool :=
  match parseCoreScriptTests
    "[[[\"00\", 0], \"\", \"1\", \"\", \"OK\"]]" with
  | .ok [.test test] =>
      match prepareCoreFixture test with
      | .error .witnessCase => true
      | _ => false
  | _ => false

/-- Witness-form rows are parsed, retained, and classified separately. -/
example : classifiesWitnessRow = true := by
  native_decide

end LeanMiniscript.Extraction
