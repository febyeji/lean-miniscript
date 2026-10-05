import Lean.Data.Json
import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Script.Codec.Deserialization
import LeanMiniscript.Extraction.BitcoinCoreLegacyScript

namespace LeanMiniscript.Extraction

open Lean
open LeanMiniscript.Script

/-!
# Bitcoin Core Script fixture import

Bitcoin Core's `script_tests.json` stores Script programs in the textual
fixture syntax accepted by its test utilities. In particular, a `0x...` token
inserts raw serialized Script bytes rather than pushing the decoded bytes as
one stack element. This module reproduces that boundary for the opcode subset
modeled by lean-miniscript and classifies unsupported semantics explicitly.
-/

/-- Bitcoin Core revision used by the checked Script fixture subset. -/
def bitcoinCoreScriptTestsCommit : String :=
  "9be056a8a72b624dae9623b2f7bded92c2a21c91"

/-- Path of the authoritative fixture file within the pinned Bitcoin Core tree. -/
def bitcoinCoreScriptTestsPath : String :=
  "src/test/data/script_tests.json"

/-- One executable entry decoded from Bitcoin Core's positional JSON format. -/
structure CoreScriptTest where
  witness : Option Json
  scriptSigSource : String
  scriptPubKeySource : String
  flagSource : String
  expectedError : String
  comments : List String

/-- `script_tests.json` also contains one-string documentation rows. -/
inductive CoreFixtureEntry where
  | comment (text : String)
  | test (test : CoreScriptTest)

/-- A malformed JSON document or positional fixture entry. -/
inductive CoreFixtureJsonError where
  | invalidJson (message : String)
  | rootNotArray
  | entryNotArray (index : Nat)
  | invalidEntry (index : Nat) (message : String)
  deriving Repr, DecidableEq

private def jsonStringAt (entryIndex : Nat) (values : Array Json)
    (fieldIndex : Nat) (fieldName : String) :
    Except CoreFixtureJsonError String := do
  let value ← match values[fieldIndex]? with
    | some value => pure value
    | none => throw (.invalidEntry entryIndex s!"missing {fieldName}")
  match value with
  | .str text => pure text
  | _ => throw (.invalidEntry entryIndex s!"{fieldName} must be a string")

private def jsonComments (entryIndex : Nat) (values : Array Json)
    (start : Nat) : Except CoreFixtureJsonError (List String) := do
  let trailing := values.toList.drop start
  trailing.mapM fun value =>
    match value with
    | .str text => pure text
    | _ => throw (.invalidEntry entryIndex "comments must be strings")

private def parseFixtureEntry (index : Nat) (json : Json) :
    Except CoreFixtureJsonError CoreFixtureEntry := do
  let values ← match json with
    | .arr values => pure values
    | _ => throw (.entryNotArray index)
  if values.size = 1 then
    return .comment (← jsonStringAt index values 0 "comment")
  let (witness, firstField) :=
    match values[0]? with
    | some witness@(.arr _) => (some witness, 1)
    | _ => (none, 0)
  if values.size < firstField + 4 then
    throw (.invalidEntry index "expected scriptSig, scriptPubKey, flags, and result")
  return .test {
    witness := witness
    scriptSigSource := ← jsonStringAt index values firstField "scriptSig"
    scriptPubKeySource := ← jsonStringAt index values (firstField + 1) "scriptPubKey"
    flagSource := ← jsonStringAt index values (firstField + 2) "flags"
    expectedError := ← jsonStringAt index values (firstField + 3) "expected result"
    comments := ← jsonComments index values (firstField + 4)
  }

/-- Parse the complete positional JSON array without dropping documentation,
    witness, comment, flag, or expected-error fields. -/
def parseCoreScriptTests (input : String) :
    Except CoreFixtureJsonError (List CoreFixtureEntry) := do
  let json ← (Json.parse input).mapError .invalidJson
  let entries ← match json with
    | .arr entries => pure entries
    | _ => throw .rootNotArray
  entries.toList.zipIdx.mapM fun (entry, index) =>
    parseFixtureEntry index entry

/-- Failures while translating Bitcoin Core's textual Script fixture syntax. -/
inductive CoreScriptSourceError where
  | unterminatedQuote
  | quoteInsideToken
  | invalidHex (token : String)
  | oddHexLength (token : String)
  | unsupportedToken (token : String)
  | serialization (error : SerializationError)
  | truncatedPushLength (offset width remaining : Nat)
  | truncatedPushData (offset expected remaining : Nat)
  | unsupportedOpcode (offset : Nat) (byte : UInt8)
  | decoderFuelExhausted (offset : Nat)
  deriving Repr, DecidableEq

/-- Preserve the fixture importer's public error categories while delegating
    byte decoding to the shared Script deserializer. -/
def CoreScriptSourceError.ofDeserialization :
    DeserializationError → CoreScriptSourceError
  | .truncatedPushLength offset width remaining =>
      .truncatedPushLength offset width remaining
  | .truncatedPushData offset expected remaining =>
      .truncatedPushData offset expected remaining
  | .unsupportedOpcode offset byte => .unsupportedOpcode offset byte

private inductive CoreSourceToken where
  | word (text : String)
  | quoted (text : String)

private def flushWord (wordRev : List Char)
    (tokensRev : List CoreSourceToken) : List CoreSourceToken :=
  match wordRev with
  | [] => tokensRev
  | _ => .word (String.ofList wordRev.reverse) :: tokensRev

private def tokenizeCoreSourceAux : List Char → List Char →
    List CoreSourceToken → Bool →
    Except CoreScriptSourceError (List CoreSourceToken)
  | [], _, _, true => .error .unterminatedQuote
  | [], wordRev, tokensRev, false => .ok (flushWord wordRev tokensRev).reverse
  | char :: rest, charsRev, tokensRev, true =>
      if char = '\'' then
        tokenizeCoreSourceAux rest []
          (.quoted (String.ofList charsRev.reverse) :: tokensRev) false
      else
        tokenizeCoreSourceAux rest (char :: charsRev) tokensRev true
  | char :: rest, wordRev, tokensRev, false =>
      if char.isWhitespace then
        tokenizeCoreSourceAux rest [] (flushWord wordRev tokensRev) false
      else if char = '\'' then
        match wordRev with
        | _ :: _ => .error .quoteInsideToken
        | [] => tokenizeCoreSourceAux rest [] tokensRev true
      else
        tokenizeCoreSourceAux rest (char :: wordRev) tokensRev false

private def tokenizeCoreSource (source : String) :
    Except CoreScriptSourceError (List CoreSourceToken) :=
  tokenizeCoreSourceAux source.toList [] [] false

private def hexNibble? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' | 'A' => some 10
  | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12
  | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14
  | 'f' | 'F' => some 15
  | _ => none

private def decodeHexChars (token : String) : List Char →
    Except CoreScriptSourceError (List UInt8)
  | [] => .ok []
  | [_] => .error (.oddHexLength token)
  | high :: low :: rest => do
      let highNibble ← match hexNibble? high with
        | some value => pure value
        | none => throw (.invalidHex token)
      let lowNibble ← match hexNibble? low with
        | some value => pure value
        | none => throw (.invalidHex token)
      return UInt8.ofNat (16 * highNibble + lowNibble) ::
        (← decodeHexChars token rest)

private def decodeRawHexToken (token : String) :
    Except CoreScriptSourceError ByteArray :=
  match token.toList with
  | '0' :: 'x' :: digits =>
      return ⟨(← decodeHexChars token digits).toArray⟩
  | '0' :: 'X' :: digits =>
      return ⟨(← decodeHexChars token digits).toArray⟩
  | _ => .error (.invalidHex token)

/-- Map the modeled opcode names used by Bitcoin Core fixture sources. -/
def opcodeFromCoreName? : String → Option Opcode
  | "NOP" => some .OP_NOP
  | "NOP1" => some .OP_NOP1
  | "NOP4" => some .OP_NOP4
  | "NOP5" => some .OP_NOP5
  | "NOP6" => some .OP_NOP6
  | "NOP7" => some .OP_NOP7
  | "NOP8" => some .OP_NOP8
  | "NOP9" => some .OP_NOP9
  | "NOP10" => some .OP_NOP10
  | "RETURN" => some .OP_RETURN
  | "IF" => some .OP_IF
  | "NOTIF" => some .OP_NOTIF
  | "ELSE" => some .OP_ELSE
  | "ENDIF" => some .OP_ENDIF
  | "2DROP" => some .OP_2DROP
  | "2DUP" => some .OP_2DUP
  | "3DUP" => some .OP_3DUP
  | "2OVER" => some .OP_2OVER
  | "2ROT" => some .OP_2ROT
  | "2SWAP" => some .OP_2SWAP
  | "IFDUP" => some .OP_IFDUP
  | "DEPTH" => some .OP_DEPTH
  | "DROP" => some .OP_DROP
  | "DUP" => some .OP_DUP
  | "NIP" => some .OP_NIP
  | "OVER" => some .OP_OVER
  | "ROT" => some .OP_ROT
  | "SWAP" => some .OP_SWAP
  | "TUCK" => some .OP_TUCK
  | "TOALTSTACK" => some .OP_TOALTSTACK
  | "FROMALTSTACK" => some .OP_FROMALTSTACK
  | "1ADD" => some .OP_1ADD
  | "1SUB" => some .OP_1SUB
  | "NEGATE" => some .OP_NEGATE
  | "ABS" => some .OP_ABS
  | "ADD" => some .OP_ADD
  | "SUB" => some .OP_SUB
  | "BOOLAND" => some .OP_BOOLAND
  | "BOOLOR" => some .OP_BOOLOR
  | "NOT" => some .OP_NOT
  | "0NOTEQUAL" => some .OP_0NOTEQUAL
  | "EQUAL" => some .OP_EQUAL
  | "EQUALVERIFY" => some .OP_EQUALVERIFY
  | "NUMEQUAL" => some .OP_NUMEQUAL
  | "NUMEQUALVERIFY" => some .OP_NUMEQUALVERIFY
  | "NUMNOTEQUAL" => some .OP_NUMNOTEQUAL
  | "LESSTHAN" => some .OP_LESSTHAN
  | "GREATERTHAN" => some .OP_GREATERTHAN
  | "LESSTHANOREQUAL" => some .OP_LESSTHANOREQUAL
  | "GREATERTHANOREQUAL" => some .OP_GREATERTHANOREQUAL
  | "WITHIN" => some .OP_WITHIN
  | "SHA256" => some .OP_SHA256
  | "HASH256" => some .OP_HASH256
  | "RIPEMD160" => some .OP_RIPEMD160
  | "HASH160" => some .OP_HASH160
  | "CHECKSIG" => some .OP_CHECKSIG
  | "CHECKSIGVERIFY" => some .OP_CHECKSIGVERIFY
  | "CHECKSIGADD" => some .OP_CHECKSIGADD
  | "CHECKMULTISIG" => some .OP_CHECKMULTISIG
  | "CHECKMULTISIGVERIFY" => some .OP_CHECKMULTISIGVERIFY
  | "CHECKSEQUENCEVERIFY" => some .OP_CHECKSEQUENCEVERIFY
  | "CHECKLOCKTIMEVERIFY" => some .OP_CHECKLOCKTIMEVERIFY
  | "VERIFY" => some .OP_VERIFY
  | "PICK" => some .OP_PICK
  | "ROLL" => some .OP_ROLL
  | "MIN" => some .OP_MIN
  | "MAX" => some .OP_MAX
  | "SIZE" => some .OP_SIZE
  | _ => none

/-- Decode raw Script bytes emitted by a Core fixture token, rejecting every
    opcode outside the modeled subset with its byte offset. -/
def deserializeCoreScriptBytes (bytes : ByteArray) :
    Except CoreScriptSourceError Script :=
  (deserializeScript bytes).mapError CoreScriptSourceError.ofDeserialization

/-- Legacy-only source aliases compile to their literal bytes, while the
shared Script AST continues to reject the corresponding unmodeled opcodes. -/
private def coreLegacyOpcodeByteFromName? : String → Option UInt8
  | "RESERVED" => some 0x50
  | "VER" => some 0x62
  | "VERIF" => some 0x65
  | "VERNOTIF" => some 0x66
  | "CAT" => some 0x7e
  | "SUBSTR" => some 0x7f
  | "LEFT" => some 0x80
  | "RIGHT" => some 0x81
  | "INVERT" => some 0x83
  | "AND" => some 0x84
  | "OR" => some 0x85
  | "XOR" => some 0x86
  | "RESERVED1" => some 0x89
  | "RESERVED2" => some 0x8a
  | "2MUL" => some 0x8d
  | "2DIV" => some 0x8e
  | "MUL" => some 0x95
  | "DIV" => some 0x96
  | "MOD" => some 0x97
  | "LSHIFT" => some 0x98
  | "RSHIFT" => some 0x99
  | _ => none

private def compileCoreToken : CoreSourceToken →
    Except CoreScriptSourceError ByteArray
  | .quoted text => (serializePushData text.toUTF8).mapError .serialization
  | .word token =>
      match token.toList with
      | '0' :: 'x' :: _ => decodeRawHexToken token
      | '0' :: 'X' :: _ => decodeRawHexToken token
      | _ =>
          match token.toInt? with
          | some number => (serializePushNum number).mapError .serialization
          | none =>
              match opcodeFromCoreName? token with
              | some opcode => .ok ⟨#[opcodeByte opcode]⟩
              | none =>
                  match coreLegacyOpcodeByteFromName? token with
                  | some byte => .ok ⟨#[byte]⟩
                  | none => .error (.unsupportedToken token)

/-- Compile Core's fixture tokens to the exact byte stream that its test
    utility feeds to the Script interpreter. -/
private def coreScriptSourceBytes (source : String) :
    Except CoreScriptSourceError ByteArray := do
  let tokens ← tokenizeCoreSource source
  tokens.foldlM (fun bytes token => do
    let next ← compileCoreToken token
    pure (bytes ++ next)) ByteArray.empty

/-- Translate Bitcoin Core fixture source through its serialized-byte
    boundary into the modeled Script AST. -/
def parseCoreScriptSource (source : String) :
    Except CoreScriptSourceError Script := do
  let bytes ← coreScriptSourceBytes source
  deserializeCoreScriptBytes bytes

/-- Reasons why a well-formed upstream row cannot yet be compared faithfully. -/
inductive CoreFixtureUnsupported where
  | witnessCase
  | scriptSig (error : CoreScriptSourceError)
  | scriptPubKey (error : CoreScriptSourceError)
  | legacyScriptSig (reason : CoreLegacyUnsupported)
  | legacyScriptPubKey (reason : CoreLegacyUnsupported)
  | unsupportedFlag (flag : String)
  | p2shEvaluation
  | signatureOpcode
  | nonMinimalPushEncoding
  | inactiveTimelockOpcode (flag : String)
  | expectedError (error : String)
  deriving Repr, DecidableEq

/-- A Core fixture whose execution and expected result fall entirely within
    the current evaluator and error-tag model. -/
structure SupportedCoreFixture where
  source : CoreScriptTest
  scriptSig : Script
  scriptPubKey : Script
  flags : ScriptFlags
  /-- Original legacy bytes with source-order execution and resource accounting. -/
  rawPrograms : Option (CoreLegacyProgram × CoreLegacyProgram) := none

private def coreFlagNames (source : String) : List String :=
  if source.trimAscii.isEmpty then []
  else (source.splitOn ",").map (fun flag => flag.trimAscii.toString)

/-- Accept flags whose effects are modeled or whose affected operations are
excluded by the subsequent fixture admission checks. -/
private def firstUnsupportedFlag (names : List String) : Option String :=
  names.find? fun flag =>
    !["P2SH", "STRICTENC", "DERSIG", "LOW_S", "MINIMALDATA", "MINIMALIF", "NULLDUMMY", "NULLFAIL",
      "CHECKLOCKTIMEVERIFY", "CHECKSEQUENCEVERIFY",
      "DISCOURAGE_UPGRADABLE_NOPS"].contains flag

private def flagsForCoreFixture (names : List String) : ScriptFlags where
  minimalIf := names.contains "MINIMALIF"
  minimalData := names.contains "MINIMALDATA"
  nullDummy := names.contains "NULLDUMMY"
  nullFail := names.contains "NULLFAIL"
  strictEncoding := names.contains "STRICTENC"
  derSig := names.contains "DERSIG"
  lowS := names.contains "LOW_S"
  discourageUpgradableNops := names.contains "DISCOURAGE_UPGRADABLE_NOPS"

/-- Bitcoin Core `ScriptErrorString` tag corresponding to each modeled
    evaluator failure. Several Lean errors intentionally share one Core tag. Boundary-only
    validation errors use explicit MODEL_ tags, not claimed Core errors. -/
def coreScriptErrorTag : ScriptError → String
  | .stackUnderflow => "INVALID_STACK_OPERATION"
  | .altStackUnderflow => "INVALID_ALTSTACK_OPERATION"
  | .stackSize => "STACK_SIZE"
  | .pushSize => "PUSH_SIZE"
  | .scriptSize => "SCRIPT_SIZE"
  | .opCount => "OP_COUNT"
  | .cleanStack => "CLEANSTACK"
  | .evalFalse => "EVAL_FALSE"
  | .scriptNumOverflow => "SCRIPTNUM"
  | .scriptNumNonMinimal => "SCRIPTNUM"
  | .minimalData => "MINIMALDATA"
  | .pubkeyCount => "PUBKEY_COUNT"
  | .signatureCount => "SIG_COUNT"
  | .negativeLocktime => "NEGATIVE_LOCKTIME"
  | .nullDummy => "SIG_NULLDUMMY"
  | .sigNullFail => "SIG_NULLFAIL"
  | .sigDer => "SIG_DER"
  | .sigHighS => "SIG_HIGH_S"
  | .sigHashType => "SIG_HASHTYPE"
  | .pubkeyType => "PUBKEYTYPE"
  | .witnessPubkeyType => "WITNESS_PUBKEYTYPE"
  | .schnorrSigSize => "SCHNORR_SIG_SIZE"
  | .schnorrSigHashType => "SCHNORR_SIG_HASHTYPE"
  | .schnorrSig => "SCHNORR_SIG"
  | .tapscriptEmptyPubkey => "TAPSCRIPT_EMPTY_PUBKEY"
  | .tapscriptValidationWeight => "TAPSCRIPT_VALIDATION_WEIGHT"
  | .tapscriptWitnessScript => "MODEL_TAPSCRIPT_WITNESS_SCRIPT"
  | .tapscriptAnnex => "MODEL_TAPSCRIPT_ANNEX"
  | .tapscriptFlags => "MODEL_TAPSCRIPT_FLAGS"
  | .discourageUpgradablePubkeyType => "DISCOURAGE_UPGRADABLE_PUBKEYTYPE"
  | .badOpcode => "BAD_OPCODE"
  | .opReturn => "OP_RETURN"
  | .disabledOpcode => "DISABLED_OPCODE"
  | .discourageUpgradableNops => "DISCOURAGE_UPGRADABLE_NOPS"
  | .tapscriptCheckMultiSig => "TAPSCRIPT_CHECKMULTISIG"
  | .equalVerify => "EQUALVERIFY"
  | .numEqualVerify => "NUMEQUALVERIFY"
  | .checkSigVerify => "CHECKSIGVERIFY"
  | .checkMultiSigVerify => "CHECKMULTISIGVERIFY"
  | .verify => "VERIFY"
  | .checkSequenceVerify => "UNSATISFIED_LOCKTIME"
  | .checkLockTimeVerify => "UNSATISFIED_LOCKTIME"
  | .minimalIf => "MINIMALIF"
  | .tapscriptMinimalIf => "TAPSCRIPT_MINIMALIF"
  | .unbalancedConditional => "UNBALANCED_CONDITIONAL"

private def supportedExpectedError : String → Bool
  | "SCRIPT_SIZE" | "OP_COUNT" | "PUSH_SIZE" | "STACK_SIZE" | "OK" | "EVAL_FALSE" | "BAD_OPCODE" | "OP_RETURN" | "DISABLED_OPCODE" |
      "DISCOURAGE_UPGRADABLE_NOPS" | "INVALID_STACK_OPERATION" |
      "INVALID_ALTSTACK_OPERATION" | "SCRIPTNUM" | "MINIMALDATA" |
      "PUBKEY_COUNT" | "SIG_COUNT" | "NEGATIVE_LOCKTIME" |
      "SIG_NULLDUMMY" | "SIG_NULLFAIL" | "SIG_DER" | "SIG_HIGH_S" |
      "SIG_HASHTYPE" | "PUBKEYTYPE" | "EQUALVERIFY" | "NUMEQUALVERIFY" |
      "CHECKSIGVERIFY" | "CHECKMULTISIGVERIFY" | "VERIFY" |
      "UNSATISFIED_LOCKTIME" | "MINIMALIF" | "TAPSCRIPT_MINIMALIF" |
      "UNBALANCED_CONDITIONAL" => true
  | _ => false

private def prepareRawCoreFixture (test : CoreScriptTest) :
    Except CoreFixtureUnsupported SupportedCoreFixture := do
  let sigBytes ← (coreScriptSourceBytes test.scriptSigSource).mapError .scriptSig
  let pubKeyBytes ← (coreScriptSourceBytes test.scriptPubKeySource).mapError .scriptPubKey
  let scriptSig ← (decodeCoreLegacyScript sigBytes).mapError .legacyScriptSig
  let scriptPubKey ← (decodeCoreLegacyScript pubKeyBytes).mapError .legacyScriptPubKey
  let flagNames := coreFlagNames test.flagSource
  if let some flag := firstUnsupportedFlag flagNames then throw (.unsupportedFlag flag)
  if flagNames.contains "P2SH" && scriptPubKey.isP2SH then throw .p2shEvaluation
  if (scriptSig.containsOpcode .OP_CHECKLOCKTIMEVERIFY ||
      scriptPubKey.containsOpcode .OP_CHECKLOCKTIMEVERIFY) &&
      !flagNames.contains "CHECKLOCKTIMEVERIFY" then
    throw (.inactiveTimelockOpcode "CHECKLOCKTIMEVERIFY")
  if (scriptSig.containsOpcode .OP_CHECKSEQUENCEVERIFY ||
      scriptPubKey.containsOpcode .OP_CHECKSEQUENCEVERIFY) &&
      !flagNames.contains "CHECKSEQUENCEVERIFY" then
    throw (.inactiveTimelockOpcode "CHECKSEQUENCEVERIFY")
  let oracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)
  let flags := flagsForCoreFixture flagNames
  let ctx : TxContext :=
    { version := 1, locktime := 0, sequence := 0xffffffff, sigHash := ⟨#[]⟩ }
  match ← (checkCoreLegacyWithoutVerifier oracle scriptSig [] flags ctx).mapError
      (fun _ => CoreFixtureUnsupported.signatureOpcode) with
  | .error _ => pure ()
  | .ok stack =>
      let _ ← (checkCoreLegacyWithoutVerifier oracle scriptPubKey stack flags ctx).mapError
        (fun _ => CoreFixtureUnsupported.signatureOpcode)
      pure ()
  return {
    source := test
    scriptSig := (parseCoreScriptSource test.scriptSigSource).toOption.getD []
    scriptPubKey := (parseCoreScriptSource test.scriptPubKeySource).toOption.getD []
    flags := flagsForCoreFixture flagNames
    rawPrograms := some (scriptSig, scriptPubKey)
  }

/-- Prepare original legacy bytes for resource-aware execution. Witness, P2SH,
unsupported flags, and paths reaching a cryptographic verifier remain excluded. -/
def prepareCoreFixture (test : CoreScriptTest) :
    Except CoreFixtureUnsupported SupportedCoreFixture := do
  if test.witness.isSome then throw .witnessCase
  if !supportedExpectedError test.expectedError then
    throw (.expectedError test.expectedError)
  prepareRawCoreFixture test

/-- Observable result at Bitcoin Core's `VerifyScript` boundary. `none` is a
    successful execution whose final stack is empty or false. -/
inductive CoreFixtureOutcome where
  | accepted
  | rejected (error : Option ScriptError)
  deriving Repr, DecidableEq, BEq

/-- Render an evaluator outcome using Bitcoin Core's fixture result tags. -/
def CoreFixtureOutcome.coreTag : CoreFixtureOutcome → String
  | .accepted => "OK"
  | .rejected none => "EVAL_FALSE"
  | .rejected (some error) => coreScriptErrorTag error

/-- Transaction fields described by the header of Core's `script_tests.json`.
    Signature cases are excluded before this simplified context is used. -/
def coreFixtureTxContext : TxContext where
  version := 1
  locktime := 0
  sequence := 0xffffffff
  sigHash := ⟨#[]⟩

/-- Execute scriptSig and scriptPubKey as separate Script evaluations. The main
    stack is preserved, while the alternate stack is reset between them just
    as it is at Core's two `EvalScript` boundaries. Concrete hashes match the
    admission preflight; caller-supplied signature callbacks remain available. -/
def runCoreFixture (oracle : CryptoOracle)
    (fixture : SupportedCoreFixture) : CoreFixtureOutcome :=
  let oracle := CryptoOracle.pureLeanHashes oracle.checkSig oracle.checkSchnorrSig
  match fixture.rawPrograms with
  | some (scriptSig, scriptPubKey) =>
      match runCoreLegacyScript oracle scriptSig [] fixture.flags coreFixtureTxContext with
      | .error error => .rejected (some error)
      | .ok stack =>
          match runCoreLegacyScript oracle scriptPubKey stack fixture.flags coreFixtureTxContext with
          | .error error => .rejected (some error)
          | .ok [] => .rejected none
          | .ok (top :: _) => if castToBool top then .accepted else .rejected none
  | none =>
      match execScript oracle fixture.scriptSig [] fixture.flags coreFixtureTxContext with
      | .failure error => .rejected (some error)
      | .success stack _ =>
          match execScript oracle fixture.scriptPubKey stack fixture.flags
              coreFixtureTxContext with
          | .failure error => .rejected (some error)
          | .success [] _ => .rejected none
          | .success (top :: _) _ =>
              if castToBool top then .accepted else .rejected none

/-- Import, conservatively classify, execute, and compare one Core fixture. -/
def checkCoreFixture (oracle : CryptoOracle) (test : CoreScriptTest) :
    Except CoreFixtureUnsupported Bool := do
  let fixture ← prepareCoreFixture test
  pure ((runCoreFixture oracle fixture).coreTag == test.expectedError)

end LeanMiniscript.Extraction
