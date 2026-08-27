import Lean.Data.Json
import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Script.Serialization

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

/-- Map the 27 modeled opcode names used by Bitcoin Core fixture sources. -/
def opcodeFromCoreName? : String → Option Opcode
  | "IF" => some .OP_IF
  | "NOTIF" => some .OP_NOTIF
  | "ELSE" => some .OP_ELSE
  | "ENDIF" => some .OP_ENDIF
  | "IFDUP" => some .OP_IFDUP
  | "DUP" => some .OP_DUP
  | "SWAP" => some .OP_SWAP
  | "TOALTSTACK" => some .OP_TOALTSTACK
  | "FROMALTSTACK" => some .OP_FROMALTSTACK
  | "ADD" => some .OP_ADD
  | "BOOLAND" => some .OP_BOOLAND
  | "BOOLOR" => some .OP_BOOLOR
  | "0NOTEQUAL" => some .OP_0NOTEQUAL
  | "EQUAL" => some .OP_EQUAL
  | "EQUALVERIFY" => some .OP_EQUALVERIFY
  | "NUMEQUAL" => some .OP_NUMEQUAL
  | "SHA256" => some .OP_SHA256
  | "HASH256" => some .OP_HASH256
  | "RIPEMD160" => some .OP_RIPEMD160
  | "HASH160" => some .OP_HASH160
  | "CHECKSIG" => some .OP_CHECKSIG
  | "CHECKSIGADD" => some .OP_CHECKSIGADD
  | "CHECKMULTISIG" => some .OP_CHECKMULTISIG
  | "CHECKSEQUENCEVERIFY" => some .OP_CHECKSEQUENCEVERIFY
  | "CHECKLOCKTIMEVERIFY" => some .OP_CHECKLOCKTIMEVERIFY
  | "VERIFY" => some .OP_VERIFY
  | "SIZE" => some .OP_SIZE
  | _ => none

private def opcodeFromByte? : Nat → Option Opcode
  | 0x63 => some .OP_IF
  | 0x64 => some .OP_NOTIF
  | 0x67 => some .OP_ELSE
  | 0x68 => some .OP_ENDIF
  | 0x73 => some .OP_IFDUP
  | 0x76 => some .OP_DUP
  | 0x7c => some .OP_SWAP
  | 0x6b => some .OP_TOALTSTACK
  | 0x6c => some .OP_FROMALTSTACK
  | 0x93 => some .OP_ADD
  | 0x9a => some .OP_BOOLAND
  | 0x9b => some .OP_BOOLOR
  | 0x92 => some .OP_0NOTEQUAL
  | 0x87 => some .OP_EQUAL
  | 0x88 => some .OP_EQUALVERIFY
  | 0x9c => some .OP_NUMEQUAL
  | 0xa8 => some .OP_SHA256
  | 0xaa => some .OP_HASH256
  | 0xa6 => some .OP_RIPEMD160
  | 0xa9 => some .OP_HASH160
  | 0xac => some .OP_CHECKSIG
  | 0xba => some .OP_CHECKSIGADD
  | 0xae => some .OP_CHECKMULTISIG
  | 0xb2 => some .OP_CHECKSEQUENCEVERIFY
  | 0xb1 => some .OP_CHECKLOCKTIMEVERIFY
  | 0x69 => some .OP_VERIFY
  | 0x82 => some .OP_SIZE
  | _ => none

private def decodePush (offset size : Nat) (payload : List UInt8) :
    Except CoreScriptSourceError (ByteArray × List UInt8) :=
  if size ≤ payload.length then
    .ok (⟨(payload.take size).toArray⟩, payload.drop size)
  else
    .error (.truncatedPushData offset size payload.length)

private def deserializeCoreBytesAux : Nat → List UInt8 → Nat →
    Except CoreScriptSourceError Script
  | _, [], _ => .ok []
  | 0, _ :: _, offset => .error (.decoderFuelExhausted offset)
  | fuel + 1, byte :: rest, offset => do
      let value := byte.toNat
      if value = 0 then
        return .pushNum 0 ::
          (← deserializeCoreBytesAux fuel rest (offset + 1))
      else if value ≤ 75 then
        let (data, tail) ← decodePush offset value rest
        return .pushData data ::
          (← deserializeCoreBytesAux fuel tail (offset + 1 + value))
      else if value = 0x4c then
        match rest with
        | [] => throw (.truncatedPushLength offset 1 0)
        | sizeByte :: payload =>
            let size := sizeByte.toNat
            let (data, tail) ← decodePush offset size payload
            return .pushData data ::
              (← deserializeCoreBytesAux fuel tail (offset + 2 + size))
      else if value = 0x4d then
        match rest with
        | low :: high :: payload =>
            let size := low.toNat + 256 * high.toNat
            let (data, tail) ← decodePush offset size payload
            return .pushData data ::
              (← deserializeCoreBytesAux fuel tail (offset + 3 + size))
        | _ => throw (.truncatedPushLength offset 2 rest.length)
      else if value = 0x4e then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: payload =>
            let size := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
              16777216 * b3.toNat
            let (data, tail) ← decodePush offset size payload
            return .pushData data ::
              (← deserializeCoreBytesAux fuel tail (offset + 5 + size))
        | _ => throw (.truncatedPushLength offset 4 rest.length)
      else if value = 0x4f then
        return .pushNum (-1) ::
          (← deserializeCoreBytesAux fuel rest (offset + 1))
      else if 0x51 ≤ value ∧ value ≤ 0x60 then
        return .pushNum (value - 0x50) ::
          (← deserializeCoreBytesAux fuel rest (offset + 1))
      else
        match opcodeFromByte? value with
        | some opcode =>
            return .op opcode ::
              (← deserializeCoreBytesAux fuel rest (offset + 1))
        | none => throw (.unsupportedOpcode offset byte)

/-- Decode raw Script bytes emitted by a Core fixture token, rejecting every
    opcode outside the modeled subset with its byte offset. -/
def deserializeCoreScriptBytes (bytes : ByteArray) :
    Except CoreScriptSourceError Script :=
  deserializeCoreBytesAux (bytes.size + 1) bytes.data.toList 0

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
  | unsupportedFlag (flag : String)
  | p2shEvaluation
  | signatureOpcode
  | nonMinimalPushEncoding
  | inactiveTimelockOpcode (flag : String)
  | expectedError (error : String)
  deriving Repr, DecidableEq

/-- A positive Core fixture whose execution falls entirely within the current
    evaluator and flag model. -/
structure SupportedCoreFixture where
  source : CoreScriptTest
  scriptSig : Script
  scriptPubKey : Script
  flags : ScriptFlags

private def coreFlagNames (source : String) : List String :=
  if source.trimAscii.isEmpty then []
  else (source.splitOn ",").map (fun flag => flag.trimAscii.toString)

private def scriptContainsSignature (script : Script) : Bool :=
  script.any fun
    | .op .OP_CHECKSIG | .op .OP_CHECKSIGADD | .op .OP_CHECKMULTISIG => true
    | _ => false

private def scriptContainsOpcode (wanted : Opcode) (script : Script) : Bool :=
  script.any fun
    | .op opcode => opcode == wanted
    | _ => false

private def isP2SHScript : Script → Bool
  | [.op .OP_HASH160, .pushData hash, .op .OP_EQUAL] => hash.size == 20
  | _ => false

private def firstUnsupportedFlag (names : List String) : Option String :=
  names.find? fun flag =>
    !["P2SH", "STRICTENC", "MINIMALDATA", "MINIMALIF", "NULLDUMMY",
      "CHECKLOCKTIMEVERIFY", "CHECKSEQUENCEVERIFY"].contains flag

private def flagsForCoreFixture (names : List String) : ScriptFlags where
  minimalIf := names.contains "MINIMALIF"
  minimalData := names.contains "MINIMALDATA"
  nullDummy := names.contains "NULLDUMMY"
  strictEncoding := names.contains "STRICTENC"

private def sourceUsesMinimalPushes (source : String) (script : Script) : Bool :=
  match coreScriptSourceBytes source, serializeScript script with
  | .ok sourceBytes, .ok canonicalBytes => sourceBytes == canonicalBytes
  | _, _ => false

/-- Conservatively prepare an upstream positive test. Flags are ignored only
    when their affected semantics are absent: `P2SH` requires a non-P2SH
    scriptPubKey, and signature flags require a script without signature
    opcodes. Every other unmodeled condition is reported. -/
def prepareCoreFixture (test : CoreScriptTest) :
    Except CoreFixtureUnsupported SupportedCoreFixture := do
  if test.witness.isSome then throw .witnessCase
  if test.expectedError != "OK" then throw (.expectedError test.expectedError)
  let scriptSig ← (parseCoreScriptSource test.scriptSigSource).mapError .scriptSig
  let scriptPubKey ←
    (parseCoreScriptSource test.scriptPubKeySource).mapError .scriptPubKey
  let flagNames := coreFlagNames test.flagSource
  if let some flag := firstUnsupportedFlag flagNames then
    throw (.unsupportedFlag flag)
  if flagNames.contains "P2SH" && isP2SHScript scriptPubKey then
    throw .p2shEvaluation
  if scriptContainsSignature scriptSig || scriptContainsSignature scriptPubKey then
    throw .signatureOpcode
  if flagNames.contains "MINIMALDATA" &&
      (!sourceUsesMinimalPushes test.scriptSigSource scriptSig ||
        !sourceUsesMinimalPushes test.scriptPubKeySource scriptPubKey) then
    throw .nonMinimalPushEncoding
  if (scriptContainsOpcode .OP_CHECKLOCKTIMEVERIFY scriptSig ||
      scriptContainsOpcode .OP_CHECKLOCKTIMEVERIFY scriptPubKey) &&
      !flagNames.contains "CHECKLOCKTIMEVERIFY" then
    throw (.inactiveTimelockOpcode "CHECKLOCKTIMEVERIFY")
  if (scriptContainsOpcode .OP_CHECKSEQUENCEVERIFY scriptSig ||
      scriptContainsOpcode .OP_CHECKSEQUENCEVERIFY scriptPubKey) &&
      !flagNames.contains "CHECKSEQUENCEVERIFY" then
    throw (.inactiveTimelockOpcode "CHECKSEQUENCEVERIFY")
  return {
    source := test
    scriptSig := scriptSig
    scriptPubKey := scriptPubKey
    flags := flagsForCoreFixture flagNames
  }

/-- Observable result at Bitcoin Core's `VerifyScript` boundary for the
    currently supported positive fixtures. -/
inductive CoreFixtureOutcome where
  | accepted
  | rejected (error : Option ScriptError)
  deriving Repr, DecidableEq, BEq

/-- Transaction fields described by the header of Core's `script_tests.json`.
    Signature cases are excluded before this simplified context is used. -/
def coreFixtureTxContext : TxContext where
  version := 1
  locktime := 0
  sequence := 0xffffffff
  sigHash := ⟨#[]⟩

/-- Execute scriptSig and scriptPubKey as separate Script evaluations. The main
    stack is preserved, while the alternate stack is reset between them just
    as it is at Core's two `EvalScript` boundaries. -/
def runCoreFixture (oracle : CryptoOracle)
    (fixture : SupportedCoreFixture) : CoreFixtureOutcome :=
  match execScript oracle fixture.scriptSig [] fixture.flags coreFixtureTxContext with
  | .failure error => .rejected (some error)
  | .success stack _ =>
      match execScript oracle fixture.scriptPubKey stack fixture.flags
          coreFixtureTxContext with
      | .failure error => .rejected (some error)
      | .success [] _ => .rejected none
      | .success (top :: _) _ =>
          if castToBool top then .accepted else .rejected none

/-- Import, conservatively classify, and execute one positive Core fixture. -/
def checkCoreFixture (oracle : CryptoOracle) (test : CoreScriptTest) :
    Except CoreFixtureUnsupported Bool := do
  let fixture ← prepareCoreFixture test
  pure (runCoreFixture oracle fixture == .accepted)

end LeanMiniscript.Extraction
