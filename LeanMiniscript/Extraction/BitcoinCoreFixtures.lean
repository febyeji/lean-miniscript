import LeanMiniscript.Extraction.CoreFixtureJson
import LeanMiniscript.Extraction.CoreScriptSource
import LeanMiniscript.Extraction.RefInterp
import LeanMiniscript.Extraction.BitcoinCoreLegacyScript
import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Extraction.CoreFixtureExecution
import LeanMiniscript.Extraction.CoreFixtureWitnessData
import LeanMiniscript.Extraction.CoreFixtureTemplates

namespace LeanMiniscript.Extraction

open Lean
open LeanMiniscript.Script

/-!
# Bitcoin Core Script fixture preparation and execution

Bitcoin Core's `script_tests.json` stores Script programs in the textual
fixture syntax accepted by its test utilities. In particular, a `0x...` token
inserts raw serialized Script bytes rather than pushing the decoded bytes as
one stack element. This module retains that byte boundary and prepares
transaction-backed execution for all rows in the pinned fixture.
-/

/-- Reasons why a well-formed upstream row cannot yet be compared faithfully. -/
inductive CoreFixtureUnsupported where
  | witnessCase
  | witnessData (message : String)
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

/-- Original bytes, resolved witness, and verification flags for concrete
transaction-backed fixture execution. Expected result tags are kept separately. -/
structure CoreConcreteFixture where
  scriptSig : ByteArray
  scriptPubKey : ByteArray
  witness : List ByteArray
  amount : UInt64
  flags : CoreVerificationFlags

/-- Prepared input for concrete fixtures or the explicitly verifier-free
    legacy compatibility boundary. -/
structure SupportedCoreFixture where
  source : CoreScriptTest
  scriptSig : Script
  scriptPubKey : Script
  flags : ScriptFlags
  /-- Original legacy bytes with source-order execution and resource accounting. -/
  rawPrograms : Option (CoreLegacyProgram × CoreLegacyProgram) := none
  /-- Full VerifyScript input, including actual transaction and witness semantics. -/
  concrete : Option CoreConcreteFixture := none

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
  | .sigNullFail => "NULLFAIL"
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
      "SIG_NULLDUMMY" | "NULLFAIL" | "SIG_DER" | "SIG_HIGH_S" |
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
def prepareCoreFixtureWithoutVerifier (test : CoreScriptTest) :
    Except CoreFixtureUnsupported SupportedCoreFixture := do
  if test.witness.isSome then throw .witnessCase
  if !supportedExpectedError test.expectedError then
    throw (.expectedError test.expectedError)
  prepareRawCoreFixture test

private def firstUnsupportedVerificationFlag (names : List String) : Option String :=
  names.find? fun name =>
    !["P2SH", "STRICTENC", "DERSIG", "LOW_S", "MINIMALDATA", "MINIMALIF",
      "NULLDUMMY", "NULLFAIL", "CHECKLOCKTIMEVERIFY", "CHECKSEQUENCEVERIFY",
      "DISCOURAGE_UPGRADABLE_NOPS", "SIGPUSHONLY", "CLEANSTACK", "WITNESS",
      "WITNESS_PUBKEYTYPE", "TAPROOT", "DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM",
      "DISCOURAGE_UPGRADABLE_TAPROOT_VERSION", "DISCOURAGE_OP_SUCCESS",
      "DISCOURAGE_UPGRADABLE_PUBKEYTYPE", "CONST_SCRIPTCODE"].contains name

/-- Core's test harness adds P2SH and WITNESS whenever CLEANSTACK is requested. -/
def coreVerificationFlagsForFixture (names : List String) : CoreVerificationFlags where
  script := { flagsForCoreFixture names with
    witnessPubKeyType := names.contains "WITNESS_PUBKEYTYPE"
    discourageUpgradablePubKeyType := names.contains "DISCOURAGE_UPGRADABLE_PUBKEYTYPE" }
  p2sh := names.contains "P2SH" || names.contains "CLEANSTACK"
  sigPushOnly := names.contains "SIGPUSHONLY"
  cleanStack := names.contains "CLEANSTACK"
  witness := names.contains "WITNESS" || names.contains "CLEANSTACK"
  taproot := names.contains "TAPROOT"
  checkLockTimeVerify := names.contains "CHECKLOCKTIMEVERIFY"
  checkSequenceVerify := names.contains "CHECKSEQUENCEVERIFY"
  discourageUpgradableWitnessProgram := names.contains "DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM"
  discourageUpgradableTaprootVersion := names.contains "DISCOURAGE_UPGRADABLE_TAPROOT_VERSION"
  discourageOpSuccess := names.contains "DISCOURAGE_OP_SUCCESS"
  constScriptCode := names.contains "CONST_SCRIPTCODE"

/-- Prepare exact original bytes and concrete witness/transaction inputs.
Admission is independent of the expected result and signature verification;
execution determines every cryptographic result and Script failure. -/
def prepareCoreFixture (test : CoreScriptTest) :
    Except CoreFixtureUnsupported SupportedCoreFixture := do
  let witnessSource ← (parseCoreFixtureWitnessSource test.witness).mapError .witnessData
  let templates ← (resolveCoreFixtureTemplates
    (fun source => (coreScriptSourceBytes source).mapError (fun error => reprStr error))
    witnessSource.elements).mapError .witnessData
  let sigBytes ← (coreScriptSourceBytes test.scriptSigSource).mapError .scriptSig
  let pubKeyBytes ← if test.scriptPubKeySource == "0x51 0x20 #TAPROOTOUTPUT#" then
      (resolveCoreFixtureScriptPubKey
        (fun source => (coreScriptSourceBytes source).mapError (fun error => reprStr error))
        templates test.scriptPubKeySource).mapError .witnessData
    else (coreScriptSourceBytes test.scriptPubKeySource).mapError .scriptPubKey
  let names := coreFlagNames test.flagSource
  if let some flag := firstUnsupportedVerificationFlag names then throw (.unsupportedFlag flag)
  let flags := coreVerificationFlagsForFixture names
  return {
    source := test
    scriptSig := (deserializeCoreScriptBytes sigBytes).toOption.getD []
    scriptPubKey := (deserializeCoreScriptBytes pubKeyBytes).toOption.getD []
    flags := flags.script
    concrete := some {
      scriptSig := sigBytes, scriptPubKey := pubKeyBytes,
      witness := templates.witness, amount := witnessSource.amount, flags := flags }
  }

/-- Observable result at Bitcoin Core's `VerifyScript` boundary. `none` is a
    successful execution whose final stack is empty or false. -/
inductive CoreFixtureOutcome where
  | accepted
  | rejected (error : Option ScriptError)
  | verificationRejected (error : CoreVerificationError)
  deriving Repr, DecidableEq, BEq

/-- Render an evaluator outcome using Bitcoin Core's fixture result tags. -/
def CoreFixtureOutcome.coreTag : CoreFixtureOutcome → String
  | .accepted => "OK"
  | .rejected none => "EVAL_FALSE"
  | .rejected (some error) => coreScriptErrorTag error
  | .verificationRejected error => error.coreTag coreScriptErrorTag

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
def runCoreFixtureWithoutVerifier (oracle : CryptoOracle)
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

/-- Execute prepared fixtures with concrete hashes, ECDSA, Schnorr, transaction
sighashes, P2SH and witness verification. The supplied abstract oracle remains
available for manually constructed fixtures without concrete source inputs. -/
def runCoreFixture (oracle : CryptoOracle) (fixture : SupportedCoreFixture) :
    CoreFixtureOutcome :=
  match fixture.concrete with
  | none => runCoreFixtureWithoutVerifier oracle fixture
  | some input =>
      let transaction := coreFixtureTransaction input.scriptSig input.scriptPubKey input.amount
      let execute := executeCoreFixtureScript transaction input.flags
      let verifyWitness : CoreWitnessVerifier := fun witness version program wrapped =>
        verifyCoreWitnessProgram execute input.flags witness version program wrapped
          (checkCoreFixtureKeyPath transaction)
      match verifyCoreScripts execute verifyWitness input.flags
          input.scriptSig input.scriptPubKey input.witness with
      | .ok () => .accepted
      | .error error => .verificationRejected error

/-- Prepare, execute, and compare one Core fixture against its expected tag. -/
def checkCoreFixture (oracle : CryptoOracle) (test : CoreScriptTest) :
    Except CoreFixtureUnsupported Bool := do
  let fixture ← prepareCoreFixture test
  pure ((runCoreFixture oracle fixture).coreTag == test.expectedError)

end LeanMiniscript.Extraction
