import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Extraction.TypedScriptReader

/-!
# Script and VerifyScript equivalence obligations

Nine propositions between Core's reference semantics and the typed Lean model.
Three say that Core's raw byte loop `executeCoreScript` and the typed executor
`executeTypedScript` give the same result for every script of one signature
version. Six say that Core's VerifyScript and the same boundary run with the
typed executor give the same verdict on one VerifyScript boundary.

The typed executor reads script bytes with `decodeTypedScript`, which gives
every byte string a typed reading (`decodeTypedScript?_isSome`), so it never
runs Core's raw loop. The reader reads OP_RESERVED, OP_VER, OP_RESERVED1,
OP_RESERVED2, and the undefined bytes 0xbb-0xff as
`badOpcode`, which fails only when executed, and the 15 disabled opcodes
(OP_CAT and the other 14), OP_VERIF, and OP_VERNOTIF as `illegalOpcode`, which
fails even in an unexecuted branch. It reads a complete push that is not
minimal as `nonminimalPush`, which keeps the original opcode and fails under
MINIMALDATA only when executed, and a push that GetOp cannot read as
`truncatedPush`, which holds the bytes from it to the end of the script and
fails with BAD_OPCODE even in an unexecuted branch, and OP_CODESEPARATOR as
`codeSeparator`, which fails under BASE CONST_SCRIPTCODE in an executed or
unexecuted branch and otherwise starts the script code of the following
signature checks at the byte after it and sets the Tapscript codesep position
to its opcode position, as `coreRawStep` does.

Tapscript reads the disabled opcodes and the `badOpcode` bytes other than
0xff as OP_SUCCESSx.

`scripts/script_equivalence_obligations.lean` counts the obligations without
a proof.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-- The transaction context of a typed script's first step: Core's
`instructionContext` before any OP_CODESEPARATOR. Later steps carry the
position of the last executed one, updated by `evaluateScriptCodeRuntime`. -/
def typedScriptContext (ctx : TxContext) (request : CoreScriptExecutionRequest) : TxContext :=
  { ctx with
    sigVersion := request.sigVersion
    taproot := if request.sigVersion == .tapscript then ctx.taproot.map fun taproot =>
      { taproot with
        annex := request.annex
        spendPath := .scriptPath request.scriptBytes request.leafVersion 0xffffffff }
      else none }

/-- The typed context with the Tapscript codesep position of the last executed
OP_CODESEPARATOR; key-path and non-Tapscript contexts are unchanged. -/
def withCodeSeparatorPosition (ctx : TxContext) (position : UInt32) : TxContext :=
  { ctx with taproot := ctx.taproot.map fun taproot =>
      { taproot with spendPath := match taproot.spendPath with
        | .scriptPath scriptBytes leafVersion _ => .scriptPath scriptBytes leafVersion position
        | .keyPath => .keyPath } }

/-- Typed whole-script execution in source order, as Core's raw loop: the
main stack or a Core verification error. Each step runs with the oracle and
script code after the last executed OP_CODESEPARATOR: `codeSeparatorOffset`
is that offset into `scriptBytes`, `opcodePosition` is the head element's
instruction position, and `ctx` carries the codesep position. An
OP_CODESEPARATOR step counts as an operation outside Tapscript, fails with
Core's own OP_CODESEPARATOR error under BASE CONST_SCRIPTCODE in an executed
or unexecuted branch, and otherwise starts the script code at its end offset
and sets the codesep position when executed. -/
def evaluateScriptCodeRuntime (oracleFor : ByteArray → CryptoOracle) (scriptBytes : ByteArray) :
    Nat → Nat → Script → RuntimeState → ScriptFlags → TxContext →
    Except CoreVerificationError Stack
  | _, _, [], state, _, _ =>
      if state.conditions.isEmpty then .ok state.stack
      else .error (.script .unbalancedConditional)
  | opcodePosition, codeSeparatorOffset, element :: rest, state, flags, ctx =>
      match element with
      | .codeSeparator nextOffset =>
          if ctx.sigVersion != .tapscript && maxOpsPerScript < state.operationCount + 1 then
            .error (.script .opCount)
          else if ctx.sigVersion == .base && flags.constScriptCode then
            .error .opCodeSeparator
          else match runtimeStep
              ⟨oracleFor, scriptBytes.extract codeSeparatorOffset scriptBytes.size⟩
              element state flags ctx with
            | .error error => .error (.script error)
            | .ok next =>
                if state.conditions.all id then
                  evaluateScriptCodeRuntime oracleFor scriptBytes (opcodePosition + 1) nextOffset
                    rest next flags (withCodeSeparatorPosition ctx (UInt32.ofNat opcodePosition))
                else
                  evaluateScriptCodeRuntime oracleFor scriptBytes (opcodePosition + 1)
                    codeSeparatorOffset rest next flags ctx
      | _ =>
          match runtimeStep ⟨oracleFor, scriptBytes.extract codeSeparatorOffset scriptBytes.size⟩
              element state flags ctx with
          | .error error => .error (.script error)
          | .ok next =>
              evaluateScriptCodeRuntime oracleFor scriptBytes (opcodePosition + 1)
                codeSeparatorOffset rest next flags ctx

/-- Lean's whole-script executor. BASE and witness-v0 reject a script over
10,000 bytes as Core does. Otherwise the typed reading of the script runs on
the typed runtime from the request's stack and validation weight, with the
oracle for the request's signature version and the script code after the last
executed OP_CODESEPARATOR. -/
def executeTypedScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) : CoreScriptExecutor :=
  fun request =>
    if request.sigVersion != .tapscript && request.scriptBytes.size > 10000 then
      .error (.script .scriptSize)
    else evaluateScriptCodeRuntime
      (oracles request.sigVersion) request.scriptBytes 0 0 (decodeTypedScript request.scriptBytes)
      { stack := request.stack, altStack := [], weight := request.validationWeight }
      flags.script (typedScriptContext ctx request)

/-- VerifyScript with a given executor for every script it runs: scriptSig,
scriptPubKey, the P2SH redeem script, and the witness script. Key-path
signatures go to `keyPath`. -/
def verifyScriptWith (execute : CoreScriptExecutor) (flags : CoreVerificationFlags)
    (keyPath : CoreKeyPathChecker) (scriptSig scriptPubKey : ByteArray)
    (witness : List ByteArray) : Except CoreVerificationError Unit :=
  verifyCoreScripts execute
    (fun witness version program isP2SH =>
      verifyCoreWitnessProgram execute flags witness version program isP2SH keyPath)
    flags scriptSig scriptPubKey witness

/-- Core's VerifyScript reference semantics: every script runs on Core's raw loop. -/
def coreVerifyScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray) :
    Except CoreVerificationError Unit :=
  verifyScriptWith (executeCoreScript flags ctx oracles) flags keyPath
    scriptSig scriptPubKey witness

/-- Lean's verification model: the same boundary, with every script run by
the typed executor. -/
def typedVerifyScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray) :
    Except CoreVerificationError Unit :=
  verifyScriptWith (executeTypedScript flags ctx oracles) flags keyPath
    scriptSig scriptPubKey witness

/-- The six VerifyScript boundaries. `verifyScriptBoundary` puts every input
in exactly one. -/
inductive VerifyScriptBoundary where
  | legacy
  | p2sh
  | witnessV0
  | p2shWitnessV0
  | taprootKeyPath
  | taprootScriptPath
  deriving Repr, DecidableEq

/-- The witness items Core's Taproot dispatch keeps, top first: an annex is
removed when at least two items remain. -/
def taprootSpendItems (witness : List ByteArray) : List ByteArray :=
  match witness.reverse with
  | last :: next :: rest => if last.size > 0 && last[0]! == 0x50 then next :: rest
      else witness.reverse
  | reversed => reversed

/-- A scriptSig that is exactly one push of a witness-v0 program: the P2SH
shape whose witness Core verifies instead of rejecting as malleated. -/
def isWrappedWitnessV0 (scriptSig : ByteArray) : Bool :=
  match readCoreRawInstruction scriptSig 0 with
  | .error _ => false
  | .ok instruction =>
      scriptSig == coreSignaturePush instruction.payload &&
        match decodeCoreWitnessProgram? instruction.payload with
        | some (0, _) => true
        | _ => false

/-- The boundary VerifyScript takes for these inputs, decided from the flags
and bytes alone.

* `witnessV0`: the scriptPubKey is a native witness-v0 program and WITNESS or
  CLEANSTACK is on.
* `taprootKeyPath` and `taprootScriptPath`: the scriptPubKey is a native
  version-1 program of 32 bytes, WITNESS or CLEANSTACK is on, and TAPROOT is
  on. Script path when at least two witness items remain after the annex,
  key path otherwise (an empty witness fails there).
* `p2shWitnessV0`: P2SH or CLEANSTACK is on, the scriptPubKey is the P2SH
  template, WITNESS or CLEANSTACK is on, and the scriptSig is exactly one push
  of a witness-v0 program.
* `p2sh`: the other inputs with the P2SH template under P2SH or CLEANSTACK.
  Core runs the redeem script and no witness script: under WITNESS a
  witness-program redeem script fails as malleated unless the scriptSig is
  exactly its push, and a wrapped program of another version is not executed.
* `legacy`: every other input. Core runs only scriptSig and scriptPubKey: bare
  scripts, and witness programs it does not execute (WITNESS off, unknown
  versions, pay-to-anchor, Taproot without TAPROOT). -/
def verifyScriptBoundary (flags : CoreVerificationFlags) (scriptSig scriptPubKey : ByteArray)
    (witness : List ByteArray) : VerifyScriptBoundary :=
  let useWitness := flags.witness || flags.cleanStack
  let p2sh := flags.p2sh || flags.cleanStack
  match decodeCoreWitnessProgram? scriptPubKey with
  | some (version, program) =>
      if !useWitness then .legacy
      else if version == 0 then .witnessV0
      else if version == 1 && program.size == 32 && flags.taproot then
        if (taprootSpendItems witness).length ≥ 2 then .taprootScriptPath
        else .taprootKeyPath
      else .legacy
  | none =>
      if p2sh && coreScriptIsP2SH scriptPubKey then
        if useWitness && isWrappedWitnessV0 scriptSig then .p2shWitnessV0 else .p2sh
      else .legacy

/-- Core's raw loop and the typed executor give the same main stack or error
for every verification flag set, transaction context, oracle, and request of
signature version `version`. The request carries the script bytes, the start
stack, and the Tapscript validation weight, annex, tapleaf hash, and leaf
version. -/
def ScriptExecutionAgreement (version : SignatureVersion) : Prop :=
  ∀ (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest),
    request.sigVersion = version →
    executeCoreScript flags ctx oracles request = executeTypedScript flags ctx oracles request

/-- Core's VerifyScript and Lean's verification model give the same verdict
for every verification flag set, transaction context, script oracle, key-path
checker, scriptSig, scriptPubKey, and witness on boundary `boundary`. -/
def VerifyScriptAgreement (boundary : VerifyScriptBoundary) : Prop :=
  ∀ (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) (keyPath : CoreKeyPathChecker)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray),
    verifyScriptBoundary flags scriptSig scriptPubKey witness = boundary →
    coreVerifyScript flags ctx oracles keyPath scriptSig scriptPubKey witness =
      typedVerifyScript flags ctx oracles keyPath scriptSig scriptPubKey witness

/-- BASE whole-script execution. Premise: the request's signature version is
BASE. The typed runtime runs the script's typed reading, and its BASE
signature opcodes remove their signatures from the script code as Core's do. -/
def BaseExecutionAgreement : Prop := ScriptExecutionAgreement .base

/-- Witness-v0 whole-script execution. Premise: the request's signature
version is witness v0. The typed runtime runs the script's typed reading. -/
def WitnessV0ExecutionAgreement : Prop := ScriptExecutionAgreement .witnessV0

/-- Tapscript whole-script execution. Premise: the request's signature
version is Tapscript. The typed runtime runs the script's typed reading. The
witness boundary scans for OP_SUCCESSx before either executor runs. -/
def TapscriptExecutionAgreement : Prop := ScriptExecutionAgreement .tapscript

/-- The legacy boundary. Premise: `verifyScriptBoundary` selects `legacy`.
scriptSig and scriptPubKey run as BASE scripts. -/
def LegacyVerificationAgreement : Prop := VerifyScriptAgreement .legacy

/-- The P2SH boundary. Premise: `verifyScriptBoundary` selects `p2sh`.
scriptSig, scriptPubKey, and the redeem script run as BASE scripts. -/
def P2SHVerificationAgreement : Prop := VerifyScriptAgreement .p2sh

/-- The native witness-v0 boundary. Premise: `verifyScriptBoundary` selects
`witnessV0`. scriptSig and scriptPubKey run as BASE scripts and the witness
script or P2WPKH template as a witness-v0 script. -/
def WitnessV0VerificationAgreement : Prop := VerifyScriptAgreement .witnessV0

/-- The P2SH-wrapped witness-v0 boundary. Premise: `verifyScriptBoundary`
selects `p2shWitnessV0`. scriptSig, scriptPubKey, and the redeem script run
as BASE scripts and the witness script or P2WPKH template as a witness-v0
script. -/
def P2SHWitnessV0VerificationAgreement : Prop := VerifyScriptAgreement .p2shWitnessV0

/-- The Taproot key-path boundary. Premise: `verifyScriptBoundary` selects
`taprootKeyPath`. scriptSig and scriptPubKey run as BASE scripts. Both sides
check the signature with the same `keyPath`. -/
def TaprootKeyPathVerificationAgreement : Prop := VerifyScriptAgreement .taprootKeyPath

/-- The Taproot script-path boundary. Premise: `verifyScriptBoundary` selects
`taprootScriptPath`. scriptSig and scriptPubKey run as BASE scripts and a
version-0xc0 leaf as a Tapscript script. The witness boundary scans the leaf
for OP_SUCCESSx before either executor runs. -/
def TaprootScriptPathVerificationAgreement : Prop :=
  VerifyScriptAgreement .taprootScriptPath

end LeanMiniscript.Extraction
