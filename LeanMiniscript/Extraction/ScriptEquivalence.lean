import LeanMiniscript.Extraction.BitcoinCoreExecutionProofs
import LeanMiniscript.Extraction.BitcoinCoreVerification

/-!
# Script and VerifyScript equivalence obligations

Nine propositions between Core's reference semantics and the typed Lean model.
Three say that Core's raw byte loop `executeCoreScript` and the typed executor
`executeTypedScript` give the same result for every script of one signature
version. Six say that Core's VerifyScript and the same boundary run with the
typed executor give the same verdict on one VerifyScript boundary.

The typed executor reads script bytes with `decodeTypedScript?`. Bytes that
have no typed reading run on Core's raw loop on both sides, so every
obligation is a claim about the bytes that do. The reader reads OP_RESERVED,
OP_VER, OP_RESERVED1, OP_RESERVED2, and the undefined bytes 0xbb-0xff as
`badOpcode`, which fails only when executed, and the 15 disabled opcodes
(OP_CAT and the other 14), OP_VERIF, and OP_VERNOTIF as `illegalOpcode`, which
fails even in an unexecuted branch. It reads a complete push that is not
minimal as `nonminimalPush`, which keeps the original opcode and fails under
MINIMALDATA only when executed, and a push that GetOp cannot read as
`truncatedPush`, which holds the bytes from it to the end of the script and
fails with BAD_OPCODE even in an unexecuted branch. It rejects
OP_CODESEPARATOR.

Tapscript reads the disabled opcodes and the `badOpcode` bytes other than
0xff as OP_SUCCESSx.

`scripts/script_equivalence_obligations.lean` counts the obligations without
a proof.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-- A raw instruction reads as a typed element when it encodes it, is the
byte of a `badOpcode` or an `illegalOpcode`, or is the opcode and data of a
`nonminimalPush`. -/
def _root_.LeanMiniscript.Script.CoreRawInstruction.ReadsAs (instruction : CoreRawInstruction) :
    ScriptElement → Prop
  | .badOpcode opcode => instruction.opcode = opcode.byte ∧
      instruction.payload = ByteArray.empty
  | .illegalOpcode opcode => instruction.opcode = opcode.byte ∧
      instruction.payload = ByteArray.empty
  | .nonminimalPush push => instruction.opcode = push.opcode ∧
      instruction.payload = push.data
  | element => instruction.Encodes element

instance (instruction : CoreRawInstruction) (element : ScriptElement) :
    Decidable (instruction.ReadsAs element) := by
  cases element <;> unfold CoreRawInstruction.ReadsAs <;> infer_instance

/-- The typed element a raw instruction reads as: a minimal push, a
`nonminimalPush`, a numeric constant, a modeled opcode, or a `badOpcode` or
`illegalOpcode` with the same byte. `none` when the instruction reads as no
typed element. -/
def typedElement? (instruction : CoreRawInstruction) : Option ScriptElement :=
  let value := instruction.opcode.toNat
  let candidate : Option ScriptElement :=
    if value ≤ 0x4e then
      if nonminimal : isNonminimalPush instruction.opcode instruction.payload then
        some (.nonminimalPush ⟨instruction.opcode, instruction.payload, nonminimal⟩)
      else some (.pushData instruction.payload)
    else if value == 0x4f then some (.pushNum (-1))
    else if 0x51 ≤ value && value ≤ 0x60 then some (.pushNum ((value : Int) - 0x50))
    else match opcodeFromByte? value with
      | some opcode => some (.op opcode)
      | none =>
          if bad : isBadOpcodeByte instruction.opcode then
            some (.badOpcode ⟨instruction.opcode, bad⟩)
          else if illegal : isIllegalOpcodeByte instruction.opcode then
            some (.illegalOpcode ⟨instruction.opcode, illegal⟩)
          else none
  match candidate with
  | some element => if instruction.ReadsAs element then some element else none
  | none => none

/-- Read `bytes` from `offset` to the end as typed elements, with Core's GetOp
boundaries. A push GetOp cannot read ends the reading as a `truncatedPush` of
the bytes from it to the end. `none` when an instruction has no typed
reading. -/
def decodeTypedScriptFrom (bytes : ByteArray) : Nat → Nat → Option Script
  | 0, _ => none
  | fuel + 1, offset =>
      if offset = bytes.size then some []
      else match readCoreRawInstruction bytes offset with
        | .error _ =>
            if truncated : offset < bytes.size ∧
                isTruncatedPush (bytes.extract offset bytes.size) then
              some [.truncatedPush ⟨bytes.extract offset bytes.size, truncated.2⟩]
            else none
        | .ok instruction =>
            if offset < bytes.size ∧ offset < instruction.nextOffset then
              match typedElement? instruction,
                  decodeTypedScriptFrom bytes fuel instruction.nextOffset with
              | some element, some rest => some (element :: rest)
              | _, _ => none
            else none

/-- The typed reading of a whole script. Every instruction advances, so
`bytes.size + 1` steps reach the end. -/
def decodeTypedScript? (bytes : ByteArray) : Option Script :=
  decodeTypedScriptFrom bytes (bytes.size + 1) 0

/-- The transaction context of every step of a typed script: Core's
`instructionContext` before any OP_CODESEPARATOR, which a typed script does
not contain. -/
def typedScriptContext (ctx : TxContext) (request : CoreScriptExecutionRequest) : TxContext :=
  { ctx with
    sigVersion := request.sigVersion
    taproot := if request.sigVersion == .tapscript then ctx.taproot.map fun taproot =>
      { taproot with
        annex := request.annex
        spendPath := .scriptPath request.scriptBytes request.leafVersion 0xffffffff }
      else none }

/-- Typed whole-script execution in source order. Every step gets the same
oracles and script code, so an active BASE signature opcode removes its
signatures from that script code as Core does. `evaluateRuntime` is this
function with one oracle and an empty script code. -/
def evaluateScriptCodeRuntime (oracles : ScriptCodeOracles) : Script → RuntimeState →
    ScriptFlags → TxContext → WeightedResult
  | [], state, _, _ => finishRuntime state
  | element :: rest, state, flags, ctx =>
      match runtimeStep oracles element state flags ctx with
      | .error error => .failure error
      | .ok next => evaluateScriptCodeRuntime oracles rest next flags ctx

/-- Lean's whole-script executor. BASE and witness-v0 reject a script over
10,000 bytes as Core does. A script with a typed reading runs on the typed
runtime from the request's stack and validation weight, with the oracle for
the request's signature version and the whole script as script code. A script
without one runs on Core's raw loop. -/
def executeTypedScript (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle) : CoreScriptExecutor :=
  fun request =>
    if request.sigVersion != .tapscript && request.scriptBytes.size > 10000 then
      .error (.script .scriptSize)
    else match decodeTypedScript? request.scriptBytes with
      | none => executeCoreScript flags ctx oracles request
      | some script => coreRuntimeResult (evaluateScriptCodeRuntime
          ⟨oracles request.sigVersion, request.scriptBytes⟩ script
          { stack := request.stack, altStack := [], weight := request.validationWeight }
          flags.script (typedScriptContext ctx request))

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
BASE. Bytes with a typed reading run on the typed runtime, whose BASE
signature opcodes remove their signatures from the whole script as script
code; other bytes run on Core's raw loop on both sides. -/
def BaseExecutionAgreement : Prop := ScriptExecutionAgreement .base

/-- Witness-v0 whole-script execution. Premise: the request's signature
version is witness v0. Bytes with a typed reading run on the typed runtime
with the whole script as script code; other bytes run on Core's raw loop on
both sides. -/
def WitnessV0ExecutionAgreement : Prop := ScriptExecutionAgreement .witnessV0

/-- Tapscript whole-script execution. Premise: the request's signature
version is Tapscript. Bytes with a typed reading run on the typed runtime;
other bytes, including OP_SUCCESSx, run on Core's raw loop on both sides. The
witness boundary scans for OP_SUCCESSx before either executor runs. -/
def TapscriptExecutionAgreement : Prop := ScriptExecutionAgreement .tapscript

/-- The legacy boundary. Premise: `verifyScriptBoundary` selects `legacy`.
scriptSig and scriptPubKey run as BASE scripts; bytes without a typed reading
run on Core's raw loop on both sides. -/
def LegacyVerificationAgreement : Prop := VerifyScriptAgreement .legacy

/-- The P2SH boundary. Premise: `verifyScriptBoundary` selects `p2sh`.
scriptSig, scriptPubKey, and the redeem script run as BASE scripts; bytes
without a typed reading run on Core's raw loop on both sides. -/
def P2SHVerificationAgreement : Prop := VerifyScriptAgreement .p2sh

/-- The native witness-v0 boundary. Premise: `verifyScriptBoundary` selects
`witnessV0`. scriptSig and scriptPubKey run as BASE scripts and the witness
script or P2WPKH template as a witness-v0 script; bytes without a typed
reading run on Core's raw loop on both sides. -/
def WitnessV0VerificationAgreement : Prop := VerifyScriptAgreement .witnessV0

/-- The P2SH-wrapped witness-v0 boundary. Premise: `verifyScriptBoundary`
selects `p2shWitnessV0`. scriptSig, scriptPubKey, and the redeem script run
as BASE scripts and the witness script or P2WPKH template as a witness-v0
script; bytes without a typed reading run on Core's raw loop on both sides. -/
def P2SHWitnessV0VerificationAgreement : Prop := VerifyScriptAgreement .p2shWitnessV0

/-- The Taproot key-path boundary. Premise: `verifyScriptBoundary` selects
`taprootKeyPath`. scriptSig and scriptPubKey run as BASE scripts; bytes
without a typed reading run on Core's raw loop on both sides. Both sides check
the signature with the same `keyPath`. -/
def TaprootKeyPathVerificationAgreement : Prop := VerifyScriptAgreement .taprootKeyPath

/-- The Taproot script-path boundary. Premise: `verifyScriptBoundary` selects
`taprootScriptPath`. scriptSig and scriptPubKey run as BASE scripts and a
version-0xc0 leaf as a Tapscript script; bytes without a typed reading,
including OP_SUCCESSx, run on Core's raw loop on both sides. -/
def TaprootScriptPathVerificationAgreement : Prop :=
  VerifyScriptAgreement .taprootScriptPath

end LeanMiniscript.Extraction
