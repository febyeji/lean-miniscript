import LeanMiniscript.Script.ValidationWeightCore
import LeanMiniscript.Script.ScriptCode

/-! Source-order execution with stack, push-size, operation-count and
signature-weight limits. Bounds, refinement and opcode lemmas are in
RuntimeLimitsProofs. -/

namespace LeanMiniscript.Script

/-!
Runtime limits for the modeled opcode subset. Instructions are visited in source
order, including inactive branches: oversized pushes fail, BASE or witness-v0
opcodes count, and disabled opcodes, OP_VERIF, and OP_VERNOTIF fail when
encountered, while signature debits, multisig key counts and ordinary opcode
execution only occur in active code.
The branch-projection evaluator remains available for budget-only reasoning.
-/

/-- Runtime state; the condition list is innermost-first. `operationCount` is
Core's per-script `nOpCount`, charged only by BASE and witness-v0 steps. -/
structure RuntimeState where
  stack : Stack
  altStack : Stack
  conditions : List Bool := []
  weight : Nat
  operationCount : Nat := 0
  deriving Repr

/-- Core's `MAX_OPS_PER_SCRIPT` for BASE and witness-v0 Script. -/
def maxOpsPerScript : Nat := 201

/-- Numeric pushes use the same byte representation as canonical serialization. -/
def ScriptElement.pushSize : ScriptElement → Nat
  | .pushData bytes => bytes.size
  | .pushNum number => (scriptNum number).size
  | .op _ | .badOpcode _ | .illegalOpcode _ => 0

/-- Core checks combined main/alt-stack depth after each visited instruction. -/
def checkRuntimeStack (state : RuntimeState) : Except ScriptError RuntimeState :=
  if state.stack.length + state.altStack.length > maxStackSize then .error .stackSize
  else .ok state

/-- The instruction the runtime executes: like Core, OP_CHECKLOCKTIMEVERIFY
    and OP_CHECKSEQUENCEVERIFY run as OP_NOP when their flag is off. -/
def ScriptElement.underTimelockFlags (flags : ScriptFlags) : ScriptElement → ScriptElement
  | .op .OP_CHECKLOCKTIMEVERIFY =>
      if flags.checkLockTimeVerify then .op .OP_CHECKLOCKTIMEVERIFY else .op .OP_NOP
  | .op .OP_CHECKSEQUENCEVERIFY =>
      if flags.checkSequenceVerify then .op .OP_CHECKSEQUENCEVERIFY else .op .OP_NOP
  | element => element

/-- One source instruction, before the combined stack check. Push size precedes
    control handling and execution, including in an inactive branch. An
    `illegalOpcode` fails in an inactive branch as well. -/
def executeRuntimeElement (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  if element.pushSize > maxScriptElementSize then throw .pushSize
  let active := state.conditions.all id
  match element with
  | .op .OP_IF | .op .OP_NOTIF =>
      if active then
        match state.stack with
        | [] => throw .stackUnderflow
        | top :: rest =>
            if minimalIfSatisfied flags ctx.sigVersion top then
              return { state with
                stack := rest
                conditions := element.branchChoice top :: state.conditions }
            else throw (minimalIfError ctx.sigVersion)
      else return { state with conditions := false :: state.conditions }
  | .op .OP_ELSE =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | first :: rest => return { state with conditions := (!first) :: rest }
  | .op .OP_ENDIF =>
      match state.conditions with
      | [] => throw .unbalancedConditional
      | _ :: rest => return { state with conditions := rest }
  | .illegalOpcode opcode => throw opcode.error
  | _ =>
      if active then
        let weight ← prepareValidationWeight element state.stack flags ctx state.weight
        match evaluate oracle [element.underTimelockFlags flags] state.stack state.altStack
            flags ctx with
        | .failure error => throw error
        | .success stack alt => return { state with stack := stack, altStack := alt, weight := weight }
      else return state

/-- Core's multisig key count, decoded from the top item and bounded before
the rest of the multisig frame is read. -/
def multisigKeyCount (flags : ScriptFlags) : Stack → Except ScriptError Nat
  | [] => .error .stackUnderflow
  | keyBytes :: _ => do
      let keys ← decodeScriptNum keyBytes flags.minimalData maxArithmeticScriptNumBytes
      if keys < 0 ∨ (maxPubKeysPerMultiSig : Int) < keys then throw .pubkeyCount
      return keys.toNat

/-- Public keys an opcode adds to the operation count: an active multisig's
key count, otherwise zero. -/
def opcodeKeyCount (opcode : Opcode) (flags : ScriptFlags) (active : Bool)
    (stack : Stack) : Except ScriptError Nat :=
  match opcode with
  | .OP_CHECKMULTISIG | .OP_CHECKMULTISIGVERIFY =>
      if active then multisigKeyCount flags stack else .ok 0
  | _ => .ok 0

/-- The operation count after one BASE or witness-v0 opcode. Every opcode is
above OP_16, so each one counts, active or not, before its keys. -/
def chargedOperationCount (opcode : Opcode) (state : RuntimeState)
    (flags : ScriptFlags) : Except ScriptError Nat := do
  let count := state.operationCount + 1
  if count > maxOpsPerScript then throw .opCount
  let keys ← opcodeKeyCount opcode flags (state.conditions.all id) state.stack
  if count + keys > maxOpsPerScript then throw .opCount
  return count + keys

/-- Core's operation count outside Tapscript. Pushes do not count, nor does
OP_RESERVED, the one byte of `badOpcode` at or below OP_16. Every
`illegalOpcode` byte is above OP_16 and counts. -/
def chargeOperations (element : ScriptElement) (state : RuntimeState)
    (flags : ScriptFlags) (ctx : TxContext) : Except ScriptError RuntimeState :=
  match element with
  | .op opcode =>
      if ctx.sigVersion = .tapscript then .ok state
      else (chargedOperationCount opcode state flags).map
        fun count => { state with operationCount := count }
  | .badOpcode opcode =>
      if ctx.sigVersion = .tapscript ∨ opcode.byte.toNat ≤ 0x60 then .ok state
      else if state.operationCount + 1 > maxOpsPerScript then .error .opCount
      else .ok { state with operationCount := state.operationCount + 1 }
  | .illegalOpcode _ =>
      if ctx.sigVersion = .tapscript then .ok state
      else if state.operationCount + 1 > maxOpsPerScript then .error .opCount
      else .ok { state with operationCount := state.operationCount + 1 }
  | _ => .ok state

/-- One instruction after its operation charge: opcode errors precede the
post-instruction stack limit. -/
def runtimeInstruction (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  let next ← executeRuntimeElement oracle element state flags ctx
  checkRuntimeStack next

/-- The signatures an opcode hands FindAndDelete: the item below the public key
of OP_CHECKSIG and OP_CHECKSIGVERIFY, and the signatures of a multisig frame
that decodes. -/
def instructionSignatures (opcode : Opcode) (state : RuntimeState)
    (flags : ScriptFlags) : Stack :=
  match opcode with
  | .OP_CHECKSIG | .OP_CHECKSIGVERIFY =>
      match state.stack with
      | _ :: sig :: _ => [sig]
      | _ => []
  | .OP_CHECKMULTISIG | .OP_CHECKMULTISIGVERIFY =>
      match decodeCheckMultiSigOperands flags state.stack with
      | .ok operands => operands.signatures
      | .error _ => []
  | _ => []

/-- Core's FindAndDelete of each signature's push, with the number of pushes
removed. -/
def removeSignatures (bytes : ByteArray) (signatures : Stack) : ByteArray × Nat :=
  signatures.foldl (fun (scriptCode, count) signature =>
    let (next, removed) := coreFindAndDelete scriptCode (coreSignaturePush signature)
    (next, count + removed)) (bytes, 0)

/-- Signature checking for one script: an oracle for each script code, and the
script code after the last executed OP_CODESEPARATOR. -/
structure ScriptCodeOracles where
  oracleFor : ByteArray → CryptoOracle
  scriptCode : ByteArray

/-- The same oracle for every script code, with an empty script code, from
which FindAndDelete removes nothing. -/
@[coe] def CryptoOracle.withoutScriptCode (oracle : CryptoOracle) : ScriptCodeOracles :=
  ⟨fun _ => oracle, ByteArray.empty⟩

instance : Coe CryptoOracle ScriptCodeOracles := ⟨CryptoOracle.withoutScriptCode⟩

/-- The oracle a step checks signatures with. Like Core, an active BASE
signature opcode first removes its signatures from the script code, and
CONST_SCRIPTCODE rejects any removal. -/
def ScriptCodeOracles.forStep (oracles : ScriptCodeOracles) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError CryptoOracle := do
  let signatures := match element with
    | .op opcode => if state.conditions.all id && ctx.sigVersion == .base then
        instructionSignatures opcode state flags else []
    | _ => []
  let (scriptCode, removed) := removeSignatures oracles.scriptCode signatures
  if removed > 0 && flags.constScriptCode then throw .sigFindAndDelete
  return oracles.oracleFor scriptCode

/-- Shared step boundary: the operation count precedes FindAndDelete, which
precedes the instruction. -/
def runtimeStep (oracles : ScriptCodeOracles) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    Except ScriptError RuntimeState := do
  let charged ← chargeOperations element state flags ctx
  let oracle ← oracles.forStep element state flags ctx
  runtimeInstruction oracle element charged flags ctx

/-- FindAndDelete removes nothing from an empty script code. -/
theorem removeSignatures_empty (signatures : Stack) :
    removeSignatures ByteArray.empty signatures = (ByteArray.empty, 0) := by
  unfold removeSignatures
  induction signatures with
  | nil => rfl
  | cons signature rest ih => simpa [List.foldl, coreFindAndDelete_empty] using ih

/-- One oracle with no script code checks every step's signatures. -/
@[simp] theorem ScriptCodeOracles.forStep_withoutScriptCode (oracle : CryptoOracle)
    (element : ScriptElement) (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    (oracle : ScriptCodeOracles).forStep element state flags ctx = .ok oracle := by
  simp [ScriptCodeOracles.forStep, CryptoOracle.withoutScriptCode, removeSignatures_empty,
    pure, Except.pure]

/-- A step with one oracle charges the operation count, then runs the
instruction. -/
theorem runtimeStep_withoutScriptCode (oracle : CryptoOracle) (element : ScriptElement)
    (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
    runtimeStep oracle element state flags ctx =
      (chargeOperations element state flags ctx).bind fun charged =>
        runtimeInstruction oracle element charged flags ctx := by
  simp only [runtimeStep, ScriptCodeOracles.forStep_withoutScriptCode, bind, Except.bind]

/-- EOF reports an unclosed conditional only after earlier runtime checks pass. -/
def finishRuntime (state : RuntimeState) : WeightedResult :=
  if state.conditions.isEmpty then .success state.stack state.altStack state.weight
  else .failure .unbalancedConditional

/-- Structural recursion over literal source order retains inactive push checks.
Each step gets `oracle` with no script code, so it removes no signatures. -/
def evaluateRuntime (oracle : CryptoOracle) : Script → RuntimeState →
    ScriptFlags → TxContext → WeightedResult
  | [], state, _, _ => finishRuntime state
  | element :: rest, state, flags, ctx =>
      match runtimeStep oracle element state flags ctx with
      | .error error => .failure error
      | .ok next => evaluateRuntime oracle rest next flags ctx

/-- The modeled relation composes source-order steps and final condition checks.
    Its step function uses the abstract crypto oracle, whose active opcode
    behavior is supplied by the existing evaluator/`Eval` refinement theorem. -/
inductive RuntimeEval : Script → RuntimeState → ScriptFlags → TxContext → WeightedResult → Prop where
  | done (state : RuntimeState) (flags : ScriptFlags) (ctx : TxContext) :
      RuntimeEval [] state flags ctx (finishRuntime state)
  | error {element : ScriptElement} {rest : Script} {state : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError}
      (failed : runtimeStep CryptoOracle.model element state flags ctx = .error error) :
      RuntimeEval (element :: rest) state flags ctx (.failure error)
  | step {element : ScriptElement} {rest : Script} {state next : RuntimeState}
      {flags : ScriptFlags} {ctx : TxContext} {result : WeightedResult}
      (stepped : runtimeStep CryptoOracle.model element state flags ctx = .ok next)
      (tail : RuntimeEval rest next flags ctx result) :
      RuntimeEval (element :: rest) state flags ctx result

/-- Runtime-limited execution starts with no open conditional. The caller
    checks initial witness bounds; the full-witness entry does so explicitly. -/
def evaluateWithRuntimeLimits (oracle : CryptoOracle) (script : Script)
    (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) : WeightedResult :=
  evaluateRuntime oracle script { stack := stack, altStack := alt, weight := weight } flags ctx

end LeanMiniscript.Script
