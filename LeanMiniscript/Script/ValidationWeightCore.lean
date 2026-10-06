import LeanMiniscript.Script.Evaluator
import LeanMiniscript.Script.BigStep
import LeanMiniscript.Script.Codec.Serialization
import LeanMiniscript.Bitcoin.Serialization

/-! Validation-weight execution and its relational specification. -/

namespace LeanMiniscript.Script

/-!
BIP342 validation weight is an execution resource separate from the stacks.
`Eval` remains the resource-free opcode relation; `WeightedEval` composes its
single-instruction transitions with debits and conditional selection. The full-witness
entry in `ValidationWeight` adds runtime limits and metadata checks. This module
contains the budget-only branch-projection API; ValidationWeightProofs proves
its refinement and erasure properties.
-/

def validationWeightOffset : Nat := 50
def validationWeightPerSigop : Nat := 50

def initialValidationWeight (fullWitness : List ByteArray) : Nat :=
  validationWeightOffset + (Bitcoin.serializeWitness fullWitness).size

/-- A successful debit cannot wrap or saturate: insufficient weight is an
    immediate typed error before public-key, signature and oracle checks. -/
def debitValidationWeight (signature : StackElement) (remaining : Nat) :
    Except ScriptError Nat :=
  if signature.size = 0 then .ok remaining
  else if remaining < validationWeightPerSigop then
    .error .tapscriptValidationWeight
  else .ok (remaining - validationWeightPerSigop)

/-- Core decodes CHECKSIGADD's count before entering EvalChecksigTapscript.
    Stack underflow and inactive opcodes are left to the opcode evaluator. -/
def prepareValidationWeight (element : ScriptElement) (stack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (remaining : Nat) :
    Except ScriptError Nat :=
  if ctx.sigVersion ≠ .tapscript then .ok remaining
  else match element, stack with
    | .op .OP_CHECKSIG, _ :: signature :: _
    | .op .OP_CHECKSIGVERIFY, _ :: signature :: _ =>
        debitValidationWeight signature remaining
    | .op .OP_CHECKSIGADD, _ :: count :: signature :: _ => do
        let _ ← decodeCheckSigAddCount flags ctx count
        debitValidationWeight signature remaining
    | _, _ => .ok remaining

/-- Successful execution returns the remaining validation weight as well as
    both stacks, so sequential calls can preserve the same resource state. -/
inductive WeightedResult where
  | success (stack altStack : Stack) (remaining : Nat)
  | failure (error : ScriptError)
  deriving Repr, DecidableEq

def WeightedResult.erase : WeightedResult → ExecResult
  | .success stack altStack _ => .success stack altStack
  | .failure error => .failure error

/-- Final witness-script acceptance, in Core's order: retain any execution
    error, require exactly one main-stack item, then test its truth value.
    The alt stack does not affect clean-stack; success returns remaining weight. -/
def WeightedResult.checkAcceptance : WeightedResult → Except ScriptError Nat
  | .failure error => .error error
  | .success [top] _ weight =>
      if castToBool top then .ok weight else .error .evalFalse
  | .success _ _ _ => .error .cleanStack

def finishWeightedUnclosed : WeightedResult → WeightedResult
  | .success _ _ _ => .failure .unbalancedConditional
  | .failure error => .failure error

def ScriptElement.isBranch : ScriptElement → Bool
  | .op .OP_IF | .op .OP_NOTIF => true
  | _ => false

def ScriptElement.branchChoice (element : ScriptElement) (top : StackElement) : Bool :=
  match element with
  | .op .OP_NOTIF => !castToBool top
  | _ => castToBool top

/-- Resource-aware execution of the same finite opcode subset. Skipped branch
    instructions never reach `prepareValidationWeight`. -/
def evaluateWithValidationWeight (oracle : CryptoOracle) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (remaining : Nat) : WeightedResult :=
  match script with
  | [] => .success stack altStack remaining
  | element :: rest =>
      if element.isBranch then
        match stack with
        | [] => .failure .stackUnderflow
        | top :: stackRest =>
            if minimalIfSatisfied flags ctx.sigVersion top then
              match _split : splitConditional rest with
              | none => finishWeightedUnclosed
                  (evaluateWithValidationWeight oracle
                    (selectUnclosedConditional rest (element.branchChoice top))
                    stackRest altStack flags ctx remaining)
              | some frame => evaluateWithValidationWeight oracle
                  (frame.select (element.branchChoice top))
                  stackRest altStack flags ctx remaining
            else .failure (minimalIfError ctx.sigVersion)
      else
        match prepareValidationWeight element stack flags ctx remaining with
        | .error error => .failure error
        | .ok nextWeight =>
            match evaluate oracle [element] stack altStack flags ctx with
            | .failure error => .failure error
            | .success nextStack nextAlt => evaluateWithValidationWeight oracle
                rest nextStack nextAlt flags ctx nextWeight
termination_by script.length
decreasing_by
  all_goals simp_wf
  · have smaller := selectUnclosedConditional_length_le rest (element.branchChoice top)
    omega
  · have smaller := ConditionalFrame.select_length_lt _split (element.branchChoice top)
    omega

/-- Authoritative composition of single-opcode `Eval` transitions with the
    resource checks. Conditional rules preserve Core's error precedence. -/
inductive WeightedEval : Script → Stack → Stack → ScriptFlags → TxContext →
    Nat → WeightedResult → Prop where
  | empty (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
      WeightedEval [] stack altStack flags ctx weight (.success stack altStack weight)
  | step {element : ScriptElement} {rest : Script} {stack alt nextStack nextAlt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {weight nextWeight : Nat} {result : WeightedResult}
      (ordinary : element.isBranch = false)
      (charged : prepareValidationWeight element stack flags ctx weight = .ok nextWeight)
      (opcode : Eval [element] stack alt flags ctx (.success nextStack nextAlt))
      (next : WeightedEval rest nextStack nextAlt flags ctx nextWeight result) :
      WeightedEval (element :: rest) stack alt flags ctx weight result
  | chargeError {element : ScriptElement} {rest : Script} {stack alt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {weight : Nat} {error : ScriptError}
      (ordinary : element.isBranch = false)
      (charged : prepareValidationWeight element stack flags ctx weight = .error error) :
      WeightedEval (element :: rest) stack alt flags ctx weight (.failure error)
  | opcodeError {element : ScriptElement} {rest : Script} {stack alt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {weight nextWeight : Nat} {error : ScriptError}
      (ordinary : element.isBranch = false)
      (charged : prepareValidationWeight element stack flags ctx weight = .ok nextWeight)
      (opcode : Eval [element] stack alt flags ctx (.failure error)) :
      WeightedEval (element :: rest) stack alt flags ctx weight (.failure error)
  | branchUnderflow {element : ScriptElement} {rest : Script} {alt : Stack}
      {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
      (branch : element.isBranch = true) :
      WeightedEval (element :: rest) [] alt flags ctx weight (.failure .stackUnderflow)
  | branchMinimal {element : ScriptElement} {rest : Script} {top : StackElement}
      {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
      (branch : element.isBranch = true)
      (minimal : ¬ minimalIfSatisfied flags ctx.sigVersion top) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight
        (.failure (minimalIfError ctx.sigVersion))
  | branch {element : ScriptElement} {rest : Script} {frame : ConditionalFrame}
      {top : StackElement} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
      {weight : Nat} {result : WeightedResult}
      (branch : element.isBranch = true) (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (split : splitConditional rest = some frame)
      (next : WeightedEval (frame.select (element.branchChoice top)) stack alt flags ctx weight result) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight result
  | unclosed {element : ScriptElement} {rest : Script} {top : StackElement}
      {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
      {result : WeightedResult}
      (branch : element.isBranch = true) (minimal : minimalIfSatisfied flags ctx.sigVersion top)
      (split : splitConditional rest = none)
      (next : WeightedEval (selectUnclosedConditional rest (element.branchChoice top))
        stack alt flags ctx weight result) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight
        (finishWeightedUnclosed result)

end LeanMiniscript.Script
