import LeanMiniscript.Script.Evaluator
import LeanMiniscript.Script.Serialization
import LeanMiniscript.Bitcoin.Serialization

namespace LeanMiniscript.Script

/-!
BIP342 validation weight is an execution resource separate from the stacks.
`Eval` remains the resource-free opcode relation; `WeightedEval` composes its
single-instruction transitions with debits and conditional selection. Complete
Tapscript callers use `evaluateTapscript`, supplying the script-path witness
including script, control block and optional annex. Control-block commitment
validation and initial stack/element limits remain outside this boundary.
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

theorem debitValidationWeight_nonincreasing
    {signature : StackElement} {before after : Nat}
    (charged : debitValidationWeight signature before = .ok after) :
    after ≤ before := by
  unfold debitValidationWeight at charged
  split at charged
  · cases charged; omega
  · split at charged
    · contradiction
    · cases charged; omega

/-- Core decodes CHECKSIGADD's count before entering EvalChecksigTapscript.
    Stack underflow and inactive opcodes are left to the opcode evaluator. -/
def prepareValidationWeight (element : ScriptElement) (stack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (remaining : Nat) :
    Except ScriptError Nat :=
  if ctx.sigVersion ≠ .tapscript then .ok remaining
  else match element, stack with
    | .op .OP_CHECKSIG, _ :: signature :: _ =>
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
            if minimalIfSatisfied flags top then
              match _split : splitConditional rest with
              | none => finishWeightedUnclosed
                  (evaluateWithValidationWeight oracle
                    (selectUnclosedConditional rest (element.branchChoice top))
                    stackRest altStack flags ctx remaining)
              | some frame => evaluateWithValidationWeight oracle
                  (frame.select (element.branchChoice top))
                  stackRest altStack flags ctx remaining
            else .failure .minimalIf
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
      (branch : element.isBranch = true) (minimal : ¬ minimalIfSatisfied flags top) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight (.failure .minimalIf)
  | branch {element : ScriptElement} {rest : Script} {frame : ConditionalFrame}
      {top : StackElement} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
      {weight : Nat} {result : WeightedResult}
      (branch : element.isBranch = true) (minimal : minimalIfSatisfied flags top)
      (split : splitConditional rest = some frame)
      (next : WeightedEval (frame.select (element.branchChoice top)) stack alt flags ctx weight result) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight result
  | unclosed {element : ScriptElement} {rest : Script} {top : StackElement}
      {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext} {weight : Nat}
      {result : WeightedResult}
      (branch : element.isBranch = true) (minimal : minimalIfSatisfied flags top)
      (split : splitConditional rest = none)
      (next : WeightedEval (selectUnclosedConditional rest (element.branchChoice top))
        stack alt flags ctx weight result) :
      WeightedEval (element :: rest) (top :: stack) alt flags ctx weight
        (finishWeightedUnclosed result)

theorem evaluateWithValidationWeight_eq_of_eval
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {result : WeightedResult}
    (evaluated : WeightedEval script stack alt flags ctx weight result) :
    evaluateWithValidationWeight oracle script stack alt flags ctx weight = result := by
  induction evaluated <;> rw [evaluateWithValidationWeight.eq_def]
  case step ordinary charged opcode next ih =>
    simp [ordinary, charged, evaluate_eq_of_eval agreement opcode, ih]
  case chargeError ordinary charged => simp [ordinary, charged]
  case opcodeError ordinary charged opcode =>
    simp [ordinary, charged, evaluate_eq_of_eval agreement opcode]
  case branchUnderflow branch => simp [branch]
  case branchMinimal branch minimal => simp [branch, minimal]
  case branch branch minimal split next ih =>
    simp only [branch, ↓reduceIte, minimal]
    rw [split]
    exact ih
  case unclosed branch minimal split next ih =>
    simp only [branch, ↓reduceIte, minimal]
    rw [split]
    simp only [ih]

theorem evaluateWithValidationWeight_sound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    (script : Script) (stack alt : Stack) (flags : ScriptFlags) (ctx : TxContext) (weight : Nat) :
    WeightedEval script stack alt flags ctx weight
      (evaluateWithValidationWeight oracle script stack alt flags ctx weight) := by
  have general : ∀ n, ∀ (script : Script), script.length = n → ∀ stack alt weight,
      WeightedEval script stack alt flags ctx weight
        (evaluateWithValidationWeight oracle script stack alt flags ctx weight) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro script lengthEq stack alt weight
      have recurse := fun (smaller : Script) (lt : smaller.length < script.length) =>
        ih smaller.length (by omega) smaller rfl
      cases script with
      | nil => simpa only [evaluateWithValidationWeight.eq_1] using
          (WeightedEval.empty stack alt flags ctx weight)
      | cons element rest =>
          rw [evaluateWithValidationWeight.eq_def]
          cases hBranch : element.isBranch with
          | true =>
              simp only [hBranch, ↓reduceIte]
              cases stack with
              | nil => exact .branchUnderflow hBranch
              | cons top stackRest =>
                  by_cases minimal : minimalIfSatisfied flags top
                  · simp only [minimal, ↓reduceIte]
                    cases split : splitConditional rest with
                    | none =>
                        exact .unclosed hBranch minimal split
                          (recurse _ (by
                            have smaller := selectUnclosedConditional_length_le rest (element.branchChoice top)
                            simp only [List.length_cons]; omega) stackRest alt weight)
                    | some frame =>
                        exact .branch hBranch minimal split
                          (recurse _ (by
                            have smaller := ConditionalFrame.select_length_lt split (element.branchChoice top)
                            simp only [List.length_cons]; omega) stackRest alt weight)
                  · simp only [minimal, ↓reduceIte]
                    exact .branchMinimal hBranch minimal
          | false =>
              simp only [hBranch, Bool.false_eq_true, ↓reduceIte]
              cases charged : prepareValidationWeight element stack flags ctx weight with
              | error error =>
                  exact .chargeError hBranch charged
              | ok nextWeight =>
                  have opcode := evaluate_sound agreement [element] stack alt flags ctx
                  cases computed : evaluate oracle [element] stack alt flags ctx with
                  | failure error =>
                      rw [computed] at opcode
                      exact .opcodeError hBranch charged opcode
                  | success nextStack nextAlt =>
                      rw [computed] at opcode
                      exact .step hBranch charged opcode
                        (recurse rest (by simp) nextStack nextAlt nextWeight)

  exact general script.length script rfl stack alt weight

theorem weighted_model_iff
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {result : WeightedResult} :
    WeightedEval script stack alt flags ctx weight result ↔
      evaluateWithValidationWeight CryptoOracle.model script stack alt flags ctx weight = result := by
  constructor
  · exact evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines
  · intro computed
    rw [← computed]
    exact evaluateWithValidationWeight_sound CryptoOracle.model_refines script stack alt flags ctx weight

theorem WeightedEval.deterministic
    {script : Script} {stack alt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {weight : Nat} {first second : WeightedResult}
    (a : WeightedEval script stack alt flags ctx weight first)
    (b : WeightedEval script stack alt flags ctx weight second) : first = second := by
  have ha := evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines a
  have hb := evaluateWithValidationWeight_eq_of_eval CryptoOracle.model_refines b
  exact ha.symm.trans hb

/-- Successful budgeted execution preserves the resource-free opcode model.
    Budget exhaustion introduces an additional failure, never a new success. -/
theorem WeightedEval.erase_success
    {script : Script} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {weight finalWeight : Nat}
    (evaluated : WeightedEval script stack alt flags ctx weight
      (.success finalStack finalAlt finalWeight)) :
    Eval script stack alt flags ctx (.success finalStack finalAlt) := by
  generalize resultEq : WeightedResult.success finalStack finalAlt finalWeight = result at evaluated
  induction evaluated with
  | empty => cases resultEq; exact .empty _ _ _ _
  | step ordinary charged opcode next ih => exact Eval.append opcode (ih resultEq)
  | chargeError => cases resultEq
  | opcodeError => cases resultEq
  | branchUnderflow => cases resultEq
  | branchMinimal => cases resultEq
  | branch branch minimal split next ih =>
      rename_i element rest frame top stack alt flags ctx weight result
      have erased := ih resultEq
      cases element with
      | pushData => contradiction
      | pushNum => contradiction
      | op opcode =>
          cases opcode <;> simp only [ScriptElement.isBranch, Bool.false_eq_true] at branch
          · exact .if_execute top stack alt rest frame flags ctx _ split minimal erased
          · exact .notif_execute top stack alt rest frame flags ctx _ split minimal erased
  | unclosed =>
      rename_i result branch minimal split next ih
      cases result <;> simp [finishWeightedUnclosed] at resultEq

/-- Script-path material, with witness arguments in wire (bottom-first) order.
    Annex, when present, must begin with 0x50. This type does not validate the
    control-block commitment to the spent Taproot output. -/
structure TapscriptWitness where
  arguments : List ByteArray
  scriptBytes : ByteArray
  controlBlock : ByteArray
  annex : Option ByteArray := none
  deriving Repr

def TapscriptWitness.fullWitness (witness : TapscriptWitness) : List ByteArray :=
  witness.arguments ++ [witness.scriptBytes, witness.controlBlock] ++ witness.annex.toList

/-- The caller supplies already parsed/validated script-path metadata. Bind
    the modeled script to the actual witness script bytes before execution. -/
def evaluateTapscript (oracle : CryptoOracle) (script : Script)
    (witness : TapscriptWitness) (flags : ScriptFlags) (ctx : TxContext) :
    WeightedResult :=
  if ctx.sigVersion ≠ .tapscript then .failure .badOpcode
  else if !(match serializeScript script with
    | .ok bytes => bytes.data == witness.scriptBytes.data
    | .error _ => false) then .failure .tapscriptWitnessScript
  else if witness.annex.any (fun bytes => bytes.size == 0 || bytes[0]! != 0x50) then
    .failure .tapscriptAnnex
  else evaluateWithValidationWeight oracle script witness.arguments.reverse [] flags ctx
    (initialValidationWeight witness.fullWitness)

end LeanMiniscript.Script
