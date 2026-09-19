import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Composable execution frames

The satisfaction algorithm stores witnesses in serialized order, while Script
execution consumes a top-first stack.  The contracts below operate on the
top-first argument frame so recursive proofs can compose independently of the
candidate-selection representation.

These are successful execution contracts for selected arguments.  They are
distinct from the type guarantees in `Soundness`, which describe the possible
success-or-error behavior of arbitrary inputs.
-/

/-- Executing `script` replaces an exact top-first input frame with an exact
    output frame while preserving every main-stack suffix and the complete
    alternate stack. -/
def ExecutesStackFrame (script : Script) (inputs outputs : Stack)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∀ (rest altStack : Stack),
    Eval script (inputs ++ rest) altStack flags ctx
      (.success (outputs ++ rest) altStack)

/-- Stack-frame execution composes in Script source order. -/
theorem ExecutesStackFrame.append
    {left right : Script} {inputs middle outputs : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (leftExec : ExecutesStackFrame left inputs middle flags ctx)
    (rightExec : ExecutesStackFrame right middle outputs flags ctx) :
    ExecutesStackFrame (left ++ right) inputs outputs flags ctx := by
  intro rest altStack
  exact Eval.append (leftExec rest altStack) (rightExec rest altStack)

/-- A selected B-type execution consumes `args` and leaves one exact result. -/
def BExecution (fragment : CoreFragment) (args : Stack) (result : StackElement)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [result] flags ctx

/-- A selected V-type execution consumes `args` and leaves no result. -/
def VExecution (fragment : CoreFragment) (args : Stack)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [] flags ctx

/-- A selected K-type execution consumes `args` and leaves the exact key-like
    element needed by a following `OP_CHECKSIG`. -/
def KExecution (fragment : CoreFragment) (args : Stack) (key : StackElement)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ExecutesStackFrame (compile fragment) args [key] flags ctx

/-- The two exact output orders used by W wrappers. Wrapper `a` restores the
    protected element above its B result; wrapper `s` will leave the B result
    above the protected element. -/
inductive WStackOrder where
  | savedFirst
  | resultFirst
  deriving Repr, DecidableEq, BEq

namespace WStackOrder

/-- Materialize a W output prefix without hiding its order in an existential. -/
def outputs : WStackOrder → StackElement → StackElement → Stack
  | .savedFirst, saved, result => [saved, result]
  | .resultFirst, saved, result => [result, saved]

end WStackOrder

/-- A selected W-type execution runs below one protected main-stack element
    and returns the protected element and exact B result in the wrapper's
    declared order. -/
def WExecution (fragment : CoreFragment) (args : Stack) (result : StackElement)
    (order : WStackOrder) (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∀ saved : StackElement,
    ExecutesStackFrame (compile fragment) (saved :: args)
      (order.outputs saved result) flags ctx

/-- A B-type execution together with the truth value required by satisfaction
    or dissatisfaction. -/
def BExecutionOutcome (fragment : CoreFragment) (args : Stack) (expected : Bool)
    (flags : ScriptFlags) (ctx : TxContext) : Prop :=
  ∃ result, BExecution fragment args result flags ctx ∧
    castToBool result = expected

/-- A selected B-type execution over a serialized witness yields the existing
    clean-stack result when instantiated with empty surrounding stacks. -/
theorem BExecutionOutcome.cleanStackResult
    {fragment : CoreFragment} {witness : Witness} {expected : Bool}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecutionOutcome fragment witness.toInitialStack expected flags ctx) :
    CleanStackResult (compile fragment) witness flags ctx expected := by
  obtain ⟨result, frame, truth⟩ := executed
  refine ⟨result, [], ?_, truth⟩
  simpa [BExecution, ExecutesStackFrame, Executes, Witness.toInitialStack] using
    frame [] []

/-! ## Base-type composition -/

/-- Wrapper `c` places a signature below the K fragment's own arguments, then
    converts its exact key output into a boolean B result. -/
theorem KExecution.c
    {fragment : CoreFragment} {args : Stack} {key signature : StackElement}
    {valid : Bool} {flags : ScriptFlags} {ctx : TxContext}
    (executed : KExecution fragment args key flags ctx)
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx
      signature key = .ok valid) :
    BExecution (.c fragment) (args ++ [signature]) (boolToElement valid)
      flags ctx := by
  intro rest altStack
  have keyExec := executed (signature :: rest) altStack
  have checkExec :
      Eval [.op .OP_CHECKSIG] (key :: signature :: rest) altStack flags ctx
        (.success (boolToElement valid :: rest) altStack) := by
    cases valid with
    | false =>
        simpa [boolToElement] using
          (Eval.checksigFalse checked
            (Eval.done (stack := falseElement :: rest) (altStack := altStack)))
    | true =>
        simpa [boolToElement] using
          (Eval.checksigTrue checked
            (Eval.done (stack := trueElement :: rest) (altStack := altStack)))
  simpa [BExecution, KExecution, ExecutesStackFrame, compile,
    compileWithKeyHash, List.append_assoc] using Eval.append keyExec checkExec

/-- Wrapper `v` consumes a truthy B result and turns successful execution into
    the silent V stack shape. -/
theorem BExecution.v
    {fragment : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args result flags ctx)
    (truthy : castToBool result = true) :
    VExecution (.v fragment) args flags ctx := by
  intro rest altStack
  have fragmentExec := executed rest altStack
  have verifyExec :
      Eval [.op .OP_VERIFY] (result :: rest) altStack flags ctx
        (.success rest altStack) :=
    Eval.verifyTrue truthy
      (Eval.done (stack := rest) (altStack := altStack))
  simpa [BExecution, VExecution, ExecutesStackFrame, compile,
    compileWithKeyHash] using Eval.append fragmentExec verifyExec

/-- Wrapper `a` protects one main-stack item on the alternate stack while its
    B child executes, then restores that item above the child's result. -/
theorem BExecution.a
    {fragment : CoreFragment} {args : Stack} {result : StackElement}
    {flags : ScriptFlags} {ctx : TxContext}
    (executed : BExecution fragment args result flags ctx) :
    WExecution (.a fragment) args result .savedFirst flags ctx := by
  intro saved rest altStack
  have fragmentExec := executed rest (saved :: altStack)
  have restoreExec :
      Eval [.op .OP_FROMALTSTACK] (result :: rest) (saved :: altStack) flags ctx
        (.success (saved :: result :: rest) altStack) :=
    Eval.fromAltStackNext
      (Eval.done (stack := saved :: result :: rest) (altStack := altStack))
  have bodyExec := Eval.append fragmentExec restoreExec
  simpa [BExecution, WExecution, WStackOrder.outputs, ExecutesStackFrame,
    compile, compileWithKeyHash] using Eval.toAltStackNext bodyExec

/-! ## Primitive execution contracts -/

/-- `1` needs no arguments and leaves the canonical true element. -/
theorem one_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .one [] trueElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_one] using
    (Eval.pushNum 1 [] rest altStack flags ctx
      (.success (trueElement :: rest) altStack)
      (Eval.done (stack := trueElement :: rest) (altStack := altStack)))

/-- `0` needs no arguments and leaves the canonical false element. -/
theorem zero_execution (flags : ScriptFlags) (ctx : TxContext) :
    BExecution .zero [] falseElement flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash,
    scriptNum_zero] using
    (Eval.pushNum 0 [] rest altStack flags ctx
      (.success (falseElement :: rest) altStack)
      (Eval.done (stack := falseElement :: rest) (altStack := altStack)))

/-- `pk_k` needs no arguments of its own and leaves its exact public key. -/
theorem pk_k_execution (key : PubKey) (flags : ScriptFlags) (ctx : TxContext) :
    KExecution (.pk_k key) [] key.bytes flags ctx := by
  intro rest altStack
  simpa [KExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushDataNext (data := key.bytes)
      (Eval.done (stack := key.bytes :: rest) (altStack := altStack)))

/-- A satisfied relative timelock preserves arbitrary surrounding stacks and
    leaves its compiler-produced numeric operand. -/
theorem older_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : sequenceSatisfied n ctx) :
    BExecution (.older n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKSEQUENCEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checksequenceverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- A satisfied absolute timelock has the corresponding arbitrary-stack
    execution contract. -/
theorem after_execution
    {n : Nat} {flags : ScriptFlags} {ctx : TxContext}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (satisfied : locktimeSatisfied n ctx) :
    BExecution (.after n) [] (scriptNum n) flags ctx := by
  intro rest altStack
  simpa [BExecution, ExecutesStackFrame, compile, compileWithKeyHash] using
    (Eval.pushNum n [.op .OP_CHECKLOCKTIMEVERIFY] rest altStack flags ctx
      (.success (scriptNum n :: rest) altStack)
      (Eval.checklocktimeverify_success (scriptNum n) n rest [] altStack flags ctx
        (.success (scriptNum n :: rest) altStack) decoded (by omega) satisfied
        (Eval.done (stack := scriptNum n :: rest) (altStack := altStack))))

/-- The basic fragment cases whose witness algorithms need no numeric
    well-formedness premise. Timelocks have separate theorems below because
    their compiled Script-number must also satisfy the five-byte limit. -/
inductive BasicSatisfactionFragment : CoreFragment → Prop where
  | one : BasicSatisfactionFragment .one
  | cPkK (key : PubKey) : BasicSatisfactionFragment (.c (.pk_k key))

/-- A witness returned for a supported basic fragment has a satisfying
    arbitrary-stack B execution. Cryptographic and byte-encoding assumptions
    are kept at this execution boundary rather than baked into the frame API. -/
theorem satisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (generated : satisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack true flags env.txCtx := by
  cases supported with
  | one =>
      simp [satisfy] at generated
      subst witness
      exact ⟨trueElement, by simpa using one_execution flags env.txCtx,
        by native_decide⟩
  | cPkK key =>
      simp [satisfy] at generated
      obtain ⟨signature, signatureFor, rfl⟩ := generated
      have verified := sound.1 key signature signatureFor
      have checked := checkSigWithEncoding_true
        (encodings key signature signatureFor) verified
      refine ⟨trueElement, ?_, by native_decide⟩
      change BExecution (.c (.pk_k key)) [signature] trueElement flags env.txCtx
      simpa [boolToElement] using
        (KExecution.c (pk_k_execution key flags env.txCtx) checked)

/-- Every witness returned for a supported basic fragment is accepted by its
    compiled script under the environment transaction and modeled flags,
    provided the supplied material also passes the selected encoding checks. -/
theorem satisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : BasicSatisfactionFragment m)
    (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : satisfy m env = some witness) :
    Accepts ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_basic_execution supported sound encodings generated).cleanStackResult⟩

/-- The witness returned for a satisfied relative timelock has the reusable B
    execution contract before final clean-stack acceptance is imposed. -/
theorem satisfy_older_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    BExecutionOutcome (.older n) witness.toInitialStack true flags env.txCtx := by
  simp [satisfy] at generated
  rcases generated with ⟨satisfied, rfl⟩
  exact ⟨scriptNum n, by simpa using older_execution decoded satisfied, positive⟩

/-- A returned `older` witness is accepted whenever its compiler-produced
    numeric operand is valid and truthy. `WellFormed` supplies these numeric
    premises when this lemma is lifted into the general correctness theorem. -/
theorem satisfy_older_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.older n) env = some witness) :
    Accepts ctx (compile (.older n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_older_execution decoded positive generated).cleanStackResult⟩

/-- The witness returned for a satisfied absolute timelock likewise executes
    over arbitrary surrounding stacks. -/
theorem satisfy_after_execution
    {n : Nat} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    BExecutionOutcome (.after n) witness.toInitialStack true flags env.txCtx := by
  simp [satisfy] at generated
  rcases generated with ⟨satisfied, rfl⟩
  exact ⟨scriptNum n, by simpa using after_execution decoded satisfied, positive⟩

/-- Absolute timelocks use the same transaction predicate and numeric boundary
    as relational Script execution. -/
theorem satisfy_after_sound
    {ctx : ScriptContext} {n : Nat} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (decoded : decodeScriptNum (scriptNum n) flags.minimalData
      maxTimelockScriptNumBytes = .ok n)
    (positive : castToBool (scriptNum n) = true)
    (generated : satisfy (.after n) env = some witness) :
    Accepts ctx (compile (.after n)) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (satisfy_after_execution decoded positive generated).cleanStackResult⟩

/-- A returned basic dissatisfaction has a false B execution over every
    surrounding main and alternate stack. -/
theorem dissatisfy_basic_execution
    {m : CoreFragment} {env : SatEnv} {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨ ∃ key, m = .c (.pk_k key))
    (sound : env.Sound)
    (keys : ∀ key, m = .c (.pk_k key) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (generated : dissatisfy m env = some witness) :
    BExecutionOutcome m witness.toInitialStack false flags env.txCtx := by
  rcases supported with rfl | ⟨key, rfl⟩
  · simp [dissatisfy] at generated
    subst witness
    exact ⟨falseElement, by simpa using zero_execution flags env.txCtx,
      by native_decide⟩
  · simp [dissatisfy] at generated
    subst witness
    have rejected := sound.2.1 key
    have checked := checkSigWithEncoding_empty (keys key rfl) rejected
    refine ⟨falseElement, ?_, by native_decide⟩
    change BExecution (.c (.pk_k key)) [falseElement] falseElement flags env.txCtx
    simpa [boolToElement] using
      (KExecution.c (pk_k_execution key flags env.txCtx) checked)

/-- Every witness returned for a supported basic dissatisfiable fragment
    executes successfully to a clean false result when the fragment's key
    passes the public-key encoding check, even with an empty signature. -/
theorem dissatisfy_basic_sound
    {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
    {witness : Witness} {flags : ScriptFlags}
    (supported : m = .zero ∨ ∃ key, m = .c (.pk_k key))
    (sound : env.Sound)
    (keys : ∀ key, m = .c (.pk_k key) →
      checkSigEncodingFor flags env.txCtx.sigVersion falseElement key.bytes = .ok ())
    (version : ModeledContextVersion ctx env.txCtx)
    (modeled : ModeledContextFlags ctx flags)
    (generated : dissatisfy m env = some witness) :
    Dissatisfies ctx (compile m) witness flags env.txCtx := by
  exact ⟨modeled, version,
    (dissatisfy_basic_execution supported sound keys generated).cleanStackResult⟩

end LeanMiniscript.Miniscript
