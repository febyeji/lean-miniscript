import LeanMiniscript.Miniscript.Acceptance
import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Validation
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Theorem 1: Type System Soundness -/

/-- The context, structural, and correctness-typing evidence needed before a
    semantic claim is made about a core fragment. -/
structure ValidTypedFragment (ctx : ScriptContext) (m : CoreFragment)
    (ty : MiniType) : Prop where
  wellFormed : m.WellFormed ctx
  hasType : HasType ctx m ty

/-- A top-level Miniscript is a context-valid core fragment with B base type. -/
def ValidMiniscript (ctx : ScriptContext) (m : CoreFragment) : Prop :=
  ∃ mods, ValidTypedFragment ctx m ⟨.B, mods⟩

/-- A top-level Miniscript carrying the correctness type system's `d`
    guarantee. -/
def ValidDissatisfiableMiniscript (ctx : ScriptContext)
    (m : CoreFragment) : Prop :=
  ∃ mods, ValidTypedFragment ctx m ⟨.B, mods⟩ ∧ mods.d = true

/-- Surface validity is stated through the single core desugaring boundary. -/
def ValidTypedSurfaceFragment (ctx : ScriptContext) (m : SurfaceFragment)
    (ty : MiniType) : Prop :=
  ValidTypedFragment ctx (desugar m) ty

/-- A top-level surface Miniscript is valid exactly when its desugared core is. -/
def ValidSurfaceMiniscript (ctx : ScriptContext)
    (m : SurfaceFragment) : Prop :=
  ValidMiniscript ctx (desugar m)

/-- Surface dissatisfaction validity is inherited from desugared core. -/
def ValidDissatisfiableSurfaceMiniscript (ctx : ScriptContext)
    (m : SurfaceFragment) : Prop :=
  ValidDissatisfiableMiniscript ctx (desugar m)

/-- The two successful output orders available to a W base fragment. -/
inductive BaseWOutputOrder where
  | savedFirst
  | resultFirst
  deriving Repr, DecidableEq, BEq

namespace BaseWOutputOrder

/-- Materialize a W output prefix in its exact main-stack order. -/
def outputs : BaseWOutputOrder → StackElement → StackElement → Stack
  | .savedFirst, saved, result => [saved, result]
  | .resultFirst, saved, result => [result, saved]

end BaseWOutputOrder

/-- The successful main-stack effect associated with each Miniscript base
    type. The input prefix records the arguments consumed by the fragment;
    everything below that frame is preserved exactly. A W fragment additionally
    protects one element above its arguments and may restore the two output
    elements in either wrapper-defined order. -/
inductive BaseStackEffect : BaseType → Stack → Stack → Prop where
  | b (args rest : Stack) (result : StackElement) :
      BaseStackEffect .B (args ++ rest) (result :: rest)
  | v (args rest : Stack) :
      BaseStackEffect .V (args ++ rest) rest
  | k (args rest : Stack) (key : StackElement) :
      BaseStackEffect .K (args ++ rest) (key :: rest)
  | w (args rest : Stack) (saved result : StackElement)
      (order : BaseWOutputOrder) :
      BaseStackEffect .W (saved :: args ++ rest)
        (order.outputs saved result ++ rest)

/-- Arbitrary-input safety for a base type. Every successful execution has the
    base type's exact stack-frame effect and restores the incoming alt stack.
    Modeled Script failures remain valid terminal outcomes. -/
def BaseTypeGuarantee (m : CoreFragment) (base : BaseType) : Prop :=
  ∀ (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
      (outcome : ExecResult),
    Eval (compile m) stack altStack flags ctx outcome →
    match outcome with
    | .success finalStack finalAltStack =>
        finalAltStack = altStack ∧ BaseStackEffect base stack finalStack
    | .failure _ => True

/-- Candidate-level meaning of the `d` modifier: a raw dissatisfaction exists
    for every material environment. The raw projection intentionally includes
    canonical `DONTUSE` rows such as hashlock dissatisfactions, before the later
    malleability filter selects usable witnesses. -/
def UnconditionalDissatisfaction (m : CoreFragment) : Prop :=
  ∀ env : SatEnv, ∃ witness,
    (satisfactionCandidates m env).dsat.witness? = some witness

/-- What a K-type fragment guarantees:
    Given a witness stack, executing the compiled script either pushes exactly
    one element (the key) while preserving the rest, or aborts with a modeled
    Script error. Composite K fragments may contain a V-type prefix, so failure
    must remain possible even though a successful K fragment leaves a key. -/
def KTypeGuarantee (m : CoreFragment) : Prop :=
  ∀ (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    (∃ (keyElem : StackElement),
      Eval (compile m) stack altStack flags ctx
        (.success (keyElem :: stack) altStack)) ∨
    ∃ (err : ScriptError),
      Eval (compile m) stack altStack flags ctx (.failure err)

/-- Soundness for pk_k: a pk_k fragment has K-type behavior.

    pk_k(key) compiles to `[pushData key]`.
    Executing this on any stack pushes `key` on top, which is exactly the
    current K-type guarantee predicate. -/
theorem pk_k_soundness (key : PubKey) :
    KTypeGuarantee (.pk_k key) := by
  intro stack altStack flags ctx
  exact Or.inl ⟨key, by
    simpa [compile, compileWithKeyHash] using
      (Eval.pushDataNext (data := key) Eval.done)⟩

/-- Regression for a supported K-type composite whose V-type prefix aborts.

    `and_v(v(0), pk_k(key))` has Ko type, but compiles to a leading false
    `VERIFY`. Its K guarantee is therefore witnessed by the modeled failure
    branch rather than an impossible unconditional success. -/
theorem and_v_v_zero_pk_k_soundness (key : PubKey) :
    KTypeGuarantee (.and_v (.v .zero) (.pk_k key)) := by
  intro stack altStack flags ctx
  right
  refine ⟨.verify, ?_⟩
  apply Eval.pushNum
  apply Eval.verify_failure
  native_decide

/-- What a B-type fragment with 'o' modifier guarantees:
    Consumes exactly one witness element from the stack and pushes
    exactly one result element (nonzero for success, zero for failure).
    Stack below the witness is preserved. -/
def BTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    (∃ (result : StackElement),
      Eval (compile m) (wit :: stack) altStack flags ctx
        (.success (result :: stack) altStack)) ∨
    ∃ (err : ScriptError),
      Eval (compile m) (wit :: stack) altStack flags ctx (.failure err)

/-- Soundness for c(pk_k(key)): the wrapped form has Bo-type behavior.

    c(pk_k(key)) compiles to `[pushData key] ++ [OP_CHECKSIG]`.
    Given a signature `wit`, the script pushes the key, checks the signature,
    consumes the witness, and leaves a boolean result on the original stack. -/
theorem c_pk_k_soundness (key : PubKey) :
    BTypeOGuarantee (.c (.pk_k key)) := by
  intro wit stack altStack flags ctx
  cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx wit key with
  | error error =>
      right
      refine ⟨error, ?_⟩
      simpa [compile, compileWithKeyHash] using
        (Eval.pushDataNext (data := key)
          (Eval.checksig_encoding_failure key wit stack [] altStack flags ctx error checked))
  | ok valid =>
      cases valid with
      | false =>
          left
          refine ⟨falseElement, ?_⟩
          simpa [compile, compileWithKeyHash] using
            (Eval.pushDataNext (data := key) (Eval.checksigFalse checked Eval.done))
      | true =>
          left
          refine ⟨trueElement, ?_⟩
          simpa [compile, compileWithKeyHash] using
            (Eval.pushDataNext (data := key) (Eval.checksigTrue checked Eval.done))

/-- What a V-type fragment with 'o' modifier guarantees:
    Consumes one witness element. On success, the stack below is unchanged
    (V-type pushes nothing). On failure, the script aborts.
    This is the key property: V-type either passes silently or kills execution. -/
def VTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    Eval (compile m) (wit :: stack) altStack flags ctx (.success stack altStack) ∨
    ∃ (err : ScriptError), Eval (compile m) (wit :: stack) altStack flags ctx (.failure err)

/-- Soundness for v(c(pk_k(key))): wrapper composition produces V-type behavior.

    v(c(pk_k(key))) compiles to `[pushData key, OP_CHECKSIGVERIFY]`. A valid
    signature verifies and leaves the original stack unchanged; an invalid
    signature reaches the opcode-specific failure. -/
theorem v_c_pk_k_soundness (key : PubKey) :
    VTypeOGuarantee (.v (.c (.pk_k key))) := by
  intro wit stack altStack flags ctx
  have compiled : compile (.v (.c (.pk_k key))) =
      [.pushData key, .op .OP_CHECKSIGVERIFY] := by
    change compileVerify ([.pushData key] ++ [.op .OP_CHECKSIG]) = _
    rw [compileVerify_append_singleton]
    rfl
  rw [compiled]
  cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx wit key with
  | error error =>
      right
      refine ⟨error, ?_⟩
      exact Eval.pushDataNext (data := key)
        (Eval.checksigverify_encoding_failure key wit stack [] altStack
          flags ctx error checked)
  | ok valid =>
      cases valid with
      | false =>
          right
          refine ⟨.checkSigVerify, ?_⟩
          exact Eval.pushDataNext (data := key)
            (Eval.checksigverify_failure key wit stack [] altStack flags ctx checked)
      | true =>
          left
          exact Eval.pushDataNext (data := key)
            (Eval.checksigverify_success key wit stack [] altStack flags ctx
              (.success stack altStack) checked Eval.done)

/-- What a W-type fragment with 'o' modifier guarantees in the current
    stack-shape model:
    Temporarily protects the top stack element on the alt stack, executes a
    B-type one-argument fragment below it, and restores the protected element
    above the boolean result on success. Like the other composite guarantees,
    it also admits a modeled terminal Script error such as NULLFAIL. -/
def WTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (saved wit : StackElement) (stack altStack : Stack)
      (flags : ScriptFlags) (ctx : TxContext),
    (∃ (result : StackElement),
      Eval (compile m) (saved :: wit :: stack) altStack flags ctx
        (.success (saved :: result :: stack) altStack)) ∨
    ∃ (err : ScriptError),
      Eval (compile m) (saved :: wit :: stack) altStack flags ctx (.failure err)

/-- Soundness for a(c(pk_k(key))): wrapper `a` turns the Bo behavior of
    c(pk_k(key)) into the corresponding W-type behavior by moving the protected
    top stack element through the alt stack. -/
theorem a_c_pk_k_soundness (key : PubKey) :
    WTypeOGuarantee (.a (.c (.pk_k key))) := by
  intro saved wit stack altStack flags ctx
  cases checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx wit key with
  | error error =>
      right
      refine ⟨error, ?_⟩
      simpa [compile, compileWithKeyHash] using
        (Eval.toAltStackNext (x := saved)
          (Eval.pushDataNext (data := key)
            (Eval.checksig_encoding_failure key wit stack [.op .OP_FROMALTSTACK]
              (saved :: altStack) flags ctx error checked)))
  | ok valid =>
      cases valid with
      | false =>
          left
          refine ⟨falseElement, ?_⟩
          simpa [compile, compileWithKeyHash] using
            (Eval.toAltStackNext (x := saved)
              (Eval.pushDataNext (data := key)
                (Eval.checksigFalse checked (Eval.fromAltStackNext (x := saved) Eval.done))))
      | true =>
          left
          refine ⟨trueElement, ?_⟩
          simpa [compile, compileWithKeyHash] using
            (Eval.toAltStackNext (x := saved)
              (Eval.pushDataNext (data := key)
                (Eval.checksigTrue checked (Eval.fromAltStackNext (x := saved) Eval.done))))

/-- `pk_k` satisfies the arbitrary-input K stack-frame contract. -/
theorem pk_k_base_type_soundness (key : PubKey) :
    BaseTypeGuarantee (.pk_k key) .K := by
  intro stack altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      have canonical : Eval (compile (.pk_k key)) stack altStack flags ctx
          (.success (key :: stack) altStack) := by
        simpa [compile, compileWithKeyHash] using
          (Eval.pushDataNext (data := key) Eval.done)
      have equal := Eval.result_unique evaluated canonical
      cases equal
      exact ⟨rfl, .k [] stack key⟩

/-- `c(pk_k)` satisfies the arbitrary-input B stack-frame contract, including
    the empty-stack failure boundary. -/
theorem c_pk_k_base_type_soundness (key : PubKey) :
    BaseTypeGuarantee (.c (.pk_k key)) .B := by
  intro input altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      cases input with
      | nil =>
          have failed : Eval (compile (.c (.pk_k key))) [] altStack flags ctx
              (.failure .stackUnderflow) := by
            simpa [compile, compileWithKeyHash] using
              (Eval.pushDataNext (data := key)
                (Eval.fixedArityStackUnderflow
                  (opcode := .OP_CHECKSIG) (required := 2)
                  (arity := rfl) (underflow := by simp)))
          have equal := Eval.result_unique evaluated failed
          contradiction
      | cons witness rest =>
          rcases c_pk_k_soundness key witness rest altStack flags ctx with
            succeeded | failed
          · rcases succeeded with ⟨result, canonical⟩
            have equal := Eval.result_unique evaluated canonical
            cases equal
            exact ⟨rfl, .b [witness] rest result⟩
          · rcases failed with ⟨error, canonical⟩
            have equal := Eval.result_unique evaluated canonical
            contradiction

/-- `v(c(pk_k))` satisfies the arbitrary-input V stack-frame contract,
    including the empty-stack failure boundary. -/
theorem v_c_pk_k_base_type_soundness (key : PubKey) :
    BaseTypeGuarantee (.v (.c (.pk_k key))) .V := by
  intro input altStack flags ctx outcome evaluated
  have compiled : compile (.v (.c (.pk_k key))) =
      [.pushData key, .op .OP_CHECKSIGVERIFY] := by
    change compileVerify ([.pushData key] ++ [.op .OP_CHECKSIG]) = _
    rw [compileVerify_append_singleton]
    rfl
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      cases input with
      | nil =>
          have failed : Eval (compile (.v (.c (.pk_k key)))) [] altStack flags ctx
              (.failure .stackUnderflow) := by
            rw [compiled]
            exact Eval.pushDataNext (data := key)
              (Eval.fixedArityStackUnderflow
                (opcode := .OP_CHECKSIGVERIFY) (required := 2)
                (arity := rfl) (underflow := by simp))
          have equal := Eval.result_unique evaluated failed
          contradiction
      | cons witness rest =>
          rcases v_c_pk_k_soundness key witness rest altStack flags ctx with
            succeeded | failed
          · have effect : BaseStackEffect .V (witness :: rest) rest :=
              .v [witness] rest
            have equal := Eval.result_unique evaluated succeeded
            cases equal
            exact ⟨rfl, effect⟩
          · rcases failed with ⟨error, canonical⟩
            have equal := Eval.result_unique evaluated canonical
            contradiction

/-- `a(c(pk_k))` satisfies the arbitrary-input W stack-frame contract,
    including both insufficient-input failure boundaries. -/
theorem a_c_pk_k_base_type_soundness (key : PubKey) :
    BaseTypeGuarantee (.a (.c (.pk_k key))) .W := by
  intro input altStack flags ctx outcome evaluated
  cases outcome with
  | failure error => trivial
  | success finalStack finalAltStack =>
      cases input with
      | nil =>
          have failed : Eval (compile (.a (.c (.pk_k key)))) [] altStack flags ctx
              (.failure .stackUnderflow) := by
            simpa [compile, compileWithKeyHash] using
              (Eval.fixedArityStackUnderflow
                (opcode := .OP_TOALTSTACK) (required := 1)
                (arity := rfl) (underflow := by decide))
          have equal := Eval.result_unique evaluated failed
          contradiction
      | cons saved tail =>
          cases tail with
          | nil =>
              have failed :
                  Eval (compile (.a (.c (.pk_k key)))) [saved] altStack flags ctx
                    (.failure .stackUnderflow) := by
                simpa [compile, compileWithKeyHash] using
                  (Eval.toAltStackNext (x := saved)
                    (Eval.pushDataNext (data := key)
                      (Eval.fixedArityStackUnderflow
                        (opcode := .OP_CHECKSIG) (required := 2)
                        (arity := rfl) (underflow := by simp))))
              have equal := Eval.result_unique evaluated failed
              contradiction
          | cons witness rest =>
              rcases a_c_pk_k_soundness key saved witness rest altStack flags ctx with
                succeeded | failed
              · rcases succeeded with ⟨result, canonical⟩
                have equal := Eval.result_unique evaluated canonical
                cases equal
                exact ⟨rfl, .w [witness] rest saved result .savedFirst⟩
              · rcases failed with ⟨error, canonical⟩
                have equal := Eval.result_unique evaluated canonical
                contradiction

/-! `TypeSoundnessProofs` extends these local examples to every `HasType`
constructor and proves the complete Core and Surface type-soundness contracts. -/

/-! ## Theorem 2: Satisfaction Correctness -/

/-- Target contract for core satisfaction. Returned serialized-order witnesses
    must be accepted by the compiled script in the environment's transaction
    context, with both cryptographic and encoding soundness premises. -/
def SatisfactionCorrectnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidMiniscript ctx m →
    env.Sound →
    env.EncodingSound flags →
    ModeledContextVersion ctx env.txCtx →
    ModeledContextFlags ctx flags →
    satisfy m env = some witness →
    Accepts ctx (compile m) witness flags env.txCtx

/-- Surface satisfaction is the core contract after desugaring. -/
def SatisfactionCorrectnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidSurfaceMiniscript ctx m →
    env.Sound →
    env.EncodingSound flags →
    ModeledContextVersion ctx env.txCtx →
    ModeledContextFlags ctx flags →
    satisfy (desugar m) env = some witness →
    Accepts ctx (compileSurface m) witness flags env.txCtx

/-! ## Theorem 3: Dissatisfaction Correctness -/

/-- Target contract for core dissatisfaction. The returned witness must execute
    successfully to a clean false result rather than aborting. Encoding
    soundness covers selected signatures; context-valid keys plus the modeled
    version and flags establish canonical empty-signature checks. -/
def DissatisfactionCorrectnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidDissatisfiableMiniscript ctx m →
    env.Sound →
    env.EncodingSound flags →
    ModeledContextVersion ctx env.txCtx →
    ModeledContextFlags ctx flags →
    dissatisfy m env = some witness →
    Dissatisfies ctx (compile m) witness flags env.txCtx

/-- Surface dissatisfaction is the core contract after desugaring. Its
    encoding premise matches the core target exactly. -/
def DissatisfactionCorrectnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidDissatisfiableSurfaceMiniscript ctx m →
    env.Sound →
    env.EncodingSound flags →
    ModeledContextVersion ctx env.txCtx →
    ModeledContextFlags ctx flags →
    dissatisfy (desugar m) env = some witness →
    Dissatisfies ctx (compileSurface m) witness flags env.txCtx

/-! ## MINIMALIF Bug Reproduction

  Historical context:
  Before the fix, the typing rule for `or_i` did not require MINIMALIF flag,
  allowing a malicious miner to use non-minimal IF arguments to bypass
  the intended spending condition.

  Plan:
  1. Define the PRE-FIX typing rule
  2. Show that soundness does NOT hold under the pre-fix rule (counterexample)
  3. Define the POST-FIX typing rule
  4. Prove soundness holds under the post-fix rule
-/

/-!
TODO(theorem): MINIMALIF regression.

Core proof tasks:
- Define pre-fix and post-fix typing rules for the core fragments affected by
  `or_i`.
- Construct the pre-fix counterexample with a non-minimal IF argument.
- Prove the post-fix rule restores the relevant soundness property.
- Check the surface `l:`/`u:` forms through `desugar`.
-/

end LeanMiniscript.Miniscript
