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
  by_cases h : checkSig wit key ctx.sigHash = true
  · exact Or.inl ⟨trueElement,
      by simpa [compile, compileWithKeyHash] using
      (Eval.pushDataNext (data := key)
        (Eval.checksigTrue (pubkey := key) (sig := wit) h Eval.done))⟩
  · simp at h
    exact Or.inl ⟨falseElement,
      by simpa [compile, compileWithKeyHash] using
      (Eval.pushDataNext (data := key)
        (Eval.checksigFalse (pubkey := key) (sig := wit) h Eval.done))⟩

/-- What a V-type fragment with 'o' modifier guarantees:
    Consumes one witness element. On success, the stack below is unchanged
    (V-type pushes nothing). On failure, the script aborts.
    This is the key property: V-type either passes silently or kills execution. -/
def VTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    Eval (compile m) (wit :: stack) altStack flags ctx (.success stack altStack) ∨
    ∃ (err : ScriptError), Eval (compile m) (wit :: stack) altStack flags ctx (.failure err)

/-- Soundness for v(c(pk_k(key))): wrapper composition produces V-type behavior.

    v(c(pk_k(key))) compiles to `[pushData key, OP_CHECKSIG] ++ [OP_VERIFY]`.
    A valid signature verifies and leaves the original stack unchanged; an
    invalid signature reaches the modeled VERIFY failure. -/
theorem v_c_pk_k_soundness (key : PubKey) :
    VTypeOGuarantee (.v (.c (.pk_k key))) := by
  intro wit stack altStack flags ctx
  by_cases h : checkSig wit key ctx.sigHash = true
  · left
    simpa [compile, compileWithKeyHash] using
      (Eval.pushDataNext (data := key)
        (Eval.checksigTrue (pubkey := key) (sig := wit) h
          (Eval.verifyTrue (top := trueElement) (by native_decide) Eval.done)))
  · right
    simp at h
    exact ⟨.verify,
      by simpa [compile, compileWithKeyHash] using
      (Eval.pushDataNext (data := key)
        (Eval.checksigFalse (pubkey := key) (sig := wit) h
          (Eval.verifyFalse (top := falseElement) (by native_decide))))⟩

/-- What a W-type fragment with 'o' modifier guarantees in the current
    stack-shape model:
    Temporarily protects the top stack element on the alt stack, executes a
    B-type one-argument fragment below it, and restores the protected element
    above the boolean result. -/
def WTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (saved wit : StackElement) (stack altStack : Stack)
      (flags : ScriptFlags) (ctx : TxContext),
    ∃ (result : StackElement),
      Eval (compile m) (saved :: wit :: stack) altStack flags ctx
        (.success (saved :: result :: stack) altStack)

/-- Type cases for which this file has a reusable, non-vacuous semantic
    predicate. Unsupported combinations are excluded explicitly. In particular,
    W types are not yet included because their protected-stack contract needs a
    general statement beyond the local `a(c(pk_k))` example. -/
def SupportedMiniType (ty : MiniType) : Prop :=
  (ty.base = .K ∧ ty.mods.o = true) ∨
  (ty.base = .B ∧ ty.mods.o = true) ∨
  (ty.base = .V ∧ ty.mods.o = true)

/-- Semantic guarantee selected by a currently supported Miniscript type.
    Unlike the previous selector, no branch reduces to `True`. -/
def MiniTypeGuarantee (m : CoreFragment) (ty : MiniType) : Prop :=
  (ty.base = .K ∧ ty.mods.o = true ∧ KTypeGuarantee m) ∨
  (ty.base = .B ∧ ty.mods.o = true ∧ BTypeOGuarantee m) ∨
  (ty.base = .V ∧ ty.mods.o = true ∧ VTypeOGuarantee m)

/-- The eventual core type-soundness theorem, stated as a proposition so the
    repository has a shared target without introducing `sorry`. It is explicit
    about the modifier cases covered by the current semantic predicates. -/
def TypeSoundnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {ty : MiniType},
    ValidTypedFragment ctx m ty →
    SupportedMiniType ty →
    MiniTypeGuarantee m ty

/-- Surface soundness should be the core theorem after desugaring. -/
def TypeSoundnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {ty : MiniType},
    ValidTypedSurfaceFragment ctx m ty →
    SupportedMiniType ty →
    MiniTypeGuarantee (desugar m) ty

/-- Soundness for a(c(pk_k(key))): wrapper `a` turns the Bo behavior of
    c(pk_k(key)) into the corresponding W-type behavior by moving the protected
    top stack element through the alt stack. -/
theorem a_c_pk_k_soundness (key : PubKey) :
    WTypeOGuarantee (.a (.c (.pk_k key))) := by
  intro saved wit stack altStack flags ctx
  by_cases h : checkSig wit key ctx.sigHash = true
  · refine ⟨trueElement, ?_⟩
    simpa [compile, compileWithKeyHash] using
      (Eval.toAltStackNext (x := saved)
        (Eval.pushDataNext (data := key)
          (Eval.checksigTrue (pubkey := key) (sig := wit) h
            (Eval.fromAltStackNext (x := saved) Eval.done))))
  · simp at h
    refine ⟨falseElement, ?_⟩
    simpa [compile, compileWithKeyHash] using
      (Eval.toAltStackNext (x := saved)
        (Eval.pushDataNext (data := key)
          (Eval.checksigFalse (pubkey := key) (sig := wit) h
            (Eval.fromAltStackNext (x := saved) Eval.done))))

/-- The `pk_k` example packaged through the shared semantic selector. -/
theorem pk_k_mini_type_soundness (key : PubKey) :
    MiniTypeGuarantee (.pk_k key)
      ⟨.K, { o := true, n := true, d := true, u := true }⟩ := by
  simpa [MiniTypeGuarantee] using pk_k_soundness key

/-- The `c(pk_k)` example packaged through the shared semantic selector. -/
theorem c_pk_k_mini_type_soundness (key : PubKey) :
    MiniTypeGuarantee (.c (.pk_k key))
      ⟨.B, { o := true, n := true, d := true, u := true }⟩ := by
  simpa [MiniTypeGuarantee] using c_pk_k_soundness key

/-- The `v(c(pk_k))` example packaged through the shared semantic selector. -/
theorem v_c_pk_k_mini_type_soundness (key : PubKey) :
    MiniTypeGuarantee (.v (.c (.pk_k key)))
      ⟨.V, { o := true, n := true }⟩ := by
  simpa [MiniTypeGuarantee] using v_c_pk_k_soundness key

/-!
TODO(theorem): promote these AST-level leaf and wrapper lemmas into the main
core type-soundness theorem.

Core proof tasks:
- Extend `SupportedMiniType` only when the corresponding non-vacuous semantic
  predicate is defined.
- Prove the theorem by induction over the `HasType` derivation, with separate
  lemmas for leaves, connectives, wrappers, threshold, `multi`, and `multi_a`.
- Prove `TypeSoundnessSurface` as a corollary through `desugar`.
-/

/-! ## Theorem 2: Satisfaction Correctness -/

/-- Target contract for core satisfaction. Returned serialized-order witnesses
    must be accepted by the compiled script in the environment's transaction
    context. -/
def SatisfactionCorrectnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidMiniscript ctx m →
    env.Sound →
    ModeledContextFlags ctx flags →
    satisfy m env = some witness →
    Accepts ctx (compile m) witness flags env.txCtx

/-- Surface satisfaction is the core contract after desugaring. -/
def SatisfactionCorrectnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidSurfaceMiniscript ctx m →
    env.Sound →
    ModeledContextFlags ctx flags →
    satisfy (desugar m) env = some witness →
    Accepts ctx (compileSurface m) witness flags env.txCtx

/-! ## Theorem 3: Dissatisfaction Correctness -/

/-- Target contract for core dissatisfaction. The returned witness must execute
    successfully to a clean false result rather than aborting. -/
def DissatisfactionCorrectnessCore : Prop :=
  ∀ {ctx : ScriptContext} {m : CoreFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidDissatisfiableMiniscript ctx m →
    env.Sound →
    ModeledContextFlags ctx flags →
    dissatisfy m env = some witness →
    Dissatisfies ctx (compile m) witness flags env.txCtx

/-- Surface dissatisfaction is the core contract after desugaring. -/
def DissatisfactionCorrectnessSurface : Prop :=
  ∀ {ctx : ScriptContext} {m : SurfaceFragment} {env : SatEnv}
      {witness : Witness} {flags : ScriptFlags},
    ValidDissatisfiableSurfaceMiniscript ctx m →
    env.Sound →
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
