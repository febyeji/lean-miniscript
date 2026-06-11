import LeanMiniscript.Script.BigStep
import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Satisfaction

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! ## Theorem 1: Type System Soundness -/

/-- What a K-type fragment guarantees:
    Given a witness stack, executing the compiled script pushes exactly one
    element (the key) onto the stack, preserving the rest. -/
def KTypeGuarantee (m : CoreFragment) : Prop :=
  ∀ (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    ∃ (keyElem : StackElement),
      Eval (compile m) stack altStack flags ctx (.success (keyElem :: stack) altStack)

/-- Soundness for pk_k: a pk_k fragment has K-type behavior.

    pk_k(key) compiles to `[pushData key]`.
    Executing this on any stack pushes `key` on top, which is exactly the
    current K-type guarantee predicate. -/
theorem pk_k_soundness (key : PubKey) :
    KTypeGuarantee (.pk_k key) := by
  intro stack altStack flags ctx
  exact ⟨key, by
    simpa [compile] using Eval.pushData key [] stack altStack flags ctx _
      (Eval.empty (key :: stack) altStack flags ctx)⟩

/-- What a B-type fragment with 'o' modifier guarantees:
    Consumes exactly one witness element from the stack and pushes
    exactly one result element (nonzero for success, zero for failure).
    Stack below the witness is preserved. -/
def BTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    ∃ (result : StackElement),
      Eval (compile m) (wit :: stack) altStack flags ctx
        (.success (result :: stack) altStack)

/-- Soundness for c(pk_k(key)): the wrapped form has Bo-type behavior.

    c(pk_k(key)) compiles to `[pushData key] ++ [OP_CHECKSIG]`.
    Given a signature `wit`, the script pushes the key, checks the signature,
    consumes the witness, and leaves a boolean result on the original stack. -/
theorem c_pk_k_soundness (key : PubKey) :
    BTypeOGuarantee (.c (.pk_k key)) := by
  intro wit stack altStack flags ctx
  by_cases h : checkSig wit key ctx.sigHash = true
  · exact ⟨trueElement,
      by simpa [compile] using
      (Eval.seq [.pushData key] [.op .OP_CHECKSIG] (wit :: stack)
        (key :: wit :: stack) altStack altStack flags ctx _
        (Eval.pushData key [] (wit :: stack) altStack flags ctx _
          (Eval.empty (key :: wit :: stack) altStack flags ctx))
        (Eval.checksig_success key wit stack [] altStack flags ctx _
          h (Eval.empty (trueElement :: stack) altStack flags ctx)))⟩
  · simp at h
    exact ⟨falseElement,
      by simpa [compile] using
      (Eval.seq [.pushData key] [.op .OP_CHECKSIG] (wit :: stack)
        (key :: wit :: stack) altStack altStack flags ctx _
        (Eval.pushData key [] (wit :: stack) altStack flags ctx _
          (Eval.empty (key :: wit :: stack) altStack flags ctx))
        (Eval.checksig_failure key wit stack [] altStack flags ctx _
          h (Eval.empty (falseElement :: stack) altStack flags ctx)))⟩

/-- What a V-type fragment with 'o' modifier guarantees:
    Consumes one witness element. On success, the stack below is unchanged
    (V-type pushes nothing). On failure, the script aborts.
    This is the key property: V-type either passes silently or kills execution. -/
def VTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    Eval (compile m) (wit :: stack) altStack flags ctx (.success stack altStack) ∨
    ∃ (msg : String), Eval (compile m) (wit :: stack) altStack flags ctx (.failure msg)

/-- Soundness for v(c(pk_k(key))): wrapper composition produces V-type behavior.

    v(c(pk_k(key))) compiles to `[pushData key, OP_CHECKSIG] ++ [OP_VERIFY]`.
    A valid signature verifies and leaves the original stack unchanged; an
    invalid signature reaches the modeled VERIFY failure. -/
theorem v_c_pk_k_soundness (key : PubKey) :
    VTypeOGuarantee (.v (.c (.pk_k key))) := by
  intro wit stack altStack flags ctx
  by_cases h : checkSig wit key ctx.sigHash = true
  · left
    simpa [compile] using
      (Eval.seq [.pushData key, .op .OP_CHECKSIG] [.op .OP_VERIFY]
        (wit :: stack) (trueElement :: stack) altStack altStack flags ctx _
        (Eval.seq [.pushData key] [.op .OP_CHECKSIG]
          (wit :: stack) (key :: wit :: stack) altStack altStack flags ctx _
          (Eval.pushData key [] (wit :: stack) altStack flags ctx _
            (Eval.empty (key :: wit :: stack) altStack flags ctx))
          (Eval.checksig_success key wit stack [] altStack flags ctx _
            h (Eval.empty (trueElement :: stack) altStack flags ctx)))
        (Eval.verify_success trueElement stack [] altStack flags ctx _
          (by native_decide) (Eval.empty stack altStack flags ctx)))
  · right
    simp at h
    exact ⟨"VERIFY failed",
      by simpa [compile] using
      (Eval.seq [.pushData key, .op .OP_CHECKSIG] [.op .OP_VERIFY]
        (wit :: stack) (falseElement :: stack) altStack altStack flags ctx _
        (Eval.seq [.pushData key] [.op .OP_CHECKSIG]
          (wit :: stack) (key :: wit :: stack) altStack altStack flags ctx _
          (Eval.pushData key [] (wit :: stack) altStack flags ctx _
            (Eval.empty (key :: wit :: stack) altStack flags ctx))
          (Eval.checksig_failure key wit stack [] altStack flags ctx _
            h (Eval.empty (falseElement :: stack) altStack flags ctx)))
        (Eval.verify_failure falseElement stack [] altStack flags ctx
          (by native_decide)))⟩

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

/-- Soundness for a(c(pk_k(key))): wrapper `a` turns the Bo behavior of
    c(pk_k(key)) into the corresponding W-type behavior by moving the protected
    top stack element through the alt stack. -/
theorem a_c_pk_k_soundness (key : PubKey) :
    WTypeOGuarantee (.a (.c (.pk_k key))) := by
  intro saved wit stack altStack flags ctx
  by_cases h : checkSig wit key ctx.sigHash = true
  · refine ⟨trueElement, ?_⟩
    simpa [compile] using
    (Eval.toAltStack saved (wit :: stack) altStack
      [.pushData key, .op .OP_CHECKSIG, .op .OP_FROMALTSTACK] flags ctx _
      (Eval.pushData key [.op .OP_CHECKSIG, .op .OP_FROMALTSTACK]
        (wit :: stack) (saved :: altStack) flags ctx _
        (Eval.checksig_success key wit stack [.op .OP_FROMALTSTACK]
          (saved :: altStack) flags ctx _
          h
          (Eval.fromAltStack saved (trueElement :: stack) altStack [] flags ctx _
            (Eval.empty (saved :: trueElement :: stack) altStack flags ctx)))))
  · simp at h
    refine ⟨falseElement, ?_⟩
    simpa [compile] using
    (Eval.toAltStack saved (wit :: stack) altStack
      [.pushData key, .op .OP_CHECKSIG, .op .OP_FROMALTSTACK] flags ctx _
      (Eval.pushData key [.op .OP_CHECKSIG, .op .OP_FROMALTSTACK]
        (wit :: stack) (saved :: altStack) flags ctx _
        (Eval.checksig_failure key wit stack [.op .OP_FROMALTSTACK]
          (saved :: altStack) flags ctx _
          h
          (Eval.fromAltStack saved (falseElement :: stack) altStack [] flags ctx _
            (Eval.empty (saved :: falseElement :: stack) altStack flags ctx)))))

/-!
TODO(theorem): promote these AST-level leaf and wrapper lemmas into the main
core type-soundness theorem.

Core proof tasks:
- State `type_soundness_core` over `CoreFragment`, `HasType`, and `compile`.
- Define the semantic guarantees for each base type/modifier pair as reusable
  predicates instead of one-off examples.
- Prove the theorem by induction over the `HasType` derivation, with separate
  lemmas for leaves, connectives, wrappers, threshold, `multi`, and `multi_a`.
- State `type_soundness_surface` as a corollary for `SurfaceFragment` by
  desugaring to core before compilation.
-/

/-! ## Theorem 2: Satisfaction Correctness -/

/-!
TODO(theorem): satisfaction correctness.

Core proof tasks:
- Define the witness/environment model needed by `satisfy`.
- State correctness over `CoreFragment`: if `satisfy m env = some w`, then
  `compile m` succeeds with witness `w` under the matching transaction context.
- Add the surface corollary by applying the core theorem to `desugar s`.
-/

/-! ## Theorem 3: Dissatisfaction Correctness -/

/-!
TODO(theorem): dissatisfaction correctness.

Core proof tasks:
- Define the exact stack shape for dissatisfied B fragments with the `d`
  modifier.
- State correctness over `CoreFragment`: if `dissatisfy m env = some w`, then
  running `compile m` with `w` reaches the designated false result.
- Add the surface corollary through `desugar`.
-/

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
