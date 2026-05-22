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
  ∀ (stack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    ∃ (keyElem : StackElement),
      Eval (compile m) stack flags ctx (.success (keyElem :: stack))

/-- What a B-type fragment with 'o' modifier guarantees:
    Consumes exactly one witness element from the stack and pushes
    exactly one result element (nonzero for success, zero for failure).
    Stack below the witness is preserved. -/
def BTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    ∃ (result : StackElement),
      Eval (compile m) (wit :: stack) flags ctx (.success (result :: stack))

/-- What a V-type fragment with 'o' modifier guarantees:
    Consumes one witness element. On success, the stack below is unchanged
    (V-type pushes nothing). On failure, the script aborts.
    This is the key property: V-type either passes silently or kills execution. -/
def VTypeOGuarantee (m : CoreFragment) : Prop :=
  ∀ (wit : StackElement) (stack : Stack) (flags : ScriptFlags) (ctx : TxContext),
    Eval (compile m) (wit :: stack) flags ctx (.success stack) ∨
    ∃ (msg : String), Eval (compile m) (wit :: stack) flags ctx (.failure msg)

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
