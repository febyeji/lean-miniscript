import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Metrics
import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Script.Serialization

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-- Bitcoin consensus limits. -/
def MAX_STACK_SIZE : Nat := 1000
def MAX_SCRIPT_SIZE : Nat := 10000
def MAX_OPS_PER_SCRIPT : Nat := 201
def MAX_SCRIPT_ELEMENT_SIZE : Nat := 520

/-- Whether a script element is a non-push opcode for the BIP 379 opcode-count
    accounting layer. -/
def isNonPushElement : ScriptElement → Bool
  | .op _ => true
  | .pushData _ => false
  | .pushNum _ => false

/-- Number of Script AST elements produced by compilation. -/
def scriptElementCount (fragment : CoreFragment) : Nat :=
  (compile fragment).length

/-- Exact serialized byte size of a compiled core fragment. -/
def serializedScriptSize (fragment : CoreFragment) : Except SerializationError Nat :=
  LeanMiniscript.Script.serializedScriptSize (compile fragment)

example : scriptElementCount .zero = 1 := by
  rfl

example : serializedScriptSize .zero = .ok 1 := by
  rfl

/-- Number of non-push opcodes in the compiled script. -/
def nonPushOpCount (script : Script) : Nat :=
  script.foldl (fun count elem => if isNonPushElement elem then count + 1 else count) 0

mutual
  /-- Static signature-operation count for core fragments. -/
  def sigopCount : CoreFragment → Nat
    | .zero => 0
    | .one => 0
    | .pk_k _ => 0
    | .pk_h _ => 0
    | .older _ => 0
    | .after _ => 0
    | .sha256 _ => 0
    | .hash256 _ => 0
    | .ripemd160 _ => 0
    | .hash160 _ => 0
    | .and_v x y => sigopCount x + sigopCount y
    | .and_b x y => sigopCount x + sigopCount y
    | .or_b x y => sigopCount x + sigopCount y
    | .or_c x y => sigopCount x + sigopCount y
    | .or_d x y => sigopCount x + sigopCount y
    | .or_i x y => sigopCount x + sigopCount y
    | .andor x y z => sigopCount x + sigopCount y + sigopCount z
    | .a x => sigopCount x
    | .s x => sigopCount x
    | .c x => sigopCount x + 1
    | .d x => sigopCount x
    | .v x => sigopCount x
    | .j x => sigopCount x
    | .n x => sigopCount x
    | .thresh _ fragments => listSigopCount fragments
    | .multi _ keys => keys.length
    | .multi_a _ keys => keys.length

  /-- Static signature-operation count for a list of core fragments. -/
  def listSigopCount : List CoreFragment → Nat
    | [] => 0
    | fragment :: fragments => sigopCount fragment + listSigopCount fragments
end

/-- Structural bound used until the small-step semantics records exact peak
    runtime stack usage. -/
def maxStackDepth (fragment : CoreFragment) : Nat :=
  fragment.depth

/-- Target theorem for the first conservative runtime bound. Counting the main
    and alt stacks together avoids treating `TOALTSTACK` as allocation. Each
    executed compiler element may increase that total by at most one, so the
    complete compiled script length is a conservative allowance independent of
    which conditional branch runs. -/
def ResourceBoundsSound : Prop :=
  ∀ {ctx : ScriptContext} {fragment : CoreFragment} {ty : MiniType}
      {initialStack initialAltStack finalStack finalAltStack : Stack}
      {flags : ScriptFlags} {txCtx : TxContext},
    ValidTypedFragment ctx fragment ty →
    Eval (compile fragment) initialStack initialAltStack flags txCtx
      (.success finalStack finalAltStack) →
    finalStack.length + finalAltStack.length ≤
      initialStack.length + initialAltStack.length + scriptElementCount fragment

/-!
TODO(theorem): resource-bound soundness.

Core proof tasks:
- Prove `ResourceBoundsSound` by induction over compiler output evaluation.
- Replace the provisional AST-depth estimate with a proved peak-main-stack
  analyzer; the combined-stack theorem above is only the first conservative
  contract.
- State the surface corollary by applying the core theorem to `desugar s`, so
  surface syntax does not need a duplicate resource proof.
-/

end LeanMiniscript.Properties
