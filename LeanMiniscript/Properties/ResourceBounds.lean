import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Metrics
import LeanMiniscript.Properties.ResourcePaths
import LeanMiniscript.Script.Codec.Serialization
import LeanMiniscript.Script.StackGrowthAllowance

/-! Compiled resource metrics and context-specific limit checks.
ResourcePathBoundsProofs proves threshold-path bounds; ResourceBoundsProofs
contains the ResourceBoundsSound contract and its proof. -/

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

/-- Bitcoin consensus limits. -/
def MAX_STACK_SIZE : Nat := maxStackSize
def MAX_SCRIPT_SIZE : Nat := 10000
def MAX_OPS_PER_SCRIPT : Nat := 201
def MAX_SCRIPT_ELEMENT_SIZE : Nat := maxScriptElementSize

/-- Standard P2WSH witness scripts are limited to 3600 serialized bytes. -/
def MAX_STANDARD_P2WSH_SCRIPT_SIZE : Nat := 3600

/-- A standard P2WSH witness has at most 100 arguments, excluding the script. -/
def MAX_STANDARD_P2WSH_STACK_ITEMS : Nat := 100

/-- Bitcoin Core's conservative Tapscript Miniscript size bound. It reserves
    enough transaction weight for 1000 maximum-size Miniscript arguments and a
    maximum-depth Taproot control block. -/
def MAX_SANE_TAPSCRIPT_SCRIPT_SIZE : Nat := 329482

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

/-- A fixed 20-byte key hash used when only compiled resource shape matters.
    This keeps resource analysis executable without evaluating the formal
    compiler's opaque HASH160 boundary. -/
private def sizingKeyHash (_key : PubKey) : Hash160 :=
  Hash160.ofBytes ⟨Array.replicate 20 0⟩

/-- Compile with a correctly sized placeholder key hash. The resulting opcode
    sequence and serialized size equal concrete compilation for every
    well-formed fragment. -/
def compileForResourceAnalysis (fragment : CoreFragment) : Script :=
  compileWithKeyHash sizingKeyHash fragment

/-- Executable serialized size used by the resource-limit checker. -/
def resourceSerializedScriptSize (fragment : CoreFragment) :
    Except SerializationError Nat :=
  LeanMiniscript.Script.serializedScriptSize
    (compileForResourceAnalysis fragment)

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

/-!
## Path-sensitive satisfaction bounds

P2WSH charges every non-push opcode statically, then charges the public-key
count of each executed CHECKMULTISIG. Stack limits depend on complete
satisfaction paths as well. The summaries below cover every usable generated
candidate path, including executable non-canonical rows retained by candidate
selection. `none` represents an empty summarized path set, sequential
composition treats it as absorbing, and branch choice takes the larger bound.
-/

/-- Maximum total P2WSH opcode count for a usable generated satisfaction.
    Static non-push opcodes are counted across the complete script; the path
    summary adds executed CHECKMULTISIG public keys. -/
def maxSatisfactionOpCount (fragment : CoreFragment) : Option Nat :=
  (opPathBounds fragment).sat.map fun dynamic =>
    nonPushOpCount (compileForResourceAnalysis fragment) + dynamic

/-- Maximum initial stack size of a top-level B satisfaction. -/
def maxSatisfactionInitialStack (fragment : CoreFragment) : Option Int :=
  (stackPathBounds fragment).sat.map fun trace => trace.netDiff + 1

/-- Maximum combined main/alt-stack size reached by a top-level B
    satisfaction. -/
def maxSatisfactionExecutionStack (fragment : CoreFragment) : Option Int :=
  (stackPathBounds fragment).sat.map fun trace => trace.exec + 1

/-- Computed resource summary used by sane-fragment validation and diagnostics. -/
structure ResourceUsage where
  /-- Serialized compiled size, or `none` if a push cannot be serialized. -/
  scriptSize : Option Nat
  /-- Non-push opcodes present in the complete compiled script. -/
  staticOps : Nat
  /-- Maximum CHECKMULTISIG key charge along a satisfaction path. -/
  executedMultiKeys : Option Nat
  /-- Maximum static plus dynamic P2WSH opcode charge. -/
  satisfactionOps : Option Nat
  /-- Maximum initial stack size for top-level B satisfaction. -/
  satisfactionInitialStack : Option Int
  /-- Maximum execution stack size for top-level B satisfaction. -/
  satisfactionExecutionStack : Option Int
  deriving Repr, DecidableEq

/-- Compute all resource quantities once for reporting or limit checks. -/
def resourceUsage (fragment : CoreFragment) : ResourceUsage :=
  let script := compileForResourceAnalysis fragment
  let staticOps := nonPushOpCount script
  let executedMultiKeys := (opPathBounds fragment).sat
  let stackBounds := (stackPathBounds fragment).sat
  {
    scriptSize := match LeanMiniscript.Script.serializedScriptSize script with
      | .ok size => some size
      | .error _ => none
    staticOps
    executedMultiKeys
    satisfactionOps := executedMultiKeys.map (staticOps + ·)
    satisfactionInitialStack := stackBounds.map (fun trace => trace.netDiff + 1)
    satisfactionExecutionStack := stackBounds.map (fun trace => trace.exec + 1)
  }

/-- Context-dependent sane script-size limit used by Bitcoin Core Miniscript. -/
def saneScriptSizeLimit : ScriptContext → Nat
  | .p2wsh => MAX_STANDARD_P2WSH_SCRIPT_SIZE
  | .tapscript => MAX_SANE_TAPSCRIPT_SCRIPT_SIZE

/-- Pure boundary predicate, separated so exact limit edges are cheap to test. -/
def scriptSizeWithinContextLimit (ctx : ScriptContext) (size : Nat) : Bool :=
  decide (size ≤ saneScriptSizeLimit ctx)

/-- Whether the compiled script fits its context's sane serialized-size bound. -/
def compiledScriptSizeWithinLimit
    (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  match resourceSerializedScriptSize fragment with
  | .ok size => scriptSizeWithinContextLimit ctx size
  | .error _ => false

/-- P2WSH's static plus path-dependent opcode limit. Tapscript uses validation
    weight instead of this legacy 201-op rule. -/
def satisfactionOpsWithinLimit
    (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  match ctx with
  | .tapscript => true
  | .p2wsh =>
      match maxSatisfactionOpCount fragment with
      | none => true
      | some count => decide (count ≤ MAX_OPS_PER_SCRIPT)

/-- Context-specific stack limit for top-level B satisfaction paths. P2WSH
    applies the 100-item standardness limit to the initial witness; Tapscript
    applies the 1000-item consensus limit throughout execution. -/
def satisfactionStackWithinLimit
    (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  match ctx with
  | .p2wsh =>
      match maxSatisfactionInitialStack fragment with
      | none => true
      | some count => decide (count ≤ Int.ofNat MAX_STANDARD_P2WSH_STACK_ITEMS)
  | .tapscript =>
      match maxSatisfactionExecutionStack fragment with
      | none => true
      | some count => decide (count ≤ Int.ofNat MAX_STACK_SIZE)

/-- Executable resource component for an integrated sane-fragment check.
    Structural validation, top-level B typing, non-malleability, unique keys,
    and HASSIG remain separate conjuncts at that boundary. -/
def resourceLimitsSatisfied
    (ctx : ScriptContext) (fragment : CoreFragment) : Bool :=
  compiledScriptSizeWithinLimit ctx fragment &&
    satisfactionOpsWithinLimit ctx fragment &&
    satisfactionStackWithinLimit ctx fragment

/-- Declarative wrapper used by the integrated sane-fragment boundary. -/
def WithinResourceLimits
    (ctx : ScriptContext) (fragment : CoreFragment) : Prop :=
  resourceLimitsSatisfied ctx fragment = true

instance (ctx : ScriptContext) (fragment : CoreFragment) :
    Decidable (WithinResourceLimits ctx fragment) := by
  unfold WithinResourceLimits
  infer_instance

/-- Maximum AST nesting depth. This structural metric is not a runtime stack
    bound. -/
def maxStackDepth (fragment : CoreFragment) : Nat :=
  fragment.depth

/-- Conservative increase in combined main/alt-stack size across any
    source-order execution prefix of the compiled fragment. The initial stack
    size must be added separately. -/
def maxStackGrowth (fragment : CoreFragment) : Nat :=
  stackGrowthAllowance (compile fragment)

example : maxStackGrowth (.after 500) = 1 := by
  rfl

example : maxStackGrowth (.or_i .one .one) = 2 := by
  rfl

/-! `maxStackGrowth` charges both sides of every conditional and does not
subtract items consumed by earlier opcodes. It is therefore conservative rather
than an exact path-sensitive peak. -/

end LeanMiniscript.Properties
