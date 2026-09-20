import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Compile
import LeanMiniscript.Miniscript.Metrics
import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Script.Serialization
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

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
satisfaction paths as well. The summaries below mirror Bitcoin Core's `Ops`
and `SatInfo` analyses: `none` denotes that no canonical non-malleable path of
the requested kind exists, sequential composition treats it as absorbing, and
branch choice takes the larger available bound.
-/

/-- Maximum of a set of path costs; `none` represents an empty path set. -/
abbrev PathMaximum := Option Nat

namespace PathMaximum

/-- Concatenate two path sets and add their costs. -/
def sequential : PathMaximum → PathMaximum → PathMaximum
  | some left, some right => some (left + right)
  | _, _ => none

/-- Take the union of two path sets and retain the maximum cost. -/
def choice : PathMaximum → PathMaximum → PathMaximum
  | none, right => right
  | left, none => left
  | some left, some right => some (max left right)

end PathMaximum

/-- Dynamic CHECKMULTISIG key counts for satisfaction and dissatisfaction
    paths. CHECKSIG and CHECKSIGADD remain part of the static opcode count. -/
structure OpPathBounds where
  sat : PathMaximum
  dsat : PathMaximum
  deriving Repr, DecidableEq

private def opThresholdMiddle (child : OpPathBounds)
    (previous : PathMaximum) : List PathMaximum → List PathMaximum
  | [] => [PathMaximum.sequential previous child.sat]
  | current :: rest =>
      PathMaximum.choice
          (PathMaximum.sequential current child.dsat)
          (PathMaximum.sequential previous child.sat) ::
        opThresholdMiddle child current rest

/-- Add one threshold child to the dynamic-programming states indexed by the
    number of satisfied children. -/
private def opThresholdStep
    (states : List PathMaximum) (child : OpPathBounds) : List PathMaximum :=
  match states with
  | [] => []
  | first :: rest =>
      PathMaximum.sequential first child.dsat ::
        opThresholdMiddle child first rest

private def opThresholdFold :
    List PathMaximum → List OpPathBounds → List PathMaximum
  | states, [] => states
  | states, child :: children =>
      opThresholdFold (opThresholdStep states child) children

mutual
  /-- Maximum executed CHECKMULTISIG key counts along canonical
      non-malleable satisfaction and dissatisfaction paths. -/
  def opPathBounds : CoreFragment → OpPathBounds
    | .zero => ⟨none, some 0⟩
    | .one => ⟨some 0, none⟩
    | .pk_k _ | .pk_h _ => ⟨some 0, some 0⟩
    | .older _ | .after _ | .sha256 _ | .hash256 _ |
        .ripemd160 _ | .hash160 _ => ⟨some 0, none⟩
    | .and_v x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.sequential xBounds.sat yBounds.sat, none⟩
    | .and_b x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.sequential xBounds.sat yBounds.sat,
          PathMaximum.sequential xBounds.dsat yBounds.dsat⟩
    | .or_b x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.choice
            (PathMaximum.sequential xBounds.sat yBounds.dsat)
            (PathMaximum.sequential xBounds.dsat yBounds.sat),
          PathMaximum.sequential xBounds.dsat yBounds.dsat⟩
    | .or_c x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.choice xBounds.sat
            (PathMaximum.sequential xBounds.dsat yBounds.sat), none⟩
    | .or_d x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.choice xBounds.sat
            (PathMaximum.sequential xBounds.dsat yBounds.sat),
          PathMaximum.sequential xBounds.dsat yBounds.dsat⟩
    | .or_i x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.choice xBounds.sat yBounds.sat,
          PathMaximum.choice xBounds.dsat yBounds.dsat⟩
    | .andor x y z =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        let zBounds := opPathBounds z
        ⟨PathMaximum.choice
            (PathMaximum.sequential xBounds.sat yBounds.sat)
            (PathMaximum.sequential xBounds.dsat zBounds.sat),
          PathMaximum.sequential xBounds.dsat zBounds.dsat⟩
    | .a x | .s x | .c x | .n x => opPathBounds x
    | .d x | .j x => ⟨(opPathBounds x).sat, some 0⟩
    | .v x => ⟨(opPathBounds x).sat, none⟩
    | .thresh k fragments =>
        let states := opThresholdFold [some 0] (opPathBoundsList fragments)
        ⟨states.getD k none, states.getD 0 none⟩
    | .multi _ keys => ⟨some keys.length, some keys.length⟩
    | .multi_a _ _ => ⟨some 0, some 0⟩

  /-- Path summaries for threshold children in source order. -/
  def opPathBoundsList : List CoreFragment → List OpPathBounds
    | [] => []
    | fragment :: fragments =>
        opPathBounds fragment :: opPathBoundsList fragments
end

/-- One set of execution traces summarized relative to the final stack. -/
structure StackTraceBound where
  /-- Largest difference between initial and final combined stack size. -/
  netDiff : Int
  /-- Largest difference between any execution stack and final stack size. -/
  exec : Int
  deriving Repr, DecidableEq

namespace StackTraceBound

/-- Concatenate every trace in `left` with every trace in `right`. -/
def sequential (left right : StackTraceBound) : StackTraceBound where
  netDiff := left.netDiff + right.netDiff
  exec := max right.exec (right.netDiff + left.exec)

def empty : StackTraceBound := ⟨0, 0⟩
def push : StackTraceBound := ⟨-1, 0⟩
def hash : StackTraceBound := ⟨0, 0⟩
def nop : StackTraceBound := ⟨0, 0⟩
def branch : StackTraceBound := ⟨1, 1⟩
def binary : StackTraceBound := ⟨1, 1⟩
def dup : StackTraceBound := ⟨-1, 0⟩
def ifdupTrue : StackTraceBound := ⟨-1, 0⟩
def ifdupFalse : StackTraceBound := ⟨0, 0⟩
def equalVerify : StackTraceBound := ⟨2, 2⟩
def equal : StackTraceBound := ⟨1, 1⟩
def size : StackTraceBound := ⟨-1, 0⟩
def checkSig : StackTraceBound := ⟨1, 1⟩
def zeroNotEqual : StackTraceBound := ⟨0, 0⟩
def verify : StackTraceBound := ⟨1, 1⟩

end StackTraceBound

/-- A set of summarized stack traces; `none` represents an empty set. -/
abbrev StackTraceSet := Option StackTraceBound

namespace StackTraceSet

/-- Concatenate two trace sets. -/
def sequential : StackTraceSet → StackTraceSet → StackTraceSet
  | some left, some right => some (left.sequential right)
  | _, _ => none

/-- Union two trace sets and retain both coordinate-wise maxima. -/
def choice : StackTraceSet → StackTraceSet → StackTraceSet
  | none, right => right
  | left, none => left
  | some left, some right => some {
      netDiff := max left.netDiff right.netDiff
      exec := max left.exec right.exec }

end StackTraceSet

/-- Stack traces for canonical non-malleable satisfaction and dissatisfaction. -/
structure StackPathBounds where
  sat : StackTraceSet
  dsat : StackTraceSet
  deriving Repr, DecidableEq

private def stackThresholdMiddle (child : StackPathBounds)
    (previous : StackTraceSet) : List StackTraceSet → List StackTraceSet
  | [] => [StackTraceSet.sequential previous child.sat]
  | current :: rest =>
      StackTraceSet.choice
          (StackTraceSet.sequential current child.dsat)
          (StackTraceSet.sequential previous child.sat) ::
        stackThresholdMiddle child current rest

private def stackThresholdStep
    (states : List StackTraceSet) (child : StackPathBounds) : List StackTraceSet :=
  match states with
  | [] => []
  | first :: rest =>
      StackTraceSet.sequential first child.dsat ::
        stackThresholdMiddle child first rest

private def appendThresholdAdd (first : Bool)
    (bounds : StackPathBounds) : StackPathBounds :=
  if first then bounds else
    ⟨StackTraceSet.sequential bounds.sat (some StackTraceBound.binary),
      StackTraceSet.sequential bounds.dsat (some StackTraceBound.binary)⟩

private def stackThresholdFold :
    Bool → List StackTraceSet → List StackPathBounds → List StackTraceSet
  | _, states, [] => states
  | first, states, child :: children =>
      stackThresholdFold false
        (stackThresholdStep states (appendThresholdAdd first child)) children

mutual
  /-- Exact Core-style stack summaries for canonical non-malleable paths. -/
  def stackPathBounds : CoreFragment → StackPathBounds
    | .zero => ⟨none, some StackTraceBound.push⟩
    | .one => ⟨some StackTraceBound.push, none⟩
    | .older _ | .after _ =>
        ⟨some (StackTraceBound.push.sequential StackTraceBound.nop), none⟩
    | .pk_k _ =>
        ⟨some StackTraceBound.push, some StackTraceBound.push⟩
    | .pk_h _ =>
        let trace := StackTraceBound.dup
          |>.sequential StackTraceBound.hash
          |>.sequential StackTraceBound.push
          |>.sequential StackTraceBound.equalVerify
        ⟨some trace, some trace⟩
    | .sha256 _ | .hash256 _ | .ripemd160 _ | .hash160 _ =>
        let trace := StackTraceBound.size
          |>.sequential StackTraceBound.push
          |>.sequential StackTraceBound.equalVerify
          |>.sequential StackTraceBound.hash
          |>.sequential StackTraceBound.push
          |>.sequential StackTraceBound.equal
        ⟨some trace, none⟩
    | .andor x y z =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        let zBounds := stackPathBounds z
        ⟨StackTraceSet.choice
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.sat
                (some StackTraceBound.branch)) yBounds.sat)
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.dsat
                (some StackTraceBound.branch)) zBounds.sat),
          StackTraceSet.sequential
            (StackTraceSet.sequential xBounds.dsat
              (some StackTraceBound.branch)) zBounds.dsat⟩
    | .and_v x y =>
        ⟨StackTraceSet.sequential (stackPathBounds x).sat
            (stackPathBounds y).sat, none⟩
    | .and_b x y =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        ⟨StackTraceSet.sequential
            (StackTraceSet.sequential xBounds.sat yBounds.sat)
            (some StackTraceBound.binary),
          StackTraceSet.sequential
            (StackTraceSet.sequential xBounds.dsat yBounds.dsat)
            (some StackTraceBound.binary)⟩
    | .or_b x y =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        ⟨StackTraceSet.sequential
            (StackTraceSet.choice
              (StackTraceSet.sequential xBounds.sat yBounds.dsat)
              (StackTraceSet.sequential xBounds.dsat yBounds.sat))
            (some StackTraceBound.binary),
          StackTraceSet.sequential
            (StackTraceSet.sequential xBounds.dsat yBounds.dsat)
            (some StackTraceBound.binary)⟩
    | .or_c x y =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        ⟨StackTraceSet.choice
            (StackTraceSet.sequential xBounds.sat
              (some StackTraceBound.branch))
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.dsat
                (some StackTraceBound.branch)) yBounds.sat), none⟩
    | .or_d x y =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        ⟨StackTraceSet.choice
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.sat
                (some StackTraceBound.ifdupTrue))
              (some StackTraceBound.branch))
            (StackTraceSet.sequential
              (StackTraceSet.sequential
                (StackTraceSet.sequential xBounds.dsat
                  (some StackTraceBound.ifdupFalse))
                (some StackTraceBound.branch)) yBounds.sat),
          StackTraceSet.sequential
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.dsat
                (some StackTraceBound.ifdupFalse))
              (some StackTraceBound.branch)) yBounds.dsat⟩
    | .or_i x y =>
        let xBounds := stackPathBounds x
        let yBounds := stackPathBounds y
        ⟨StackTraceSet.sequential (some StackTraceBound.branch)
            (StackTraceSet.choice xBounds.sat yBounds.sat),
          StackTraceSet.sequential (some StackTraceBound.branch)
            (StackTraceSet.choice xBounds.dsat yBounds.dsat)⟩
    | .multi k keys =>
        let trace : StackTraceBound :=
          ⟨Int.ofNat k, Int.ofNat (k + keys.length + 2)⟩
        ⟨some trace, some trace⟩
    | .multi_a _ keys =>
        let trace : StackTraceBound :=
          ⟨Int.ofNat keys.length - 1, Int.ofNat keys.length⟩
        ⟨some trace, some trace⟩
    | .a x | .n x | .s x => stackPathBounds x
    | .c x =>
        let bounds := stackPathBounds x
        ⟨StackTraceSet.sequential bounds.sat
            (some StackTraceBound.checkSig),
          StackTraceSet.sequential bounds.dsat
            (some StackTraceBound.checkSig)⟩
    | .d x =>
        let prefixTrace := StackTraceBound.dup.sequential StackTraceBound.branch
        ⟨StackTraceSet.sequential (some prefixTrace) (stackPathBounds x).sat,
          some prefixTrace⟩
    | .v x =>
        ⟨StackTraceSet.sequential (stackPathBounds x).sat
            (some StackTraceBound.verify), none⟩
    | .j x =>
        let prefixTrace := StackTraceBound.size
          |>.sequential StackTraceBound.zeroNotEqual
          |>.sequential StackTraceBound.branch
        ⟨StackTraceSet.sequential (some prefixTrace) (stackPathBounds x).sat,
          some prefixTrace⟩
    | .thresh k fragments =>
        let states := stackThresholdFold true [some StackTraceBound.empty]
          (stackPathBoundsList fragments)
        let suffix := StackTraceBound.push.sequential StackTraceBound.equal
        ⟨StackTraceSet.sequential (states.getD k none) (some suffix),
          StackTraceSet.sequential (states.getD 0 none) (some suffix)⟩

  /-- Stack summaries for threshold children in source order. -/
  def stackPathBoundsList : List CoreFragment → List StackPathBounds
    | [] => []
    | fragment :: fragments =>
        stackPathBounds fragment :: stackPathBoundsList fragments
end

/-- Maximum total P2WSH opcode count for a canonical non-malleable
    satisfaction. Static non-push opcodes are counted across the complete
    script; the path summary adds executed CHECKMULTISIG public keys. -/
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
  {
    scriptSize := match LeanMiniscript.Script.serializedScriptSize script with
      | .ok size => some size
      | .error _ => none
    staticOps
    executedMultiKeys
    satisfactionOps := executedMultiKeys.map (staticOps + ·)
    satisfactionInitialStack := maxSatisfactionInitialStack fragment
    satisfactionExecutionStack := maxSatisfactionExecutionStack fragment
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

/-- Contract for the first conservative final-state growth bound, proved by
    `resourceBoundsSound` in `ResourceBoundsProofs`. Counting the main
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

/-! `maxStackGrowth` charges both sides of every conditional and does not
subtract items consumed by earlier opcodes. It is therefore conservative rather
than an exact path-sensitive peak. -/

end LeanMiniscript.Properties
