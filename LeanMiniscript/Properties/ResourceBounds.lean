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
satisfaction paths as well. The summaries below cover every usable generated
candidate path, including executable non-canonical rows retained by candidate
selection. `none` represents an empty summarized path set, sequential
composition treats it as absorbing, and branch choice takes the larger bound.
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

/-- Dynamic CHECKMULTISIG key counts for usable generated satisfaction and
    dissatisfaction paths. CHECKSIG and CHECKSIGADD remain part of the static
    opcode count. -/
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
  /-- Maximum executed CHECKMULTISIG key counts along usable generated
      satisfaction and dissatisfaction paths. -/
  def opPathBounds : CoreFragment → OpPathBounds
    | .zero => ⟨none, some 0⟩
    | .one => ⟨some 0, none⟩
    | .pk_k _ | .pk_h _ => ⟨some 0, some 0⟩
    | .older _ | .after _ | .sha256 _ | .hash256 _ |
        .ripemd160 _ | .hash160 _ => ⟨some 0, none⟩
    | .and_v x y =>
        let xBounds := opPathBounds x
        let yBounds := opPathBounds y
        ⟨PathMaximum.sequential xBounds.sat yBounds.sat,
          PathMaximum.sequential xBounds.sat yBounds.dsat⟩
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
          PathMaximum.choice
            (PathMaximum.sequential xBounds.dsat zBounds.dsat)
            (PathMaximum.sequential xBounds.sat yBounds.dsat)⟩
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

/-- Add the `OP_ADD` that follows every threshold child after the first. -/
def thresholdChild (trace : StackTraceBound) (first : Bool) : StackTraceBound :=
  if first then trace else trace.sequential binary

/-- Add the threshold literal and final equality comparison to a complete row
    of child executions. -/
def thresholdComparison (trace : StackTraceBound) : StackTraceBound :=
  trace.sequential (push.sequential equal)

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

/-- Stack traces for usable generated satisfaction and dissatisfaction paths. -/
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

/-- One concrete source-order threshold choice, retaining both its complete
    stack trace and its dynamic legacy-multisignature key charge. The stack and
    opcode summaries select the same satisfaction or dissatisfaction side for
    every child. The trace includes each inter-child `OP_ADD`; the final
    threshold literal and `OP_EQUAL` are added by `thresholdComparison`. -/
inductive ThresholdResourcePath :
    List StackPathBounds → List OpPathBounds → Nat → StackTraceBound → Nat → Prop where
  | nil : ThresholdResourcePath [] [] 0 StackTraceBound.empty 0
  | sat {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
      {count dynamic : Nat} {trace : StackTraceBound}
      {stackChild : StackPathBounds} {opChild : OpPathBounds}
      {childTrace : StackTraceBound} {childDynamic : Nat}
      (prior : ThresholdResourcePath stackBounds opBounds count trace dynamic)
      (stackSelected : stackChild.sat = some childTrace)
      (opSelected : opChild.sat = some childDynamic) :
      ThresholdResourcePath (stackBounds ++ [stackChild]) (opBounds ++ [opChild])
        (count + 1)
        (trace.sequential (childTrace.thresholdChild stackBounds.isEmpty))
        (dynamic + childDynamic)
  | dsat {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
      {count dynamic : Nat} {trace : StackTraceBound}
      {stackChild : StackPathBounds} {opChild : OpPathBounds}
      {childTrace : StackTraceBound} {childDynamic : Nat}
      (prior : ThresholdResourcePath stackBounds opBounds count trace dynamic)
      (stackSelected : stackChild.dsat = some childTrace)
      (opSelected : opChild.dsat = some childDynamic) :
      ThresholdResourcePath (stackBounds ++ [stackChild]) (opBounds ++ [opChild])
        count (trace.sequential (childTrace.thresholdChild stackBounds.isEmpty))
        (dynamic + childDynamic)

/-- One concrete source-order threshold path through the stack-summary table.
    The integer accumulates the selected summaries' net stack differences;
    every child after the first is followed by `OP_ADD`. -/
inductive ThresholdStackPath : List StackPathBounds → Nat → Int → Prop where
  | nil : ThresholdStackPath [] 0 0
  | sat {bounds : List StackPathBounds} {count : Nat} {netDiff : Int}
      {child : StackPathBounds} {childTrace : StackTraceBound}
      (prior : ThresholdStackPath bounds count netDiff)
      (selected : child.sat = some childTrace) :
      ThresholdStackPath (bounds ++ [child]) (count + 1)
        (netDiff + childTrace.netDiff + if bounds = [] then 0 else 1)
  | dsat {bounds : List StackPathBounds} {count : Nat} {netDiff : Int}
      {child : StackPathBounds} {childTrace : StackTraceBound}
      (prior : ThresholdStackPath bounds count netDiff)
      (selected : child.dsat = some childTrace) :
      ThresholdStackPath (bounds ++ [child]) count
        (netDiff + childTrace.netDiff + if bounds = [] then 0 else 1)

/-- Forget dynamic opcode charges and the execution-peak coordinate while
    retaining the legacy net-difference path used by witness-length proofs. -/
theorem ThresholdResourcePath.toThresholdStackPath
    {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
    {count dynamic : Nat} {trace : StackTraceBound}
    (path : ThresholdResourcePath stackBounds opBounds count trace dynamic) :
    ThresholdStackPath stackBounds count trace.netDiff := by
  induction path with
  | nil => exact .nil
  | @sat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      have extended := ThresholdStackPath.sat ih stackSelected
      cases stackBounds with
      | nil => simpa [StackTraceBound.thresholdChild,
          StackTraceBound.sequential] using extended
      | cons head tail =>
          simpa [StackTraceBound.thresholdChild, StackTraceBound.sequential,
            StackTraceBound.binary, Int.add_assoc] using extended
  | @dsat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      have extended := ThresholdStackPath.dsat ih stackSelected
      cases stackBounds with
      | nil => simpa [StackTraceBound.thresholdChild,
          StackTraceBound.sequential] using extended
      | cons head tail =>
          simpa [StackTraceBound.thresholdChild, StackTraceBound.sequential,
            StackTraceBound.binary, Int.add_assoc] using extended

private theorem ThresholdStackPath.nil_inv {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath [] count netDiff) : count = 0 ∧ netDiff = 0 := by
  generalize boundsEq : ([] : List StackPathBounds) = bounds at path
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | sat prior selected => simp at boundsEq
  | dsat prior selected => simp at boundsEq

private theorem stackThresholdFold_append (first : Bool)
    (states : List StackTraceSet) (bounds : List StackPathBounds)
    (child : StackPathBounds) :
    stackThresholdFold first states (bounds ++ [child]) =
      stackThresholdStep (stackThresholdFold first states bounds)
        (appendThresholdAdd (first && bounds.isEmpty) child) := by
  induction bounds generalizing first states with
  | nil => simp [stackThresholdFold]
  | cons bound bounds ih =>
      simp only [List.cons_append, stackThresholdFold, List.isEmpty_cons,
        Bool.and_false, appendThresholdAdd]
      exact ih false (stackThresholdStep states
        (if first then bound else
          { sat := StackTraceSet.sequential bound.sat
              (some StackTraceBound.binary)
            dsat := StackTraceSet.sequential bound.dsat
              (some StackTraceBound.binary) }))

private theorem stackThresholdStep_getD_zero
    (states : List StackTraceSet) (child : StackPathBounds) :
    (stackThresholdStep states child).getD 0 none =
      StackTraceSet.sequential (states.getD 0 none) child.dsat := by
  cases states <;> simp [stackThresholdStep, StackTraceSet.sequential]

private theorem stackThresholdMiddle_getD
    (child : StackPathBounds) (previous : StackTraceSet)
    (rest : List StackTraceSet) (count : Nat) :
    (stackThresholdMiddle child previous rest).getD count none =
      match count with
      | 0 =>
          StackTraceSet.choice
            (StackTraceSet.sequential (rest.getD 0 none) child.dsat)
            (StackTraceSet.sequential previous child.sat)
      | count + 1 =>
          StackTraceSet.choice
            (StackTraceSet.sequential (rest.getD (count + 1) none) child.dsat)
            (StackTraceSet.sequential (rest.getD count none) child.sat) := by
  induction rest generalizing previous count with
  | nil =>
      cases count <;> simp [stackThresholdMiddle, StackTraceSet.sequential,
        StackTraceSet.choice]
  | cons current rest ih =>
      cases count with
      | zero => simp [stackThresholdMiddle]
      | succ count =>
          simp only [stackThresholdMiddle, List.getD_cons_succ]
          cases count with
          | zero => simpa using ih current 0
          | succ count =>
              simpa [Nat.succ_eq_add_one] using ih current (count + 1)

private theorem stackThresholdStep_getD_succ
    (states : List StackTraceSet) (child : StackPathBounds) (count : Nat) :
    (stackThresholdStep states child).getD (count + 1) none =
      StackTraceSet.choice
        (StackTraceSet.sequential (states.getD (count + 1) none) child.dsat)
        (StackTraceSet.sequential (states.getD count none) child.sat) := by
  cases states with
  | nil => simp [stackThresholdStep, StackTraceSet.sequential,
      StackTraceSet.choice]
  | cons first rest =>
      simp only [stackThresholdStep, List.getD_cons_succ]
      rw [stackThresholdMiddle_getD]
      cases count <;> simp

private theorem opThresholdFold_append
    (states : List PathMaximum) (bounds : List OpPathBounds)
    (child : OpPathBounds) :
    opThresholdFold states (bounds ++ [child]) =
      opThresholdStep (opThresholdFold states bounds) child := by
  induction bounds generalizing states with
  | nil => simp [opThresholdFold]
  | cons bound bounds ih =>
      simp only [List.cons_append, opThresholdFold]
      exact ih (opThresholdStep states bound)

private theorem opThresholdStep_getD_zero
    (states : List PathMaximum) (child : OpPathBounds) :
    (opThresholdStep states child).getD 0 none =
      PathMaximum.sequential (states.getD 0 none) child.dsat := by
  cases states <;> simp [opThresholdStep, PathMaximum.sequential]

private theorem opThresholdMiddle_getD
    (child : OpPathBounds) (previous : PathMaximum)
    (rest : List PathMaximum) (count : Nat) :
    (opThresholdMiddle child previous rest).getD count none =
      match count with
      | 0 =>
          PathMaximum.choice
            (PathMaximum.sequential (rest.getD 0 none) child.dsat)
            (PathMaximum.sequential previous child.sat)
      | count + 1 =>
          PathMaximum.choice
            (PathMaximum.sequential (rest.getD (count + 1) none) child.dsat)
            (PathMaximum.sequential (rest.getD count none) child.sat) := by
  induction rest generalizing previous count with
  | nil =>
      cases count <;> simp [opThresholdMiddle, PathMaximum.sequential,
        PathMaximum.choice]
  | cons current rest ih =>
      cases count with
      | zero => simp [opThresholdMiddle]
      | succ count =>
          simp only [opThresholdMiddle, List.getD_cons_succ]
          cases count with
          | zero => simpa using ih current 0
          | succ count =>
              simpa [Nat.succ_eq_add_one] using ih current (count + 1)

private theorem opThresholdStep_getD_succ
    (states : List PathMaximum) (child : OpPathBounds) (count : Nat) :
    (opThresholdStep states child).getD (count + 1) none =
      PathMaximum.choice
        (PathMaximum.sequential (states.getD (count + 1) none) child.dsat)
        (PathMaximum.sequential (states.getD count none) child.sat) := by
  cases states with
  | nil => simp [opThresholdStep, PathMaximum.sequential, PathMaximum.choice]
  | cons first rest =>
      simp only [opThresholdStep, List.getD_cons_succ]
      rw [opThresholdMiddle_getD]
      cases count <;> simp

private def stackTraceBound
    (summary : StackTraceSet) (trace : StackTraceBound) : Prop :=
  ∃ limit, summary = some limit ∧
    trace.netDiff ≤ limit.netDiff ∧ trace.exec ≤ limit.exec

private theorem stackTraceBound_sequential
    {left right : StackTraceSet} {leftTrace rightTrace : StackTraceBound}
    (leftBound : stackTraceBound left leftTrace)
    (rightBound : stackTraceBound right rightTrace) :
    stackTraceBound (StackTraceSet.sequential left right)
      (leftTrace.sequential rightTrace) := by
  obtain ⟨leftLimit, rfl, leftNet, leftExec⟩ := leftBound
  obtain ⟨rightLimit, rfl, rightNet, rightExec⟩ := rightBound
  refine ⟨leftLimit.sequential rightLimit, rfl, ?_, ?_⟩
  · simp only [StackTraceBound.sequential]
    omega
  · simp only [StackTraceBound.sequential]
    exact Int.max_le.mpr ⟨
      Int.le_trans rightExec (Int.le_max_left _ _),
      Int.le_trans (Int.add_le_add rightNet leftExec)
        (Int.le_max_right _ _)⟩

private theorem stackTraceBound_choiceLeft
    {left right : StackTraceSet} {trace : StackTraceBound}
    (bounded : stackTraceBound left trace) :
    stackTraceBound (StackTraceSet.choice left right) trace := by
  obtain ⟨leftLimit, rfl, netBound, execBound⟩ := bounded
  cases right with
  | none => exact ⟨leftLimit, rfl, netBound, execBound⟩
  | some rightLimit =>
      exact ⟨{
        netDiff := max leftLimit.netDiff rightLimit.netDiff
        exec := max leftLimit.exec rightLimit.exec }, rfl,
        Int.le_trans netBound (Int.le_max_left _ _),
        Int.le_trans execBound (Int.le_max_left _ _)⟩

private theorem stackTraceBound_choiceRight
    {left right : StackTraceSet} {trace : StackTraceBound}
    (bounded : stackTraceBound right trace) :
    stackTraceBound (StackTraceSet.choice left right) trace := by
  obtain ⟨rightLimit, rfl, netBound, execBound⟩ := bounded
  cases left with
  | none => exact ⟨rightLimit, rfl, netBound, execBound⟩
  | some leftLimit =>
      exact ⟨{
        netDiff := max leftLimit.netDiff rightLimit.netDiff
        exec := max leftLimit.exec rightLimit.exec }, rfl,
        Int.le_trans netBound (Int.le_max_right _ _),
        Int.le_trans execBound (Int.le_max_right _ _)⟩

private def dynamicChargeBound (summary : PathMaximum) (charge : Nat) : Prop :=
  ∃ limit, summary = some limit ∧ charge ≤ limit

private theorem dynamicChargeBound_sequential
    {left right : PathMaximum} {leftCharge rightCharge : Nat}
    (leftBound : dynamicChargeBound left leftCharge)
    (rightBound : dynamicChargeBound right rightCharge) :
    dynamicChargeBound (PathMaximum.sequential left right)
      (leftCharge + rightCharge) := by
  obtain ⟨leftLimit, rfl, leftLe⟩ := leftBound
  obtain ⟨rightLimit, rfl, rightLe⟩ := rightBound
  exact ⟨leftLimit + rightLimit, rfl, Nat.add_le_add leftLe rightLe⟩

private theorem dynamicChargeBound_choiceLeft
    {left right : PathMaximum} {charge : Nat}
    (bounded : dynamicChargeBound left charge) :
    dynamicChargeBound (PathMaximum.choice left right) charge := by
  obtain ⟨leftLimit, rfl, bound⟩ := bounded
  cases right with
  | none => exact ⟨leftLimit, rfl, bound⟩
  | some rightLimit =>
      exact ⟨max leftLimit rightLimit, rfl,
        Nat.le_trans bound (Nat.le_max_left _ _)⟩

private theorem dynamicChargeBound_choiceRight
    {left right : PathMaximum} {charge : Nat}
    (bounded : dynamicChargeBound right charge) :
    dynamicChargeBound (PathMaximum.choice left right) charge := by
  obtain ⟨rightLimit, rfl, bound⟩ := bounded
  cases left with
  | none => exact ⟨rightLimit, rfl, bound⟩
  | some leftLimit =>
      exact ⟨max leftLimit rightLimit, rfl,
        Nat.le_trans bound (Nat.le_max_right _ _)⟩

private theorem stackTraceBound_thresholdChildSat
    {child : StackPathBounds} {trace : StackTraceBound}
    (selected : child.sat = some trace) (first : Bool) :
    stackTraceBound (appendThresholdAdd first child).sat
      (trace.thresholdChild first) := by
  cases first with
  | false =>
      exact stackTraceBound_sequential
        ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩
        ⟨StackTraceBound.binary, rfl, Int.le_refl _, Int.le_refl _⟩
  | true => exact ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩

private theorem stackTraceBound_thresholdChildDsat
    {child : StackPathBounds} {trace : StackTraceBound}
    (selected : child.dsat = some trace) (first : Bool) :
    stackTraceBound (appendThresholdAdd first child).dsat
      (trace.thresholdChild first) := by
  cases first with
  | false =>
      exact stackTraceBound_sequential
        ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩
        ⟨StackTraceBound.binary, rfl, Int.le_refl _, Int.le_refl _⟩
  | true => exact ⟨trace, selected, Int.le_refl _, Int.le_refl _⟩

private def stackNetBound (summary : StackTraceSet) (netDiff : Int) : Prop :=
  ∃ trace, summary = some trace ∧ netDiff ≤ trace.netDiff

private theorem stackNetBound_sequential
    {left right : StackTraceSet} {leftNet rightNet : Int}
    (leftBound : stackNetBound left leftNet)
    (rightBound : stackNetBound right rightNet) :
    stackNetBound (StackTraceSet.sequential left right) (leftNet + rightNet) := by
  obtain ⟨leftTrace, rfl, leftLe⟩ := leftBound
  obtain ⟨rightTrace, rfl, rightLe⟩ := rightBound
  exact ⟨leftTrace.sequential rightTrace, rfl, by
    simp only [StackTraceBound.sequential]
    omega⟩

private theorem stackNetBound_choiceLeft
    {left right : StackTraceSet} {netDiff : Int}
    (bounded : stackNetBound left netDiff) :
    stackNetBound (StackTraceSet.choice left right) netDiff := by
  obtain ⟨leftTrace, rfl, bound⟩ := bounded
  cases right with
  | none => exact ⟨leftTrace, rfl, bound⟩
  | some rightTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl,
        Int.le_trans bound (Int.le_max_left _ _)⟩

private theorem stackNetBound_choiceRight
    {left right : StackTraceSet} {netDiff : Int}
    (bounded : stackNetBound right netDiff) :
    stackNetBound (StackTraceSet.choice left right) netDiff := by
  obtain ⟨rightTrace, rfl, bound⟩ := bounded
  cases left with
  | none => exact ⟨rightTrace, rfl, bound⟩
  | some leftTrace =>
      exact ⟨{
        netDiff := max leftTrace.netDiff rightTrace.netDiff
        exec := max leftTrace.exec rightTrace.exec }, rfl,
        Int.le_trans bound (Int.le_max_right _ _)⟩

private theorem stackThresholdFold_bounds_path
    {bounds : List StackPathBounds} {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath bounds count netDiff) :
    stackNetBound
      ((stackThresholdFold true [some StackTraceBound.empty] bounds).getD
        count none) netDiff := by
  induction path with
  | nil => exact ⟨StackTraceBound.empty, rfl, Int.le_refl 0⟩
  | @sat bounds count netDiff child childTrace prior selected ih =>
      rw [stackThresholdFold_append, stackThresholdStep_getD_succ]
      apply stackNetBound_choiceRight
      by_cases empty : bounds = []
      · subst bounds
        have inv := prior.nil_inv
        rw [inv.1, inv.2] at ih ⊢
        simp only [List.isEmpty_nil, Bool.and_true, appendThresholdAdd]
        simpa using stackNetBound_sequential ih
          ⟨childTrace, selected, Int.le_refl childTrace.netDiff⟩
      · have notEmpty : bounds.isEmpty = false := by
          simpa [List.isEmpty_iff] using empty
        simp only [notEmpty, Bool.and_false, appendThresholdAdd]
        rw [selected]
        have childBound :
            stackNetBound
              (StackTraceSet.sequential (some childTrace)
                (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
          stackNetBound_sequential
            ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
            ⟨StackTraceBound.binary, rfl, by
              simp [StackTraceBound.binary]⟩
        simpa [empty, Int.add_assoc] using
          stackNetBound_sequential ih childBound
  | @dsat bounds count netDiff child childTrace prior selected ih =>
      rw [stackThresholdFold_append]
      cases count with
      | zero =>
        rw [stackThresholdStep_getD_zero]
        by_cases empty : bounds = []
        · subst bounds
          have netZero := (prior.nil_inv).2
          rw [netZero] at ih ⊢
          simp only [List.isEmpty_nil, Bool.and_true, appendThresholdAdd]
          simpa using stackNetBound_sequential ih
            ⟨childTrace, selected, Int.le_refl childTrace.netDiff⟩
        · have notEmpty : bounds.isEmpty = false := by
            simpa [List.isEmpty_iff] using empty
          simp only [notEmpty, Bool.and_false, appendThresholdAdd]
          rw [selected]
          have childBound :
              stackNetBound
                (StackTraceSet.sequential (some childTrace)
                  (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
            stackNetBound_sequential
              ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
              ⟨StackTraceBound.binary, rfl, by
                simp [StackTraceBound.binary]⟩
          simpa [empty, Int.add_assoc] using
            stackNetBound_sequential ih childBound
      | succ previous =>
        rw [stackThresholdStep_getD_succ]
        apply stackNetBound_choiceLeft
        by_cases empty : bounds = []
        · subst bounds
          obtain ⟨countEq, _⟩ := prior.nil_inv
          simp at countEq
        · have notEmpty : bounds.isEmpty = false := by
            simpa [List.isEmpty_iff] using empty
          simp only [notEmpty, Bool.and_false, appendThresholdAdd]
          rw [selected]
          have childBound :
              stackNetBound
                (StackTraceSet.sequential (some childTrace)
                  (some StackTraceBound.binary)) (childTrace.netDiff + 1) :=
            stackNetBound_sequential
              ⟨childTrace, rfl, Int.le_refl childTrace.netDiff⟩
              ⟨StackTraceBound.binary, rfl, by
                simp [StackTraceBound.binary]⟩
          simpa [empty, Int.add_assoc] using
            stackNetBound_sequential ih childBound

private theorem thresholdResourceFold_bounds_path
    {stackBounds : List StackPathBounds} {opBounds : List OpPathBounds}
    {count dynamic : Nat} {trace : StackTraceBound}
    (path : ThresholdResourcePath stackBounds opBounds count trace dynamic) :
    stackTraceBound
        ((stackThresholdFold true [some StackTraceBound.empty] stackBounds).getD
          count none) trace ∧
      dynamicChargeBound
        ((opThresholdFold [some 0] opBounds).getD count none) dynamic := by
  induction path with
  | nil =>
      exact ⟨⟨StackTraceBound.empty, rfl, Int.le_refl _, Int.le_refl _⟩,
        ⟨0, rfl, Nat.le_refl _⟩⟩
  | @sat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      rw [stackThresholdFold_append, stackThresholdStep_getD_succ,
        opThresholdFold_append, opThresholdStep_getD_succ]
      constructor
      · apply stackTraceBound_choiceRight
        simpa using stackTraceBound_sequential ih.1
          (stackTraceBound_thresholdChildSat stackSelected stackBounds.isEmpty)
      · apply dynamicChargeBound_choiceRight
        exact dynamicChargeBound_sequential ih.2
          ⟨childDynamic, opSelected, Nat.le_refl _⟩
  | @dsat stackBounds opBounds count dynamic trace stackChild opChild
      childTrace childDynamic prior stackSelected opSelected ih =>
      rw [stackThresholdFold_append, opThresholdFold_append]
      cases count with
      | zero =>
          rw [stackThresholdStep_getD_zero, opThresholdStep_getD_zero]
          constructor
          · simpa using stackTraceBound_sequential ih.1
              (stackTraceBound_thresholdChildDsat stackSelected
                stackBounds.isEmpty)
          · exact dynamicChargeBound_sequential ih.2
              ⟨childDynamic, opSelected, Nat.le_refl _⟩
      | succ count =>
          rw [stackThresholdStep_getD_succ, opThresholdStep_getD_succ]
          constructor
          · apply stackTraceBound_choiceLeft
            simpa using stackTraceBound_sequential ih.1
              (stackTraceBound_thresholdChildDsat stackSelected
                stackBounds.isEmpty)
          · apply dynamicChargeBound_choiceLeft
            exact dynamicChargeBound_sequential ih.2
              ⟨childDynamic, opSelected, Nat.le_refl _⟩

mutual
  /-- Exact Core-style stack summaries for usable generated paths. -/
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
          StackTraceSet.choice
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.dsat
                (some StackTraceBound.branch)) zBounds.dsat)
            (StackTraceSet.sequential
              (StackTraceSet.sequential xBounds.sat
                (some StackTraceBound.branch)) yBounds.dsat)⟩
    | .and_v x y =>
        ⟨StackTraceSet.sequential (stackPathBounds x).sat
            (stackPathBounds y).sat,
          StackTraceSet.sequential (stackPathBounds x).sat
            (stackPathBounds y).dsat⟩
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

/-- A concrete exact-count threshold path is bounded by the public
    satisfaction summary for that threshold. The internal dynamic-programming
    table remains an implementation detail. -/
theorem ThresholdStackPath.bounds_thresh
    {fragments : List CoreFragment} {count : Nat} {netDiff : Int}
    (path : ThresholdStackPath (stackPathBoundsList fragments) count netDiff) :
    ∃ trace,
      (stackPathBounds (.thresh count fragments)).sat = some trace ∧
        netDiff ≤ trace.netDiff := by
  obtain ⟨stateTrace, stateEq, bounded⟩ :=
    stackThresholdFold_bounds_path path
  let suffix := StackTraceBound.push.sequential StackTraceBound.equal
  refine ⟨stateTrace.sequential suffix, ?_, ?_⟩
  · simp only [stackPathBounds]
    rw [stateEq]
    rfl
  · simp only [StackTraceBound.sequential, suffix, StackTraceBound.push,
      StackTraceBound.equal]
    omega

/-- An all-dissatisfaction threshold path is bounded by the public
    dissatisfaction summary, independently of the threshold literal. -/
theorem ThresholdStackPath.bounds_thresh_dsat
    {fragments : List CoreFragment} {threshold : Nat} {netDiff : Int}
    (path : ThresholdStackPath (stackPathBoundsList fragments) 0 netDiff) :
    ∃ trace,
      (stackPathBounds (.thresh threshold fragments)).dsat = some trace ∧
        netDiff ≤ trace.netDiff := by
  obtain ⟨stateTrace, stateEq, bounded⟩ :=
    stackThresholdFold_bounds_path path
  let suffix := StackTraceBound.push.sequential StackTraceBound.equal
  refine ⟨stateTrace.sequential suffix, ?_, ?_⟩
  · simp only [stackPathBounds]
    rw [stateEq]
    rfl
  · simp only [StackTraceBound.sequential, suffix, StackTraceBound.push,
      StackTraceBound.equal]
    omega

/-- A concrete exact-count threshold choice is bounded by both public resource
    summaries for the same satisfaction path. The returned stack bound includes
    the final threshold literal and equality comparison. -/
theorem ThresholdResourcePath.bounds_thresh
    {fragments : List CoreFragment} {count dynamic : Nat}
    {trace : StackTraceBound}
    (path : ThresholdResourcePath (stackPathBoundsList fragments)
      (opPathBoundsList fragments) count trace dynamic) :
    ∃ stackLimit opLimit,
      (stackPathBounds (.thresh count fragments)).sat = some stackLimit ∧
      (opPathBounds (.thresh count fragments)).sat = some opLimit ∧
      trace.thresholdComparison.netDiff ≤ stackLimit.netDiff ∧
      trace.thresholdComparison.exec ≤ stackLimit.exec ∧
      dynamic ≤ opLimit := by
  obtain ⟨stackBound, dynamicBound⟩ :=
    thresholdResourceFold_bounds_path path
  have suffixBound : stackTraceBound
      (some (StackTraceBound.push.sequential StackTraceBound.equal))
      (StackTraceBound.push.sequential StackTraceBound.equal) :=
    ⟨_, rfl, Int.le_refl _, Int.le_refl _⟩
  obtain ⟨stackLimit, stackEq, netBound, execBound⟩ :=
    stackTraceBound_sequential stackBound suffixBound
  obtain ⟨opLimit, opEq, dynamicLe⟩ := dynamicBound
  refine ⟨stackLimit, opLimit, ?_, ?_, netBound, execBound, dynamicLe⟩
  · simpa [stackPathBounds, StackTraceBound.thresholdComparison] using stackEq
  · simpa [opPathBounds] using opEq

/-- An all-dissatisfaction threshold choice is bounded by both public
    dissatisfaction summaries. Its dynamic charge is independent of the
    threshold literal used by the enclosing fragment. -/
theorem ThresholdResourcePath.bounds_thresh_dsat
    {fragments : List CoreFragment} {threshold dynamic : Nat}
    {trace : StackTraceBound}
    (path : ThresholdResourcePath (stackPathBoundsList fragments)
      (opPathBoundsList fragments) 0 trace dynamic) :
    ∃ stackLimit opLimit,
      (stackPathBounds (.thresh threshold fragments)).dsat = some stackLimit ∧
      (opPathBounds (.thresh threshold fragments)).dsat = some opLimit ∧
      trace.thresholdComparison.netDiff ≤ stackLimit.netDiff ∧
      trace.thresholdComparison.exec ≤ stackLimit.exec ∧
      dynamic ≤ opLimit := by
  obtain ⟨stackBound, dynamicBound⟩ :=
    thresholdResourceFold_bounds_path path
  have suffixBound : stackTraceBound
      (some (StackTraceBound.push.sequential StackTraceBound.equal))
      (StackTraceBound.push.sequential StackTraceBound.equal) :=
    ⟨_, rfl, Int.le_refl _, Int.le_refl _⟩
  obtain ⟨stackLimit, stackEq, netBound, execBound⟩ :=
    stackTraceBound_sequential stackBound suffixBound
  obtain ⟨opLimit, opEq, dynamicLe⟩ := dynamicBound
  refine ⟨stackLimit, opLimit, ?_, ?_, netBound, execBound, dynamicLe⟩
  · simpa [stackPathBounds, StackTraceBound.thresholdComparison] using stackEq
  · simpa [opPathBounds] using opEq

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
