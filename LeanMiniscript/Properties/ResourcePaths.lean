import LeanMiniscript.Miniscript.Syntax

/-! Satisfaction-path summaries for dynamic opcode counts and combined stack usage. -/

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript LeanMiniscript.Script

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

namespace ResourceAnalysis

def opThresholdMiddle (child : OpPathBounds)
    (previous : PathMaximum) : List PathMaximum → List PathMaximum
  | [] => [PathMaximum.sequential previous child.sat]
  | current :: rest =>
      PathMaximum.choice
          (PathMaximum.sequential current child.dsat)
          (PathMaximum.sequential previous child.sat) ::
        opThresholdMiddle child current rest

/-- Add one threshold child to the dynamic-programming states indexed by the
    number of satisfied children. -/
def opThresholdStep
    (states : List PathMaximum) (child : OpPathBounds) : List PathMaximum :=
  match states with
  | [] => []
  | first :: rest =>
      PathMaximum.sequential first child.dsat ::
        opThresholdMiddle child first rest

def opThresholdFold :
    List PathMaximum → List OpPathBounds → List PathMaximum
  | states, [] => states
  | states, child :: children =>
      opThresholdFold (opThresholdStep states child) children

end ResourceAnalysis

open ResourceAnalysis

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

namespace ResourceAnalysis

def stackThresholdMiddle (child : StackPathBounds)
    (previous : StackTraceSet) : List StackTraceSet → List StackTraceSet
  | [] => [StackTraceSet.sequential previous child.sat]
  | current :: rest =>
      StackTraceSet.choice
          (StackTraceSet.sequential current child.dsat)
          (StackTraceSet.sequential previous child.sat) ::
        stackThresholdMiddle child current rest

def stackThresholdStep
    (states : List StackTraceSet) (child : StackPathBounds) : List StackTraceSet :=
  match states with
  | [] => []
  | first :: rest =>
      StackTraceSet.sequential first child.dsat ::
        stackThresholdMiddle child first rest

def appendThresholdAdd (first : Bool)
    (bounds : StackPathBounds) : StackPathBounds :=
  if first then bounds else
    ⟨StackTraceSet.sequential bounds.sat (some StackTraceBound.binary),
      StackTraceSet.sequential bounds.dsat (some StackTraceBound.binary)⟩

def stackThresholdFold :
    Bool → List StackTraceSet → List StackPathBounds → List StackTraceSet
  | _, states, [] => states
  | first, states, child :: children =>
      stackThresholdFold false
        (stackThresholdStep states (appendThresholdAdd first child)) children

end ResourceAnalysis

open ResourceAnalysis

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

end LeanMiniscript.Properties
