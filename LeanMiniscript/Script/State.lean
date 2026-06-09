import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-- A stack element is a byte array.
    Bitcoin Script uses byte arrays for all stack operations. -/
abbrev StackElement := ByteArray

/-- The main and alt stacks. -/
abbrev Stack := List StackElement

/-- Script verification flags that affect execution semantics. -/
structure ScriptFlags where
  /-- BIP 141: Require minimal encoding for IF/NOTIF arguments -/
  minimalIf : Bool := true
  /-- BIP 147: Require dummy element for CHECKMULTISIG to be null -/
  nullDummy : Bool := true
  /-- BIP 66: Strict DER signature encoding -/
  strictEncoding : Bool := true
  deriving Repr

/-- Transaction context needed for signature verification and timelocks. -/
structure TxContext where
  /-- Transaction locktime for OP_CHECKLOCKTIMEVERIFY -/
  locktime : Nat
  /-- Input sequence number for OP_CHECKSEQUENCEVERIFY -/
  sequence : Nat
  /-- Signature hash (simplified — real implementation needs full tx) -/
  sigHash : ByteArray
  deriving Repr

/-- The complete execution state of the Bitcoin Script interpreter. -/
structure ExecState where
  /-- Main data stack -/
  stack : Stack
  /-- Alternative stack -/
  altStack : Stack
  /-- Remaining script to execute -/
  script : Script
  /-- Program counter (index into original script) -/
  pc : Nat
  /-- Condition stack for IF/ELSE nesting (true = executing, false = skipping) -/
  condStack : List Bool
  /-- Verification flags -/
  flags : ScriptFlags
  /-- Transaction context -/
  txCtx : TxContext
  deriving Repr

/-- Execution result. -/
inductive ExecResult where
  | success : Stack → Stack → ExecResult -- Script succeeded with final main and alt stacks
  | failure : String → ExecResult        -- Script failed with error message
  | running : ExecState → ExecResult     -- Still executing (for small-step)
  deriving Repr

/-- Bitcoin's truthiness check: a byte array is true iff it is not all-zero
    (with the exception that negative zero 0x80 is also false).
    Simplified: empty or all-zero → false, otherwise → true. -/
def castToBool (b : StackElement) : Bool :=
  -- Check if any byte is nonzero (ignoring sign bit of last byte)
  if b.size == 0 then false
  else
    let lastIdx := b.size - 1
    -- Negative zero: only last byte is 0x80, rest are 0x00
    b.data.toList.enum.any fun ⟨i, byte⟩ =>
      if i == lastIdx then byte != 0x00 && byte != 0x80
      else byte != 0x00

/-- The canonical "true" stack element (0x01). -/
def trueElement : StackElement := ⟨#[0x01]⟩

/-- The canonical "false" stack element (empty). -/
def falseElement : StackElement := ⟨#[]⟩

/-- Convert a Bool to a stack element. -/
def boolToElement (b : Bool) : StackElement :=
  if b then trueElement else falseElement

/-- Byte-array equality for stack elements, kept local to script-state
    predicates instead of introducing a global `BEq ByteArray` instance. -/
def stackElementEq (x y : StackElement) : Bool :=
  x.data == y.data

/-- MINIMALIF accepts only the canonical false and true stack elements as
    OP_IF/OP_NOTIF arguments. -/
def minimalIfArg (b : StackElement) : Bool :=
  stackElementEq b falseElement || stackElementEq b trueElement

/-- Whether an IF-like opcode argument satisfies the active script flags. -/
def minimalIfSatisfied (flags : ScriptFlags) (b : StackElement) : Prop :=
  flags.minimalIf = false ∨ minimalIfArg b = true

theorem falseElement_minimalIfArg : minimalIfArg falseElement = true :=
  by native_decide

theorem trueElement_minimalIfArg : minimalIfArg trueElement = true :=
  by native_decide

/-- A concrete non-minimal truthy element used by MINIMALIF regression tests. -/
def nonMinimalTruthyElement : StackElement := ⟨#[0x02]⟩

theorem nonMinimalTruthyElement_truthy :
    castToBool nonMinimalTruthyElement = true := by
  native_decide

theorem nonMinimalTruthyElement_not_minimalIfArg :
    minimalIfArg nonMinimalTruthyElement = false := by
  native_decide

/-- Abstract hash160 function (RIPEMD160 ∘ SHA256).
    Opaque in the formal model — we only reason about its properties. -/
opaque hash160 (x : StackElement) : StackElement

/-- Abstract signature verification.
    In formal proofs we treat this as an opaque predicate.
    Returns true iff the signature is valid for the given key and sighash. -/
opaque checkSig (sig : StackElement) (pubkey : StackElement) (sigHash : ByteArray) : Bool

end LeanMiniscript.Script
