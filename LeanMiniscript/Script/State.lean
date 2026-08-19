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

/-- Script failures represented by the current semantics. Typed errors keep
    proofs independent of display strings and make case analysis exhaustive. -/
inductive ScriptError where
  | stackUnderflow
  | altStackUnderflow
  | nullDummy
  | equalVerify
  | verify
  | checkSequenceVerify
  | checkLockTimeVerify
  | minimalIf
  deriving Repr, DecidableEq, BEq

/-- Fixed main-stack inputs consumed or inspected by a modeled opcode.

    `OP_CHECKMULTISIG` is the only variable-arity opcode in the current model,
    so it has no fixed requirement. Conditional delimiters and
    `OP_FROMALTSTACK` have fixed main-stack arity zero; their structural and
    alternate-stack requirements are modeled separately. -/
def Opcode.fixedMainStackInputs? : Opcode → Option Nat
  | .OP_IF | .OP_NOTIF => some 1
  | .OP_ELSE | .OP_ENDIF => some 0
  | .OP_IFDUP | .OP_DUP => some 1
  | .OP_SWAP => some 2
  | .OP_TOALTSTACK => some 1
  | .OP_FROMALTSTACK => some 0
  | .OP_ADD | .OP_BOOLAND | .OP_BOOLOR => some 2
  | .OP_0NOTEQUAL => some 1
  | .OP_EQUAL | .OP_EQUALVERIFY | .OP_NUMEQUAL => some 2
  | .OP_SHA256 | .OP_HASH256 | .OP_RIPEMD160 | .OP_HASH160 => some 1
  | .OP_CHECKSIG => some 2
  | .OP_CHECKSIGADD => some 3
  | .OP_CHECKMULTISIG => none
  | .OP_CHECKSEQUENCEVERIFY | .OP_CHECKLOCKTIMEVERIFY => some 1
  | .OP_VERIFY | .OP_SIZE => some 1

/-- Final execution result. Small-step execution represents intermediate
    states with `ExecState` directly rather than as a final result variant. -/
inductive ExecResult where
  | success : Stack → Stack → ExecResult -- Script succeeded with final main and alt stacks
  | failure : ScriptError → ExecResult   -- Script failed with a modeled error
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
    b.data.toList.zipIdx.any fun ⟨byte, i⟩ =>
      if i == lastIdx then byte != 0x00 && byte != 0x80
      else byte != 0x00

/-- The canonical "true" stack element (0x01). -/
def trueElement : StackElement := ⟨#[0x01]⟩

/-- The canonical "false" stack element (empty). -/
def falseElement : StackElement := ⟨#[]⟩

/-- Convert a Bool to a stack element. -/
def boolToElement (b : Bool) : StackElement :=
  if b then trueElement else falseElement

/-- Encode a nonnegative magnitude as little-endian base-256 bytes.
    The fuel argument makes the definition structurally recursive; using the
    magnitude itself as fuel is enough for every nonzero input. -/
def scriptNumMagnitudeBytesAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
      if n = 0 then
        []
      else
        UInt8.ofNat (n % 256) :: scriptNumMagnitudeBytesAux fuel (n / 256)

/-- Whether the most significant byte would be confused with a sign bit. -/
def scriptNumNeedsSignByte : List UInt8 → Bool
  | [] => false
  | [byte] => 128 ≤ byte.toNat
  | _ :: rest => scriptNumNeedsSignByte rest

/-- Set the sign bit on the most significant byte of a nonempty magnitude. -/
def scriptNumSetSignBit : List UInt8 → List UInt8
  | [] => []
  | [byte] => [UInt8.ofNat (byte.toNat + 128)]
  | byte :: rest => byte :: scriptNumSetSignBit rest

/-- Canonical Bitcoin Script numeric encoding.

    Numbers are little-endian signed magnitudes. Zero is the empty byte array;
    negative numbers set the high bit of the most significant byte, appending
    a sign byte when the magnitude already uses that bit. -/
def scriptNumBytes (n : Int) : List UInt8 :=
  if n = 0 then
    []
  else
    let magnitude := n.natAbs
    let bytes := scriptNumMagnitudeBytesAux magnitude magnitude
    let negative := n < 0
    if scriptNumNeedsSignByte bytes then
      bytes ++ [if negative then 0x80 else 0x00]
    else if negative then
      scriptNumSetSignBit bytes
    else
      bytes

/-- Canonical stack element produced by numeric pushes. -/
def scriptNum (n : Int) : StackElement :=
  ⟨(scriptNumBytes n).toArray⟩

/-- Canonical stack element for a natural number. -/
def scriptNat (n : Nat) : StackElement :=
  scriptNum n

theorem scriptNum_zero : scriptNum 0 = falseElement := by
  rfl

theorem scriptNum_one : scriptNum 1 = trueElement := by
  rfl

theorem scriptNum_128 : scriptNum 128 = ⟨#[0x80, 0x00]⟩ := by
  rfl

theorem scriptNum_neg_one : scriptNum (-1) = ⟨#[0x81]⟩ := by
  rfl

/-- Simplified locktime check used by `OP_CHECKLOCKTIMEVERIFY`.
    The full Bitcoin rule also checks locktime classes and final sequence;
    Miniscript AST validation tracks the class-level side conditions. -/
def locktimeSatisfied (required : Nat) (ctx : TxContext) : Prop :=
  required ≤ ctx.locktime

/-- Simplified sequence check used by `OP_CHECKSEQUENCEVERIFY`.
    The full Bitcoin rule also interprets BIP 68 disable/type bits; Miniscript
    AST validation tracks the class-level side conditions. -/
def sequenceSatisfied (required : Nat) (ctx : TxContext) : Prop :=
  required ≤ ctx.sequence

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

/-- Whether the legacy CHECKMULTISIG dummy argument satisfies NULLDUMMY. -/
def nullDummySatisfied (flags : ScriptFlags) (dummy : StackElement) : Prop :=
  flags.nullDummy = false ∨ stackElementEq dummy falseElement = true

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

/-- Abstract SHA256 function.
    Opaque in the formal model — we only reason about its properties. -/
opaque sha256 (x : StackElement) : StackElement

/-- Abstract HASH256 function (SHA256 ∘ SHA256).
    Opaque in the formal model — we only reason about its properties. -/
opaque hash256 (x : StackElement) : StackElement

/-- Abstract RIPEMD160 function.
    Opaque in the formal model — we only reason about its properties. -/
opaque ripemd160 (x : StackElement) : StackElement

/-- Abstract HASH160 function (RIPEMD160 ∘ SHA256).
    Opaque in the formal model — we only reason about its properties. -/
opaque hash160 (x : StackElement) : StackElement

/-- Abstract signature verification.
    In formal proofs we treat this as an opaque predicate.
    Returns true iff the signature is valid for the given key and sighash. -/
opaque checkSig (sig : StackElement) (pubkey : StackElement) (sigHash : ByteArray) : Bool

/-- Abstract legacy multisignature verification.
    This models the cryptographic matching of signatures to public keys while
    keeping the stack discipline of `OP_CHECKMULTISIG` explicit in `Eval`. -/
opaque checkMultiSig
  (sigs : List StackElement) (pubkeys : List StackElement) (sigHash : ByteArray) : Bool

end LeanMiniscript.Script
