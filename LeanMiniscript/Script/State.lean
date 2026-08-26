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
  /-- `SCRIPT_VERIFY_MINIMALDATA`: require minimal Script-number operands. -/
  minimalData : Bool := true
  /-- BIP 147: Require dummy element for CHECKMULTISIG to be null -/
  nullDummy : Bool := true
  /-- BIP 66: Strict DER signature encoding -/
  strictEncoding : Bool := true
  deriving Repr

/-- Transaction context needed for signature verification and timelocks. -/
structure TxContext where
  /-- Signed transaction version used to activate BIP 68 relative locktimes. -/
  version : Int
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
  | scriptNumOverflow
  | scriptNumNonMinimal
  | pubkeyCount
  | signatureCount
  | negativeLocktime
  | nullDummy
  | equalVerify
  | verify
  | checkSequenceVerify
  | checkLockTimeVerify
  | minimalIf
  | unbalancedConditional
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

/-- Opcodes in the generated subset that decode both operands as Script
    numbers with the ordinary four-byte limit. -/
def Opcode.usesBinaryScriptNums : Opcode → Bool
  | .OP_ADD | .OP_BOOLAND | .OP_BOOLOR | .OP_NUMEQUAL => true
  | _ => false

/-- Timelock opcodes decode one Script number with the extended five-byte
    limit. -/
def Opcode.usesTimelockScriptNum : Opcode → Bool
  | .OP_CHECKSEQUENCEVERIFY | .OP_CHECKLOCKTIMEVERIFY => true
  | _ => false

/-- Final execution result. Small-step execution represents intermediate
    states with `ExecState` directly rather than as a final result variant. -/
inductive ExecResult where
  | success : Stack → Stack → ExecResult -- Script succeeded with final main and alt stacks
  | failure : ScriptError → ExecResult   -- Script failed with a modeled error
  deriving Repr

/-- Bitcoin's truthiness check: a byte array is true iff it is not all-zero
    after ignoring the sign bit of its final byte. This makes the empty vector,
    every all-zero vector, and negative zero (`00...80`) false. -/
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

/-- Ordinary arithmetic opcodes accept at most four encoded bytes. -/
def maxArithmeticScriptNumBytes : Nat := 4

/-- CLTV and CSV accept five-byte operands so unsigned 32-bit transaction
    fields remain representable. -/
def maxTimelockScriptNumBytes : Nat := 5

/-- Consensus limit for public keys consumed by legacy `OP_CHECKMULTISIG`. -/
def maxPubKeysPerMultiSig : Nat := 20

/-- Clear the sign bit on the most-significant byte of a little-endian signed
    magnitude. -/
def clearScriptNumSignBit : List UInt8 → List UInt8
  | [] => []
  | [last] => [UInt8.ofNat (last.toNat % 128)]
  | byte :: rest => byte :: clearScriptNumSignBit rest

/-- Decode an unsigned little-endian byte list. -/
def decodeUnsignedLEAux : List UInt8 → Nat → Nat
  | [], _ => 0
  | byte :: rest, place =>
      byte.toNat * place + decodeUnsignedLEAux rest (place * 256)

/-- Whether a nonempty signed-magnitude encoding has its sign bit set. -/
def scriptNumIsNegative (bytes : List UInt8) : Bool :=
  match bytes.reverse with
  | [] => false
  | last :: _ => 128 ≤ last.toNat

/-- Bitcoin Core's minimal signed-magnitude predicate. Empty bytes are the
    unique minimal zero. A zero-valued final byte is allowed only when the
    preceding byte needs protection from being interpreted as a sign bit. -/
def scriptNumIsMinimal (bytes : StackElement) : Bool :=
  match bytes.data.toList.reverse with
  | [] => true
  | last :: preceding =>
      if last.toNat % 128 != 0 then
        true
      else
        match preceding with
        | [] => false
        | previous :: _ => 128 ≤ previous.toNat

/-- Decode Bitcoin Script's little-endian signed-magnitude number format.

    Operand-size failure takes precedence over minimal-encoding failure, as in
    `CScriptNum`. When `requireMinimal` is false, redundant sign and zero bytes
    are accepted while the byte limit remains enforced. -/
def decodeScriptNum (bytes : StackElement) (requireMinimal : Bool)
    (maxBytes : Nat) : Except ScriptError Int :=
  if bytes.size > maxBytes then
    .error .scriptNumOverflow
  else if requireMinimal && !scriptNumIsMinimal bytes then
    .error .scriptNumNonMinimal
  else
    let encoded := bytes.data.toList
    let magnitude := decodeUnsignedLEAux (clearScriptNumSignBit encoded) 1
    if scriptNumIsNegative encoded then
      .ok (-Int.ofNat magnitude)
    else
      .ok (Int.ofNat magnitude)

/-- Decode two ordinary numeric operands. `belowTop` is decoded first to match
    Bitcoin Core's `stacktop(-2)` then `stacktop(-1)` evaluation order. The
    returned pair remains in this repository's top-first stack order. -/
def decodeBinaryScriptNums (flags : ScriptFlags) (top belowTop : StackElement) :
    Except ScriptError (Int × Int) := do
  let belowValue ← decodeScriptNum belowTop flags.minimalData
    maxArithmeticScriptNumBytes
  let topValue ← decodeScriptNum top flags.minimalData
    maxArithmeticScriptNumBytes
  pure (topValue, belowValue)

/-- Dynamically decoded legacy multisignature operands in top-first stack order.

    The count elements and dummy are consumed by `OP_CHECKMULTISIG`; `rest`
    remains below them. Public keys and signatures retain the order in which
    the Bitcoin Core interpreter visits them from the top of the stack. -/
structure CheckMultiSigOperands where
  pubkeys : Stack
  signatures : Stack
  dummy : StackElement
  rest : Stack
  deriving Repr

/-- Decode the variable-size `OP_CHECKMULTISIG` stack frame.

    This follows Bitcoin Core's observable validation order: decode and bound
    the public-key count, require the public-key frame and signature-count
    element, decode and bound the signature count, then require the signatures
    and historical dummy element. The ordinary four-byte Script-number limit
    applies to both counts. -/
def decodeCheckMultiSigOperands (flags : ScriptFlags) (stack : Stack) :
    Except ScriptError CheckMultiSigOperands := do
  let (pubkeyCountBytes, afterPubkeyCount) ←
    match stack with
    | [] => .error .stackUnderflow
    | countBytes :: rest => .ok (countBytes, rest)
  let pubkeyCount ← decodeScriptNum pubkeyCountBytes flags.minimalData
    maxArithmeticScriptNumBytes
  if pubkeyCount < 0 then
    .error .pubkeyCount
  else if (maxPubKeysPerMultiSig : Int) < pubkeyCount then
    .error .pubkeyCount
  else
    let n := pubkeyCount.toNat
    if afterPubkeyCount.length < n + 1 then
      .error .stackUnderflow
    else
      let pubkeys := afterPubkeyCount.take n
      match afterPubkeyCount.drop n with
      | [] => .error .stackUnderflow
      | signatureCountBytes :: afterSignatureCount => do
          let signatureCount ← decodeScriptNum signatureCountBytes
            flags.minimalData maxArithmeticScriptNumBytes
          if signatureCount < 0 then
            .error .signatureCount
          else if pubkeyCount < signatureCount then
            .error .signatureCount
          else
            let k := signatureCount.toNat
            if afterSignatureCount.length < k + 1 then
              .error .stackUnderflow
            else
              let signatures := afterSignatureCount.take k
              match afterSignatureCount.drop k with
              | [] => .error .stackUnderflow
              | dummy :: rest => .ok { pubkeys, signatures, dummy, rest }

theorem scriptNum_zero : scriptNum 0 = falseElement := by
  rfl

theorem scriptNum_one : scriptNum 1 = trueElement := by
  rfl

theorem scriptNum_128 : scriptNum 128 = ⟨#[0x80, 0x00]⟩ := by
  rfl

theorem scriptNum_neg_one : scriptNum (-1) = ⟨#[0x81]⟩ := by
  rfl

/-- Values below this threshold are block heights; values at or above it are
    Unix timestamps. This is Bitcoin Core's `LOCKTIME_THRESHOLD`. -/
def locktimeThreshold : Nat := 500000000

/-- The final input sequence disables transaction locktime. -/
def sequenceFinal : Nat := 4294967295

/-- BIP 68 flag that disables relative-locktime interpretation. -/
def sequenceLocktimeDisableFlag : Nat := 2147483648

/-- BIP 68 flag selecting 512-second units instead of block heights. -/
def sequenceLocktimeTypeFlag : Nat := 4194304

/-- BIP 68 mask retaining the low 16-bit relative-locktime value. -/
def sequenceLocktimeMask : Nat := 65535

/-- Whether a locktime is timestamp-based rather than height-based. -/
def locktimeIsTimestamp (locktime : Nat) : Bool :=
  locktimeThreshold ≤ locktime

/-- Whether the BIP 68 disable bit is set. The quotient formulation is the
    single-bit test used by Bitcoin Core, stated without fixing a machine-word
    representation for Script-number operands. -/
def sequenceDisableFlagSet (sequence : Nat) : Bool :=
  sequence / sequenceLocktimeDisableFlag % 2 == 1

/-- Whether the BIP 68 type bit selects 512-second intervals. -/
def sequenceTypeFlagSet (sequence : Nat) : Bool :=
  sequence / sequenceLocktimeTypeFlag % 2 == 1

/-- The consensus-enforced low 16-bit relative-locktime value. -/
def sequenceLocktimeValue (sequence : Nat) : Nat :=
  sequence % (sequenceLocktimeMask + 1)

/-- Bitcoin Core's BIP 65 `CheckLockTime` conditions for
    `OP_CHECKLOCKTIMEVERIFY`: matching height/time classes, an adequate
    transaction locktime, and a non-final sequence for the current input. -/
def locktimeSatisfied (required : Nat) (ctx : TxContext) : Prop :=
  locktimeIsTimestamp required = locktimeIsTimestamp ctx.locktime ∧
  required ≤ ctx.locktime ∧
  ctx.sequence ≠ sequenceFinal

instance (required : Nat) (ctx : TxContext) :
    Decidable (locktimeSatisfied required ctx) := by
  unfold locktimeSatisfied
  infer_instance

/-- Bitcoin Core's BIP 112 `OP_CHECKSEQUENCEVERIFY` conditions. An operand
    with the disable bit set is a forward-compatible NOP. Otherwise BIP 68
    requires transaction version 2 or later, an active input sequence, equal
    height/time types, and an adequate masked 16-bit relative-locktime value. -/
def sequenceSatisfied (required : Nat) (ctx : TxContext) : Prop :=
  sequenceDisableFlagSet required = true ∨
  ((2 : Int) ≤ ctx.version ∧
    sequenceDisableFlagSet ctx.sequence = false ∧
    sequenceTypeFlagSet required = sequenceTypeFlagSet ctx.sequence ∧
    sequenceLocktimeValue required ≤ sequenceLocktimeValue ctx.sequence)

instance (required : Nat) (ctx : TxContext) :
    Decidable (sequenceSatisfied required ctx) := by
  unfold sequenceSatisfied
  infer_instance

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

instance (flags : ScriptFlags) (b : StackElement) :
    Decidable (minimalIfSatisfied flags b) := by
  unfold minimalIfSatisfied
  infer_instance

/-- Whether the legacy CHECKMULTISIG dummy argument satisfies NULLDUMMY. -/
def nullDummySatisfied (flags : ScriptFlags) (dummy : StackElement) : Prop :=
  flags.nullDummy = false ∨ stackElementEq dummy falseElement = true

instance (flags : ScriptFlags) (dummy : StackElement) :
    Decidable (nullDummySatisfied flags dummy) := by
  unfold nullDummySatisfied
  infer_instance

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
