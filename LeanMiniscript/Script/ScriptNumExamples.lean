import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
# Script-number decoding and evaluation fixtures

These examples pin the signed-magnitude codec and the numeric failure
boundaries used by compiler-emitted opcodes. Ordinary arithmetic uses the
four-byte `CScriptNum` limit; CLTV and CSV use the extended five-byte limit.
-/

private def strictNumberFlags : ScriptFlags := {}

private def relaxedNumberFlags : ScriptFlags where
  minimalData := false

private def numberFixtureTx : TxContext where
  locktime := 4294967295
  sequence := 4294967295
  sigHash := ⟨#[]⟩

/-- Redundant high zero: numerically one, but not minimally encoded. -/
def nonMinimalOne : StackElement := ⟨#[0x01, 0x00]⟩

/-- The largest unsigned 32-bit value needs a fifth sign-protection byte. -/
def uint32MaxScriptNum : StackElement := ⟨#[0xff, 0xff, 0xff, 0xff, 0x00]⟩

/-! ## Codec boundaries -/

example : decodeScriptNum (scriptNum 0) true maxArithmeticScriptNumBytes =
    .ok 0 := by
  rfl

example : decodeScriptNum (scriptNum 128) true maxArithmeticScriptNumBytes =
    .ok 128 := by
  rfl

example : decodeScriptNum (scriptNum (-128)) true maxArithmeticScriptNumBytes =
    .ok (-128) := by
  rfl

example : decodeScriptNum (scriptNum 2147483647) true
    maxArithmeticScriptNumBytes = .ok 2147483647 := by
  rfl

example : decodeScriptNum (scriptNum (-2147483647)) true
    maxArithmeticScriptNumBytes = .ok (-2147483647) := by
  rfl

example : decodeScriptNum (scriptNum 2147483648) true
    maxArithmeticScriptNumBytes = .error .scriptNumOverflow := by
  rfl

example : decodeScriptNum nonMinimalOne true maxArithmeticScriptNumBytes =
    .error .scriptNumNonMinimal := by
  rfl

example : decodeScriptNum nonMinimalOne false maxArithmeticScriptNumBytes =
    .ok 1 := by
  rfl

/-- Negative zero is accepted only when minimal encoding is not required. -/
example : decodeScriptNum ⟨#[0x80]⟩ true maxArithmeticScriptNumBytes =
    .error .scriptNumNonMinimal := by
  rfl

example : decodeScriptNum ⟨#[0x80]⟩ false maxArithmeticScriptNumBytes =
    .ok 0 := by
  rfl

example : decodeScriptNum uint32MaxScriptNum true maxArithmeticScriptNumBytes =
    .error .scriptNumOverflow := by
  rfl

example : decodeScriptNum uint32MaxScriptNum true maxTimelockScriptNumBytes =
    .ok 4294967295 := by
  rfl

/-! ## Ordinary numeric opcodes -/

/-- Arithmetic consumes signed values and emits a canonical result. -/
example : Eval [.op .OP_ADD] [scriptNum (-2), scriptNum 3] []
    strictNumberFlags numberFixtureTx (.success [scriptNum 1] []) := by
  apply Eval.add (a := -2) (b := 3)
  · rfl
  · exact Eval.done

/-- The four-byte bound applies to inputs; arithmetic may emit a canonical
    result that needs a fifth byte. -/
example : Eval [.op .OP_ADD] [scriptNum 2147483647, scriptNum 1] []
    strictNumberFlags numberFixtureTx
    (.success [scriptNum 2147483648] []) := by
  apply Eval.add (a := 2147483647) (b := 1)
  · rfl
  · exact Eval.done

/-- MINIMALDATA turns a redundant encoding into a terminal numeric error. -/
example : Eval [.op .OP_ADD] [nonMinimalOne, scriptNum 2] []
    strictNumberFlags numberFixtureTx (.failure .scriptNumNonMinimal) := by
  exact Eval.binaryScriptNumFailure (opcode := .OP_ADD) rfl (by rfl)

/-- The ordinary four-byte limit is enforced even for a minimally encoded
    value that CLTV/CSV can consume. -/
example : Eval [.op .OP_ADD] [scriptNum 1, uint32MaxScriptNum] []
    strictNumberFlags numberFixtureTx (.failure .scriptNumOverflow) := by
  exact Eval.binaryScriptNumFailure (opcode := .OP_ADD) rfl (by rfl)

/-- With MINIMALDATA disabled, numeric equality compares decoded values rather
    than raw byte strings. -/
example : Eval [.op .OP_NUMEQUAL] [nonMinimalOne, scriptNum 1] []
    relaxedNumberFlags numberFixtureTx (.success [trueElement] []) := by
  apply Eval.numequal (a := 1) (b := 1)
  · rfl
  · exact Eval.done

example : Eval [.op .OP_BOOLAND] [scriptNum (-1), scriptNum 0] []
    strictNumberFlags numberFixtureTx (.success [falseElement] []) := by
  apply Eval.booland (a := -1) (b := 0)
  · rfl
  · exact Eval.done

example : Eval [.op .OP_BOOLOR] [scriptNum (-1), scriptNum 0] []
    strictNumberFlags numberFixtureTx (.success [trueElement] []) := by
  apply Eval.boolor (a := -1) (b := 0)
  · rfl
  · exact Eval.done

example : Eval [.op .OP_0NOTEQUAL] [scriptNum (-1)] []
    strictNumberFlags numberFixtureTx (.success [trueElement] []) := by
  apply Eval.zeroNotEqual (value := -1)
  · rfl
  · exact Eval.done

example : Eval [.op .OP_0NOTEQUAL] [nonMinimalOne] []
    strictNumberFlags numberFixtureTx (.failure .scriptNumNonMinimal) := by
  apply Eval.unary_scriptnum_failure
  rfl

/-- CHECKSIGADD decodes the middle stack item before consulting the signature
    oracle, so malformed counts fail without a cryptographic premise. -/
example : Eval [.op .OP_CHECKSIGADD]
    [⟨#[0x02]⟩, nonMinimalOne, ⟨#[]⟩] []
    strictNumberFlags numberFixtureTx (.failure .scriptNumNonMinimal) := by
  apply Eval.checksigadd_scriptnum_failure
  rfl

/-! ## Timelock numeric boundaries -/

example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [uint32MaxScriptNum] []
    strictNumberFlags numberFixtureTx
    (.success [uint32MaxScriptNum] []) := by
  apply Eval.checklocktimeverify_success (n := 4294967295)
  · rfl
  · omega
  · simp [locktimeSatisfied, numberFixtureTx]
  · exact Eval.done

example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [uint32MaxScriptNum] []
    strictNumberFlags numberFixtureTx
    (.success [uint32MaxScriptNum] []) := by
  apply Eval.checksequenceverify_success (n := 4294967295)
  · rfl
  · omega
  · simp [sequenceSatisfied, numberFixtureTx]
  · exact Eval.done

example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum (-1)] []
    strictNumberFlags numberFixtureTx (.failure .negativeLocktime) := by
  apply Eval.timelock_negative_failure (value := -1)
  · rfl
  · rfl
  · omega

example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [nonMinimalOne] []
    strictNumberFlags numberFixtureTx (.failure .scriptNumNonMinimal) := by
  exact Eval.timelockScriptNumFailure (opcode := .OP_CHECKSEQUENCEVERIFY)
    rfl (by rfl)

/-- The explicit decoder failure excludes a successful result for the same
    binary numeric state. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_ADD] [nonMinimalOne, scriptNum 2] []
      strictNumberFlags numberFixtureTx (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.binaryScriptNumFailure_result
    (opcode := .OP_ADD) (error := .scriptNumNonMinimal)
    (usesNumbers := rfl) (decoded := by rfl) evaluated
  cases impossible

end LeanMiniscript.Script
