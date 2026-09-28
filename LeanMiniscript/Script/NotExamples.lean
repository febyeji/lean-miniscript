import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! OP_NOT regressions run after canonical serialization and deserialization.
The input stack is kept as raw bytes to exercise numeric decoding boundaries. -/

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty,
    sigVersion := .tapscript }

private def oracle : CryptoOracle :=
  CryptoOracle.pureLeanHashes (fun _ _ _ => false)

private def run (script : Script) (stack : Stack := [])
    (minimalData : Bool := true) (alt : Stack := []) (weight : Nat := 17) :
    Option WeightedResult := do
  let bytes ← (serializeScript script).toOption
  let decoded ← (deserializeScript bytes).toOption
  return evaluateWithRuntimeLimits oracle decoded stack alt { minimalData := minimalData }
    ctx weight

-- Raw expected bytes pin canonical output for zero, positive and negative values,
-- including both ends of the four-byte signed-magnitude domain.
private def canonicalFixtures : List (ByteArray × ByteArray) :=
  [(⟨#[]⟩, ⟨#[1]⟩), (⟨#[1]⟩, ⟨#[]⟩), (⟨#[11]⟩, ⟨#[]⟩),
   (⟨#[0x81]⟩, ⟨#[]⟩), (⟨#[0x80, 0]⟩, ⟨#[]⟩), (⟨#[0x80, 0x80]⟩, ⟨#[]⟩),
   (⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[]⟩),
   (⟨#[0xff, 0xff, 0xff, 0xff]⟩, ⟨#[]⟩)]

example : [false, true].all (fun minimal => canonicalFixtures.all fun (input, expected) =>
    run [.op .OP_NOT] [input] minimal == some (.success [expected] [] 17)) = true := by
  native_decide

private def nonMinimalFixtures : List (ByteArray × ByteArray) :=
  [(⟨#[0]⟩, ⟨#[1]⟩), (⟨#[0x80]⟩, ⟨#[1]⟩),
   (⟨#[0, 0]⟩, ⟨#[1]⟩), (⟨#[0, 0x80]⟩, ⟨#[1]⟩),
   (⟨#[1, 0]⟩, ⟨#[]⟩), (⟨#[1, 0x80]⟩, ⟨#[]⟩),
   (⟨#[0, 0, 0, 0x80]⟩, ⟨#[1]⟩)]

-- Relaxed decoding normalizes redundant zero, negative zero and redundant ±1.
example : nonMinimalFixtures.all (fun (input, expected) =>
    run [.op .OP_NOT] [input] false == some (.success [expected] [] 17)) = true := by
  native_decide

-- The same bytes fail before the suffix when minimalData is enabled.
example : nonMinimalFixtures.all (fun (input, _) =>
    run [.op .OP_NOT, .op .OP_DROP, .pushNum 1] [input] true ==
      some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

-- Five-byte inputs overflow under both flag settings, including encodings
-- which are also non-minimal. Size errors take precedence over minimality.
private def oversizedFixtures : List ByteArray :=
  [⟨#[0, 0, 0, 0x80, 0]⟩, ⟨#[0, 0, 0, 0x80, 0x80]⟩,
   ⟨#[0, 0, 0, 0, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩]

example : [false, true].all (fun minimal => oversizedFixtures.all fun input =>
    run [.op .OP_NOT, .op .OP_DROP, .pushNum 1] [input] minimal ==
      some (.failure .scriptNumOverflow)) = true := by
  native_decide

example : run [.op .OP_NOT, .pushNum 1] [] true [trueElement] =
    some (.failure .stackUnderflow) := by
  native_decide

-- Only the top item is decoded; lower non-minimal bytes retain their order.
example : run [.op .OP_NOT] [ByteArray.empty, ⟨#[0x80]⟩, scriptNum 9]
    true [scriptNum 3] 0 =
    some (.success [trueElement, ⟨#[0x80]⟩, scriptNum 9] [scriptNum 3] 0) := by
  native_decide

example : run [.op .OP_NOT, .op .OP_NOT] [scriptNum (-1)] =
    some (.success [trueElement] [] 17) := by
  native_decide

-- Inactive execution skips underflow and numeric decoding.
example : run [.pushNum 0, .op .OP_IF, .op .OP_NOT, .op .OP_ENDIF]
    [] true [scriptNum 3] 0 = some (.success [] [scriptNum 3] 0) := by
  native_decide

example : run [.pushNum 0, .op .OP_IF, .op .OP_NOT, .op .OP_ENDIF]
    [⟨#[1, 0, 0, 0, 0]⟩] true [scriptNum 3] 0 =
    some (.success [⟨#[1, 0, 0, 0, 0]⟩] [scriptNum 3] 0) := by
  native_decide

example : run [.pushNum 0, .op .OP_IF, .op .OP_NOT, .op .OP_ENDIF]
    [⟨#[0x80]⟩] true = some (.success [⟨#[0x80]⟩] [] 17) := by
  native_decide

-- Stack count stays at the combined limit, including alternate-stack items.
example : run [.op .OP_NOT] (ByteArray.empty :: List.replicate 998 trueElement)
    true [scriptNum 3] =
    some (.success (trueElement :: List.replicate 998 trueElement) [scriptNum 3] 17) := by
  native_decide

example : run [.op .OP_NOT] (ByteArray.empty :: List.replicate 999 trueElement)
    true [scriptNum 3] = some (.failure .stackSize) := by
  native_decide

-- Numeric failure wins over an oversized combined stack after the instruction.
example : run [.op .OP_NOT] (⟨#[1, 0, 0, 0, 0]⟩ :: List.replicate 999 trueElement)
    true [scriptNum 3] = some (.failure .scriptNumOverflow) := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_NOT) = 0 := rfl

end LeanMiniscript.Script
