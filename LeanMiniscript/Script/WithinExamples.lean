import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! WITHIN regressions serialize and deserialize each script before runtime
execution. Raw stack bytes exercise the numeric decoder independently of pushes. -/

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

-- Tuples list (value, lower, upper, expected bytes); stacks are top-first.
private def intervalFixtures : List (Int × Int × Int × ByteArray) :=
  [(0, 0, 1, ⟨#[1]⟩), (1, 0, 1, ⟨#[]⟩), (0, 0, 0, ⟨#[]⟩),
   (1, 2, 0, ⟨#[]⟩), (0, 1, 2, ⟨#[]⟩), (3, 1, 2, ⟨#[]⟩),
   (-1, -1, 0, ⟨#[1]⟩), (0, -1, 0, ⟨#[]⟩), (-2, -3, -1, ⟨#[1]⟩),
   (0, -100, 100, ⟨#[1]⟩), (11, -100, 100, ⟨#[1]⟩),
   (-2147483647, -2147483647, 2147483647, ⟨#[1]⟩),
   (2147483647, -2147483647, 2147483647, ⟨#[]⟩),
   (2147483646, 2147483646, 2147483647, ⟨#[1]⟩)]

example : [false, true].all (fun minimal => intervalFixtures.all fun (value, lower, upper, expected) =>
    run [.op .OP_WITHIN] [scriptNum upper, scriptNum lower, scriptNum value] minimal ==
      some (.success [expected] [] 17)) = true := by
  native_decide

-- Canonical signed four-byte inputs are supplied directly in every position.
example : run [.op .OP_WITHIN]
    [⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩,
     ⟨#[0xff, 0xff, 0xff, 0xff]⟩] = some (.success [⟨#[1]⟩] [] 17) := by
  native_decide

private def nonMinimalZeros : List ByteArray :=
  [⟨#[0]⟩, ⟨#[0x80]⟩, ⟨#[0, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0, 0, 0, 0x80]⟩]

private def nonMinimalOnes : List (ByteArray × Int) :=
  [(⟨#[1, 0]⟩, 1), (⟨#[1, 0x80]⟩, -1)]

-- Non-minimal and negative zero occupy each operand position separately.
example : nonMinimalZeros.all (fun raw =>
    ([[scriptNum 1, scriptNum 0, raw], [scriptNum 1, raw, scriptNum 0],
      [raw, scriptNum (-1), scriptNum (-1)]] : List Stack).all fun stack =>
      run [.op .OP_WITHIN] stack false == some (.success [⟨#[1]⟩] [] 17) &&
      run [.op .OP_WITHIN, .op .OP_DROP, .pushNum 1] stack true ==
        some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

example : nonMinimalOnes.all (fun (raw, value) =>
    ([[scriptNum (value + 1), scriptNum value, raw],
      [scriptNum (value + 1), raw, scriptNum value],
      [raw, scriptNum (value - 1), scriptNum (value - 1)]] : List Stack).all fun stack =>
      run [.op .OP_WITHIN] stack false == some (.success [⟨#[1]⟩] [] 17) &&
      run [.op .OP_WITHIN] stack true == some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

private def oversizedFixtures : List ByteArray :=
  [⟨#[0, 0, 0, 0x80, 0]⟩, ⟨#[0, 0, 0, 0x80, 0x80]⟩,
   ⟨#[0, 0, 0, 0, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩]

-- Size overflow precedes minimal encoding checks for each operand.
example : [false, true].all (fun minimal => oversizedFixtures.all fun raw =>
    ([[scriptNum 1, scriptNum 0, raw], [scriptNum 1, raw, scriptNum 0],
      [raw, scriptNum 0, scriptNum 0]] : List Stack).all fun stack =>
      run [.op .OP_WITHIN, .op .OP_DROP, .pushNum 1] stack minimal ==
        some (.failure .scriptNumOverflow)) = true := by
  native_decide

private def nonminimal : ByteArray := ⟨#[0x80]⟩
private def oversized : ByteArray := ⟨#[0, 0, 0, 0, 0]⟩

-- Decode value first, lower second, upper third; comparison cannot skip upper.
private def precedenceFixtures : List (Stack × ScriptError) :=
  [([oversized, oversized, nonminimal], .scriptNumNonMinimal),
   ([nonminimal, nonminimal, oversized], .scriptNumOverflow),
   ([oversized, nonminimal, scriptNum 0], .scriptNumNonMinimal),
   ([nonminimal, oversized, scriptNum 0], .scriptNumOverflow),
   ([nonminimal, scriptNum 1, scriptNum 0], .scriptNumNonMinimal),
   ([oversized, scriptNum 1, scriptNum 0], .scriptNumOverflow)]

example : precedenceFixtures.all (fun (stack, error) =>
    run [.op .OP_WITHIN, .op .OP_DROP, .pushNum 1] stack == some (.failure error)) = true := by
  native_decide

-- Underflow is checked before decoding any available operand or the suffix.
example : [false, true].all (fun minimal =>
    ([[], [oversized], [oversized, nonminimal]] : List Stack).all fun stack =>
      run [.op .OP_WITHIN, .pushNum 1] stack minimal [scriptNum 9] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- Preserve the lower stack order, alt stack and budget; execute the suffix.
example : run [.op .OP_WITHIN, .op .OP_VERIFY, .pushNum 7]
    [scriptNum 3, scriptNum 1, scriptNum 2, nonminimal, scriptNum 9]
    true [scriptNum 4] 0 =
    some (.success [scriptNum 7, nonminimal, scriptNum 9] [scriptNum 4] 0) := by
  native_decide

example : run [.op .OP_WITHIN, .op .OP_VERIFY, .pushNum 7]
    [scriptNum 2, scriptNum 1, scriptNum 2] = some (.failure .verify) := by
  native_decide

-- Skipped WITHIN does not require inputs or decode malformed numeric bytes.
example : ([[], [oversized, nonminimal, oversized]] : List Stack).all (fun stack =>
    run [.pushNum 0, .op .OP_IF, .op .OP_WITHIN, .op .OP_ENDIF]
      stack true [scriptNum 4] 0 == some (.success stack [scriptNum 4] 0)) = true := by
  native_decide

-- The low-level runtime checks combined stack size after each instruction.
-- WITHIN can shrink an initially oversized stack; witness entry bounds are separate.
example : run [.op .OP_WITHIN]
    (scriptNum 1 :: scriptNum 0 :: scriptNum 0 :: List.replicate 999 trueElement) =
    some (.success (trueElement :: List.replicate 999 trueElement) [] 17) := by
  native_decide

example : run [.op .OP_WITHIN]
    (scriptNum 1 :: scriptNum 0 :: scriptNum 0 :: List.replicate 998 trueElement)
    true [scriptNum 4] =
    some (.success (trueElement :: List.replicate 998 trueElement) [scriptNum 4] 17) := by
  native_decide

example : run [.op .OP_WITHIN]
    (scriptNum 1 :: scriptNum 0 :: scriptNum 0 :: List.replicate 999 trueElement)
    true [scriptNum 4] = some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_WITHIN]
    (scriptNum 1 :: scriptNum 0 :: oversized :: List.replicate 999 trueElement)
    true [scriptNum 4] = some (.failure .scriptNumOverflow) := by
  native_decide

-- Inactive execution skips the opcode but still enforces combined stack size.
example : evaluateRuntime oracle [.op .OP_WITHIN]
    { stack := List.replicate 1000 trueElement, altStack := [trueElement],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_WITHIN) = 0 := rfl

end LeanMiniscript.Script
