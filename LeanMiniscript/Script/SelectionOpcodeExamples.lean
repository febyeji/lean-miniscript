import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! Numeric and indexed-stack selection regressions execute serialized scripts.
Expected result bytes and stack orders are pinned independently of the evaluator. -/

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

private def numericOpcodes : List Opcode := [.OP_MIN, .OP_MAX]
private def indexedOpcodes : List Opcode := [.OP_PICK, .OP_ROLL]
private def selectionOpcodes : List Opcode := numericOpcodes ++ indexedOpcodes

-- Both operand orders, equal inputs, signs, and four-byte signed-magnitude endpoints.
private def numericFixtures : List (Int × Int × ByteArray × ByteArray) :=
  [(0, 0, ⟨#[]⟩, ⟨#[]⟩),
   (1, 1, ⟨#[1]⟩, ⟨#[1]⟩),
   (-1, -1, ⟨#[0x81]⟩, ⟨#[0x81]⟩),
   (1, 0, ⟨#[]⟩, ⟨#[1]⟩),
   (0, 1, ⟨#[]⟩, ⟨#[1]⟩),
   (-1, 0, ⟨#[0x81]⟩, ⟨#[]⟩),
   (0, -1, ⟨#[0x81]⟩, ⟨#[]⟩),
   (-2, -1, ⟨#[0x82]⟩, ⟨#[0x81]⟩),
   (-1, -2, ⟨#[0x82]⟩, ⟨#[0x81]⟩),
   (127, -128, ⟨#[0x80, 0x80]⟩, ⟨#[0x7f]⟩),
   (-128, 127, ⟨#[0x80, 0x80]⟩, ⟨#[0x7f]⟩),
   (128, -127, ⟨#[0xff]⟩, ⟨#[0x80, 0]⟩),
   (2147483647, -2147483647, ⟨#[0xff, 0xff, 0xff, 0xff]⟩,
     ⟨#[0xff, 0xff, 0xff, 0x7f]⟩),
   (-2147483647, 2147483647, ⟨#[0xff, 0xff, 0xff, 0xff]⟩,
     ⟨#[0xff, 0xff, 0xff, 0x7f]⟩)]

example : [false, true].all (fun minimal => numericFixtures.all fun (top, below, lo, hi) =>
    run [.op .OP_MIN] [scriptNum top, scriptNum below] minimal ==
      some (.success [lo] [] 17) &&
    run [.op .OP_MAX] [scriptNum top, scriptNum below] minimal ==
      some (.success [hi] [] 17)) = true := by
  native_decide

private def nonminimal : ByteArray := ⟨#[0x80]⟩
private def oversized : ByteArray := ⟨#[0, 0, 0, 0, 0]⟩
private def opaqueBytes : ByteArray := ⟨#[0xde, 0xad, 0xbe, 0xef, 0x00]⟩

private def nonMinimalZeros : List ByteArray :=
  [⟨#[0]⟩, ⟨#[0x80]⟩, ⟨#[0, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0, 0, 0, 0x80]⟩]

-- MIN/MAX canonicalize zero and negative zero when minimal encoding is optional.
example : numericOpcodes.all (fun opcode => nonMinimalZeros.all fun input =>
    ([[input, ⟨#[]⟩], [⟨#[]⟩, input], [input, input]] : List Stack).all fun stack =>
      run [.op opcode] stack false == some (.success [⟨#[]⟩] [] 17) &&
      run [.op opcode, .pushNum 1] stack true ==
        some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

-- The selected numeric value is encoded canonically even when both inputs use extra bytes.
example : numericOpcodes.all (fun opcode =>
    ([(⟨#[1, 0]⟩, ⟨#[1]⟩), (⟨#[1, 0x80]⟩, ⟨#[0x81]⟩)] :
      List (ByteArray × ByteArray)).all fun (raw, expected) =>
      run [.op opcode] [raw, raw] false == some (.success [expected] [] 17) &&
      run [.op opcode] [raw, raw] true == some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

private def oversizedNumbers : List ByteArray :=
  [oversized, ⟨#[0, 0, 0, 0x80, 0]⟩, ⟨#[0, 0, 0, 0x80, 0x80]⟩]

example : [false, true].all (fun minimal => numericOpcodes.all fun opcode =>
    oversizedNumbers.all fun raw =>
      ([[raw, ⟨#[]⟩], [⟨#[]⟩, raw]] : List Stack).all fun stack =>
        run [.op opcode, .pushNum 1] stack minimal ==
          some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- The lower numeric operand is decoded first, including when both inputs are malformed.
example : numericOpcodes.all (fun opcode =>
    run [.op opcode, .pushNum 1] [oversized, nonminimal] ==
      some (.failure .scriptNumNonMinimal) &&
    run [.op opcode, .pushNum 1] [nonminimal, oversized] ==
      some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- All four instructions require an index/value pair or two numbers before decoding.
example : [false, true].all (fun minimal => selectionOpcodes.all fun opcode =>
    ([[], [oversized], [nonminimal], [scriptNum (-1)], [scriptNum 0]] : List Stack).all
      fun stack => run [.op opcode, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- PICK copies and ROLL removes the selected value; all remaining values retain their order.
-- Selected and unselected bytes include oversized numbers, negative zero and empty data.
private def indexedFixtures : List (Opcode × Int × Stack) :=
  [(.OP_PICK, 0, [opaqueBytes, opaqueBytes, nonminimal, ByteArray.empty]),
   (.OP_PICK, 1, [nonminimal, opaqueBytes, nonminimal, ByteArray.empty]),
   (.OP_PICK, 2, [ByteArray.empty, opaqueBytes, nonminimal, ByteArray.empty]),
   (.OP_ROLL, 0, [opaqueBytes, nonminimal, ByteArray.empty]),
   (.OP_ROLL, 1, [nonminimal, opaqueBytes, ByteArray.empty]),
   (.OP_ROLL, 2, [ByteArray.empty, opaqueBytes, nonminimal])]

example : [false, true].all (fun minimal => indexedFixtures.all fun (opcode, index, expected) =>
    run [.op opcode] [scriptNum index, opaqueBytes, nonminimal, ByteArray.empty] minimal ==
      some (.success expected [] 17)) = true := by
  native_decide

-- Relaxed nonminimal index zero is decoded, while the selected bytes remain intact.
example : nonMinimalZeros.all (fun input =>
    run [.op .OP_PICK] [input, opaqueBytes] false == some (.success [opaqueBytes, opaqueBytes] [] 17) &&
    run [.op .OP_ROLL] [input, opaqueBytes] false == some (.success [opaqueBytes] [] 17) &&
    indexedOpcodes.all fun opcode => run [.op opcode] [input, opaqueBytes] true ==
      some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

-- A two-byte positive index reaches the last value without decoding intervening data.
example :
    run [.op .OP_PICK] (scriptNum 128 :: List.replicate 128 nonminimal ++ [opaqueBytes]) ==
      some (.success (opaqueBytes :: List.replicate 128 nonminimal ++ [opaqueBytes]) [] 17) ∧
    run [.op .OP_ROLL] (scriptNum 128 :: List.replicate 128 nonminimal ++ [opaqueBytes]) ==
      some (.success (opaqueBytes :: List.replicate 128 nonminimal) [] 17) := by
  native_decide

-- Negative indices and indices at or beyond the remaining depth fail after decoding.
-- Four-byte canonical indices pass numeric decoding and fail the range check.
example : [false, true].all (fun minimal => indexedOpcodes.all fun opcode =>
    ([-1, -2147483647, 3, 4, 2147483647] : List Int).all fun index =>
      run [.op opcode, .pushNum 1]
        [scriptNum index, opaqueBytes, nonminimal, ByteArray.empty] minimal ==
          some (.failure .stackUnderflow)) = true := by
  native_decide

example : [false, true].all (fun minimal => indexedOpcodes.all fun opcode =>
    oversizedNumbers.all fun index => run [.op opcode, .pushNum 1] [index, opaqueBytes] minimal ==
      some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- Nonminimal negative indices fail encoding first when MINIMALDATA is enabled.
example : indexedOpcodes.all (fun opcode =>
    run [.op opcode] [⟨#[1, 0x80]⟩, opaqueBytes] true ==
      some (.failure .scriptNumNonMinimal) &&
    run [.op opcode] [⟨#[1, 0x80]⟩, opaqueBytes] false ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

private def stateFixtures : List (Opcode × Stack × Stack) :=
  [(.OP_MIN, [scriptNum 2, scriptNum (-1)], [⟨#[0x81]⟩]),
   (.OP_MAX, [scriptNum 2, scriptNum (-1)], [⟨#[2]⟩]),
   (.OP_PICK, [scriptNum 1, opaqueBytes, nonminimal], [nonminimal, opaqueBytes, nonminimal]),
   (.OP_ROLL, [scriptNum 1, opaqueBytes, nonminimal], [nonminimal, opaqueBytes])]

-- Suffix execution and runtime execution preserve opaque tails, alternate data and weight.
example : stateFixtures.all (fun (opcode, stack, expected) =>
    run [.op opcode, .pushNum 7] (stack ++ [oversized]) true [opaqueBytes] 0 ==
      some (.success (scriptNum 7 :: expected ++ [oversized]) [opaqueBytes] 0)) = true := by
  native_decide

example : stateFixtures.all (fun (opcode, stack, expected) =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := stack ++ [oversized], altStack := [opaqueBytes],
          conditions := [true, true], weight := 0 } { minimalData := true } ctx with
    | .error _ => false
    | .ok next => next.stack == expected ++ [oversized] &&
        next.altStack == [opaqueBytes] && next.conditions == [true, true] && next.weight == 0) =
    true := by
  native_decide

-- Inactive branches skip numeric decoding, range checks and input arity checks.
example : selectionOpcodes.all (fun opcode =>
    ([[], [oversized], [oversized, nonminimal], [scriptNum (-1), opaqueBytes]] : List Stack).all
      fun stack => run [.pushNum 0, .op .OP_IF, .op opcode, .op .OP_ENDIF]
        stack true [opaqueBytes] 0 == some (.success stack [opaqueBytes] 0)) = true := by
  native_decide

example : selectionOpcodes.all (fun opcode =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := [oversized, nonminimal], altStack := [opaqueBytes],
          conditions := [true, false], weight := 0 } { minimalData := true } ctx with
    | .error _ => false
    | .ok next => next.stack == [oversized, nonminimal] &&
        next.altStack == [opaqueBytes] && next.conditions == [true, false] && next.weight == 0) =
    true := by
  native_decide

-- MIN/MAX and ROLL reduce the combined count by one before the runtime stack limit.
example : (numericOpcodes ++ [Opcode.OP_ROLL]).all (fun opcode =>
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 997 trueElement)
      true [opaqueBytes] ==
        some (.success (ByteArray.empty :: List.replicate 997 trueElement) [opaqueBytes] 17) &&
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 998 trueElement)
      true [opaqueBytes] ==
        some (.success (ByteArray.empty :: List.replicate 998 trueElement) [opaqueBytes] 17) &&
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 999 trueElement)
      true [opaqueBytes] == some (.failure .stackSize)) = true := by
  native_decide

-- PICK consumes its index and duplicates one value, preserving the combined count.
example :
    run [.op .OP_PICK] (ByteArray.empty :: opaqueBytes :: List.replicate 997 trueElement)
      true [nonminimal] ==
        some (.success (opaqueBytes :: opaqueBytes :: List.replicate 997 trueElement) [nonminimal] 17) ∧
    run [.op .OP_PICK] (ByteArray.empty :: opaqueBytes :: List.replicate 998 trueElement)
      true [nonminimal] == some (.failure .stackSize) := by
  native_decide

-- Active opcode errors precede the shared stack limit, including invalid indices.
example : numericOpcodes.all (fun opcode =>
    run [.op opcode] (oversized :: nonminimal :: List.replicate 999 trueElement)
      true [opaqueBytes] == some (.failure .scriptNumNonMinimal) &&
    run [.op opcode] (nonminimal :: oversized :: List.replicate 999 trueElement)
      true [opaqueBytes] == some (.failure .scriptNumOverflow)) = true := by
  native_decide

example : indexedOpcodes.all (fun opcode =>
    run [.op opcode] (oversized :: List.replicate 1000 trueElement)
      true [opaqueBytes] == some (.failure .scriptNumOverflow) &&
    run [.op opcode] (nonminimal :: List.replicate 1000 trueElement)
      true [opaqueBytes] == some (.failure .scriptNumNonMinimal) &&
    run [.op opcode] (scriptNum (-1) :: List.replicate 1000 trueElement)
      true [opaqueBytes] == some (.failure .stackUnderflow) &&
    run [.op opcode] (scriptNum 1000 :: List.replicate 1000 trueElement)
      true [opaqueBytes] == some (.failure .stackUnderflow)) = true := by
  native_decide

example : selectionOpcodes.all (fun opcode =>
    run [.op opcode] [oversized] true (List.replicate 1000 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

-- Skipped instructions still perform the shared combined-stack check.
example : selectionOpcodes.all (fun opcode =>
    evaluateRuntime oracle [.op opcode]
      { stack := List.replicate 1000 trueElement, altStack := [opaqueBytes],
        conditions := [false], weight := 17 } {} ctx == .failure .stackSize) = true := by
  native_decide

example : selectionOpcodes.all (fun opcode =>
    ScriptElement.stackGrowthAllowance (.op opcode) == 0) = true := by
  native_decide

end LeanMiniscript.Script
