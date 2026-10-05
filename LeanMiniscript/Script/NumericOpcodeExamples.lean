import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! Arithmetic and comparison regressions serialize and deserialize scripts before
runtime execution. Expected output bytes are pinned independently of the evaluator. -/

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

private def unaryOpcodes : List Opcode :=
  [.OP_1ADD, .OP_1SUB, .OP_NEGATE, .OP_ABS]

private def binaryOpcodes : List Opcode :=
  [.OP_SUB, .OP_NUMNOTEQUAL, .OP_LESSTHAN, .OP_GREATERTHAN,
   .OP_LESSTHANOREQUAL, .OP_GREATERTHANOREQUAL]

-- Zero, signs, sign-bit transitions, and both four-byte signed-magnitude endpoints.
private def unaryFixtures : List (Opcode × Int × ByteArray) :=
  [(.OP_1ADD, 0, ⟨#[0x01]⟩),
   (.OP_1ADD, 1, ⟨#[0x02]⟩),
   (.OP_1ADD, -1, ⟨#[]⟩),
   (.OP_1ADD, 127, ⟨#[0x80, 0x00]⟩),
   (.OP_1ADD, -127, ⟨#[0xfe]⟩),
   (.OP_1ADD, 128, ⟨#[0x81, 0x00]⟩),
   (.OP_1ADD, -128, ⟨#[0xff]⟩),
   (.OP_1ADD, 2147483647, ⟨#[0x00, 0x00, 0x00, 0x80, 0x00]⟩),
   (.OP_1ADD, -2147483647, ⟨#[0xfe, 0xff, 0xff, 0xff]⟩),
   (.OP_1SUB, 0, ⟨#[0x81]⟩),
   (.OP_1SUB, 1, ⟨#[]⟩),
   (.OP_1SUB, -1, ⟨#[0x82]⟩),
   (.OP_1SUB, 127, ⟨#[0x7e]⟩),
   (.OP_1SUB, -127, ⟨#[0x80, 0x80]⟩),
   (.OP_1SUB, 128, ⟨#[0x7f]⟩),
   (.OP_1SUB, -128, ⟨#[0x81, 0x80]⟩),
   (.OP_1SUB, 2147483647, ⟨#[0xfe, 0xff, 0xff, 0x7f]⟩),
   (.OP_1SUB, -2147483647, ⟨#[0x00, 0x00, 0x00, 0x80, 0x80]⟩),
   (.OP_NEGATE, 0, ⟨#[]⟩),
   (.OP_NEGATE, 1, ⟨#[0x81]⟩),
   (.OP_NEGATE, -1, ⟨#[0x01]⟩),
   (.OP_NEGATE, 127, ⟨#[0xff]⟩),
   (.OP_NEGATE, -127, ⟨#[0x7f]⟩),
   (.OP_NEGATE, 128, ⟨#[0x80, 0x80]⟩),
   (.OP_NEGATE, -128, ⟨#[0x80, 0x00]⟩),
   (.OP_NEGATE, 2147483647, ⟨#[0xff, 0xff, 0xff, 0xff]⟩),
   (.OP_NEGATE, -2147483647, ⟨#[0xff, 0xff, 0xff, 0x7f]⟩),
   (.OP_ABS, 0, ⟨#[]⟩),
   (.OP_ABS, 1, ⟨#[0x01]⟩),
   (.OP_ABS, -1, ⟨#[0x01]⟩),
   (.OP_ABS, 127, ⟨#[0x7f]⟩),
   (.OP_ABS, -127, ⟨#[0x7f]⟩),
   (.OP_ABS, 128, ⟨#[0x80, 0x00]⟩),
   (.OP_ABS, -128, ⟨#[0x80, 0x00]⟩),
   (.OP_ABS, 2147483647, ⟨#[0xff, 0xff, 0xff, 0x7f]⟩),
   (.OP_ABS, -2147483647, ⟨#[0xff, 0xff, 0xff, 0x7f]⟩)]

example : [false, true].all (fun minimal => unaryFixtures.all fun (opcode, input, expected) =>
    run [.op opcode] [scriptNum input] minimal == some (.success [expected] [] 17)) = true := by
  native_decide

-- Operands are top-first: SUB computes below - top; ordered comparisons use below first.
private def binaryFixtures : List (Opcode × Int × Int × ByteArray) :=
  [(.OP_SUB, 0, 0, ⟨#[]⟩),
   (.OP_SUB, 1, 1, ⟨#[]⟩),
   (.OP_SUB, 2, 1, ⟨#[0x81]⟩),
   (.OP_SUB, 1, 2, ⟨#[0x01]⟩),
   (.OP_SUB, 1, -1, ⟨#[0x82]⟩),
   (.OP_SUB, -1, 1, ⟨#[0x02]⟩),
   (.OP_SUB, -2, -1, ⟨#[0x01]⟩),
   (.OP_SUB, -1, -2, ⟨#[0x81]⟩),
   (.OP_SUB, 2147483647, -2147483647, ⟨#[0xfe, 0xff, 0xff, 0xff, 0x80]⟩),
   (.OP_SUB, -2147483647, 2147483647, ⟨#[0xfe, 0xff, 0xff, 0xff, 0x00]⟩),
   (.OP_NUMNOTEQUAL, 0, 0, ⟨#[]⟩),
   (.OP_NUMNOTEQUAL, 1, 1, ⟨#[]⟩),
   (.OP_NUMNOTEQUAL, 2, 1, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, 1, 2, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, 1, -1, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, -1, 1, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, -2, -1, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, -1, -2, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, 2147483647, -2147483647, ⟨#[0x01]⟩),
   (.OP_NUMNOTEQUAL, -2147483647, 2147483647, ⟨#[0x01]⟩),
   (.OP_LESSTHAN, 0, 0, ⟨#[]⟩),
   (.OP_LESSTHAN, 1, 1, ⟨#[]⟩),
   (.OP_LESSTHAN, 2, 1, ⟨#[0x01]⟩),
   (.OP_LESSTHAN, 1, 2, ⟨#[]⟩),
   (.OP_LESSTHAN, 1, -1, ⟨#[0x01]⟩),
   (.OP_LESSTHAN, -1, 1, ⟨#[]⟩),
   (.OP_LESSTHAN, -2, -1, ⟨#[]⟩),
   (.OP_LESSTHAN, -1, -2, ⟨#[0x01]⟩),
   (.OP_LESSTHAN, 2147483647, -2147483647, ⟨#[0x01]⟩),
   (.OP_LESSTHAN, -2147483647, 2147483647, ⟨#[]⟩),
   (.OP_GREATERTHAN, 0, 0, ⟨#[]⟩),
   (.OP_GREATERTHAN, 1, 1, ⟨#[]⟩),
   (.OP_GREATERTHAN, 2, 1, ⟨#[]⟩),
   (.OP_GREATERTHAN, 1, 2, ⟨#[0x01]⟩),
   (.OP_GREATERTHAN, 1, -1, ⟨#[]⟩),
   (.OP_GREATERTHAN, -1, 1, ⟨#[0x01]⟩),
   (.OP_GREATERTHAN, -2, -1, ⟨#[0x01]⟩),
   (.OP_GREATERTHAN, -1, -2, ⟨#[]⟩),
   (.OP_GREATERTHAN, 2147483647, -2147483647, ⟨#[]⟩),
   (.OP_GREATERTHAN, -2147483647, 2147483647, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, 0, 0, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, 1, 1, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, 2, 1, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, 1, 2, ⟨#[]⟩),
   (.OP_LESSTHANOREQUAL, 1, -1, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, -1, 1, ⟨#[]⟩),
   (.OP_LESSTHANOREQUAL, -2, -1, ⟨#[]⟩),
   (.OP_LESSTHANOREQUAL, -1, -2, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, 2147483647, -2147483647, ⟨#[0x01]⟩),
   (.OP_LESSTHANOREQUAL, -2147483647, 2147483647, ⟨#[]⟩),
   (.OP_GREATERTHANOREQUAL, 0, 0, ⟨#[0x01]⟩),
   (.OP_GREATERTHANOREQUAL, 1, 1, ⟨#[0x01]⟩),
   (.OP_GREATERTHANOREQUAL, 2, 1, ⟨#[]⟩),
   (.OP_GREATERTHANOREQUAL, 1, 2, ⟨#[0x01]⟩),
   (.OP_GREATERTHANOREQUAL, 1, -1, ⟨#[]⟩),
   (.OP_GREATERTHANOREQUAL, -1, 1, ⟨#[0x01]⟩),
   (.OP_GREATERTHANOREQUAL, -2, -1, ⟨#[0x01]⟩),
   (.OP_GREATERTHANOREQUAL, -1, -2, ⟨#[]⟩),
   (.OP_GREATERTHANOREQUAL, 2147483647, -2147483647, ⟨#[]⟩),
   (.OP_GREATERTHANOREQUAL, -2147483647, 2147483647, ⟨#[0x01]⟩)]

example : [false, true].all (fun minimal => binaryFixtures.all fun (opcode, top, below, expected) =>
    run [.op opcode] [scriptNum top, scriptNum below] minimal ==
      some (.success [expected] [] 17)) = true := by
  native_decide

private def nonMinimalZeros : List ByteArray :=
  [⟨#[0]⟩, ⟨#[0x80]⟩, ⟨#[0, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0, 0, 0, 0x80]⟩]

private def nonMinimalOnes : List (ByteArray × Int) :=
  [(⟨#[1, 0]⟩, 1), (⟨#[1, 0x80]⟩, -1)]

private def unaryZeroResults : List (Opcode × ByteArray) :=
  [(.OP_1ADD, ⟨#[1]⟩), (.OP_1SUB, ⟨#[0x81]⟩),
   (.OP_NEGATE, ⟨#[]⟩), (.OP_ABS, ⟨#[]⟩)]

private def binaryZeroResults : List (Opcode × ByteArray) :=
  [(.OP_SUB, ⟨#[]⟩), (.OP_NUMNOTEQUAL, ⟨#[]⟩), (.OP_LESSTHAN, ⟨#[]⟩),
   (.OP_GREATERTHAN, ⟨#[]⟩), (.OP_LESSTHANOREQUAL, ⟨#[1]⟩),
   (.OP_GREATERTHANOREQUAL, ⟨#[1]⟩)]

-- Relaxed zero and negative-zero decoding always produces canonical result bytes.
example : unaryZeroResults.all (fun (opcode, expected) => nonMinimalZeros.all fun input =>
    run [.op opcode] [input] false == some (.success [expected] [] 17) &&
    run [.op opcode, .op .OP_DROP, .pushNum 1] [input] true ==
      some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

example : binaryZeroResults.all (fun (opcode, expected) => nonMinimalZeros.all fun input =>
    ([[input, ⟨#[]⟩], [⟨#[]⟩, input]] : List Stack).all fun stack =>
      run [.op opcode] stack false == some (.success [expected] [] 17) &&
      run [.op opcode, .op .OP_DROP, .pushNum 1] stack true ==
        some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

-- Non-minimal ±1 uses the same independently pinned expectations as canonical inputs.
example : unaryFixtures.all (fun (opcode, input, expected) =>
    nonMinimalOnes.all fun (raw, value) => input != value ||
      (run [.op opcode] [raw] false == some (.success [expected] [] 17) &&
       run [.op opcode] [raw] true == some (.failure .scriptNumNonMinimal))) = true := by
  native_decide

example : binaryFixtures.all (fun (opcode, top, below, expected) =>
    nonMinimalOnes.all fun (raw, value) =>
      (top != value ||
        (run [.op opcode] [raw, scriptNum below] false == some (.success [expected] [] 17) &&
         run [.op opcode] [raw, scriptNum below] true ==
           some (.failure .scriptNumNonMinimal))) &&
      (below != value ||
        (run [.op opcode] [scriptNum top, raw] false == some (.success [expected] [] 17) &&
         run [.op opcode] [scriptNum top, raw] true ==
           some (.failure .scriptNumNonMinimal)))) = true := by
  native_decide

private def oversizedFixtures : List ByteArray :=
  [⟨#[0, 0, 0, 0x80, 0]⟩, ⟨#[0, 0, 0, 0x80, 0x80]⟩,
   ⟨#[0, 0, 0, 0, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩]

-- Size errors precede minimal encoding errors for every operand and both flag settings.
example : [false, true].all (fun minimal => oversizedFixtures.all fun raw =>
    unaryOpcodes.all fun opcode =>
      run [.op opcode, .op .OP_DROP, .pushNum 1] [raw] minimal ==
        some (.failure .scriptNumOverflow)) = true := by
  native_decide

example : [false, true].all (fun minimal => oversizedFixtures.all fun raw =>
    binaryOpcodes.all fun opcode =>
      ([[raw, ⟨#[]⟩], [⟨#[]⟩, raw]] : List Stack).all fun stack =>
        run [.op opcode, .op .OP_DROP, .pushNum 1] stack minimal ==
          some (.failure .scriptNumOverflow)) = true := by
  native_decide

private def nonminimal : ByteArray := ⟨#[0x80]⟩
private def oversized : ByteArray := ⟨#[0, 0, 0, 0, 0]⟩

-- Binary instructions decode the lower operand before the top operand.
example : binaryOpcodes.all (fun opcode =>
    run [.op opcode, .pushNum 1] [oversized, nonminimal] ==
      some (.failure .scriptNumNonMinimal) &&
    run [.op opcode, .pushNum 1] [nonminimal, oversized] ==
      some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- Input arity is checked before decoding any available operand or executing a suffix.
example : [false, true].all (fun minimal => unaryOpcodes.all fun opcode =>
    run [.op opcode, .pushNum 1] [] minimal [trueElement] ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

example : [false, true].all (fun minimal => binaryOpcodes.all fun opcode =>
    ([[], [oversized], [nonminimal]] : List Stack).all fun stack =>
      run [.op opcode, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- Four-byte inputs may produce five-byte results, which EQUAL accepts as bytes.
private def wideResultFixtures : List (Opcode × Stack × ByteArray) :=
  [(.OP_1ADD, [⟨#[0xff, 0xff, 0xff, 0x7f]⟩], ⟨#[0, 0, 0, 0x80, 0]⟩),
   (.OP_1SUB, [⟨#[0xff, 0xff, 0xff, 0xff]⟩], ⟨#[0, 0, 0, 0x80, 0x80]⟩),
   (.OP_SUB, [⟨#[0xff, 0xff, 0xff, 0xff]⟩, ⟨#[0xff, 0xff, 0xff, 0x7f]⟩],
     ⟨#[0xfe, 0xff, 0xff, 0xff, 0]⟩),
   (.OP_SUB, [⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩],
     ⟨#[0xfe, 0xff, 0xff, 0xff, 0x80]⟩)]

example : wideResultFixtures.all (fun (opcode, stack, expected) =>
    run [.op opcode, .pushData expected, .op .OP_EQUAL] stack ==
      some (.success [⟨#[1]⟩] [] 17) &&
    run [.op opcode, .op .OP_NOT, .pushNum 1] stack ==
      some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- Representative successful operations pin suffix execution and every preserved field.
private def stateFixtures : List (Opcode × Stack × ByteArray) :=
  [(.OP_1ADD, [⟨#[1]⟩], ⟨#[2]⟩), (.OP_1SUB, [⟨#[1]⟩], ⟨#[]⟩),
   (.OP_NEGATE, [⟨#[1]⟩], ⟨#[0x81]⟩), (.OP_ABS, [⟨#[0x81]⟩], ⟨#[1]⟩),
   (.OP_SUB, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[0x81]⟩),
   (.OP_NUMNOTEQUAL, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[1]⟩),
   (.OP_LESSTHAN, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[1]⟩),
   (.OP_GREATERTHAN, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[]⟩),
   (.OP_LESSTHANOREQUAL, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[1]⟩),
   (.OP_GREATERTHANOREQUAL, [⟨#[2]⟩, ⟨#[1]⟩], ⟨#[]⟩)]

example : stateFixtures.all (fun (opcode, stack, expected) =>
    run [.op opcode, .pushNum 7] (stack ++ [nonminimal, scriptNum 9])
      true [scriptNum 4] 0 ==
        some (.success [scriptNum 7, expected, nonminimal, scriptNum 9] [scriptNum 4] 0)) =
    true := by
  native_decide

example : stateFixtures.all (fun (opcode, stack, expected) =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := stack ++ [nonminimal], altStack := [scriptNum 4],
          conditions := [true, true], weight := 0 } { minimalData := true } ctx with
    | .error _ => false
    | .ok next => next.stack == [expected, nonminimal] &&
        next.altStack == [scriptNum 4] && next.conditions == [true, true] && next.weight == 0) =
    true := by
  native_decide

-- Inactive execution skips missing inputs and malformed numeric bytes.
example : (unaryOpcodes ++ binaryOpcodes).all (fun opcode =>
    ([[], [oversized], [oversized, nonminimal]] : List Stack).all fun stack =>
      run [.pushNum 0, .op .OP_IF, .op opcode, .op .OP_ENDIF]
        stack true [scriptNum 4] 0 == some (.success stack [scriptNum 4] 0)) = true := by
  native_decide

example : (unaryOpcodes ++ binaryOpcodes).all (fun opcode =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := [oversized, nonminimal], altStack := [scriptNum 4],
          conditions := [true, false], weight := 0 } { minimalData := true } ctx with
    | .error _ => false
    | .ok next => next.stack == [oversized, nonminimal] &&
        next.altStack == [scriptNum 4] && next.conditions == [true, false] && next.weight == 0) =
    true := by
  native_decide

-- Unary arithmetic keeps the combined stack count at the 1000-item boundary.
example : unaryZeroResults.all (fun (opcode, expected) =>
    run [.op opcode] (ByteArray.empty :: List.replicate 998 trueElement)
      true [scriptNum 4] ==
        some (.success (expected :: List.replicate 998 trueElement) [scriptNum 4] 17) &&
    run [.op opcode] (ByteArray.empty :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .stackSize)) = true := by
  native_decide

-- Binary operations shrink by one: an initial combined 1001 items becomes 1000.
example : binaryZeroResults.all (fun (opcode, expected) =>
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 997 trueElement)
      true [scriptNum 4] ==
        some (.success (expected :: List.replicate 997 trueElement) [scriptNum 4] 17) &&
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 998 trueElement)
      true [scriptNum 4] ==
        some (.success (expected :: List.replicate 998 trueElement) [scriptNum 4] 17) &&
    run [.op opcode] (ByteArray.empty :: ByteArray.empty :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .stackSize)) = true := by
  native_decide

-- Numeric errors take precedence over the post-instruction combined-stack limit.
example : unaryOpcodes.all (fun opcode =>
    run [.op opcode] (oversized :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .scriptNumOverflow) &&
    run [.op opcode] (nonminimal :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .scriptNumNonMinimal)) = true := by
  native_decide

example : binaryOpcodes.all (fun opcode =>
    run [.op opcode] (oversized :: nonminimal :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .scriptNumNonMinimal) &&
    run [.op opcode] (nonminimal :: oversized :: List.replicate 999 trueElement)
      true [scriptNum 4] == some (.failure .scriptNumOverflow)) = true := by
  native_decide

-- Skipped instructions still perform the shared combined-stack check.
example : (unaryOpcodes ++ binaryOpcodes).all (fun opcode =>
    evaluateRuntime oracle [.op opcode]
      { stack := List.replicate 1000 trueElement, altStack := [trueElement],
        conditions := [false], weight := 17 } {} ctx == .failure .stackSize) = true := by
  native_decide

example : (unaryOpcodes ++ binaryOpcodes).all (fun opcode =>
    ScriptElement.stackGrowthAllowance (.op opcode) == 0) = true := by
  native_decide

end LeanMiniscript.Script
