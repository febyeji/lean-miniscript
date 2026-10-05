import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! Upgradeable NOP and RETURN regressions execute serialized scripts and retain
explicit expected errors, stack bytes and runtime fields. -/

private def ctx : TxContext :=
  { version := 2, locktime := 0, sequence := 0, sigHash := ByteArray.empty,
    sigVersion := .tapscript }

private def oracle : CryptoOracle := CryptoOracle.pureLeanHashes (fun _ _ _ => false)

private def nops : List Opcode :=
  [.OP_NOP1, .OP_NOP4, .OP_NOP5, .OP_NOP6, .OP_NOP7, .OP_NOP8, .OP_NOP9, .OP_NOP10]

private def opaqueBytes : ByteArray := ⟨#[0x80, 0, 0, 0, 0]⟩

private def run (script : Script) (stack : Stack := []) (discourage : Bool := false)
    (alt : Stack := []) (weight : Nat := 17) : Option WeightedResult := do
  let bytes ← (serializeScript script).toOption
  let decoded ← (deserializeScript bytes).toOption
  return evaluateWithRuntimeLimits oracle decoded stack alt
    { discourageUpgradableNops := discourage } ctx weight

private def byteFixtures : List (Opcode × UInt8) :=
  [(.OP_NOP1, 0xb0), (.OP_NOP4, 0xb3), (.OP_NOP5, 0xb4), (.OP_NOP6, 0xb5),
   (.OP_NOP7, 0xb6), (.OP_NOP8, 0xb7), (.OP_NOP9, 0xb8), (.OP_NOP10, 0xb9),
   (.OP_RETURN, 0x6a)]

example : byteFixtures.all (fun (opcode, byte) =>
    opcodeByte opcode == byte && (serializeScript [.op opcode]).toOption == some ⟨#[byte]⟩ &&
    match deserializeScript ⟨#[byte]⟩ with
    | .ok [.op actual] => actual == opcode
    | _ => false) = true := by
  native_decide

example : nops.all (fun opcode => opcode.isUpgradeableNop) = true := by
  native_decide

example : ([.OP_NOP, .OP_RETURN, .OP_CHECKLOCKTIMEVERIFY, .OP_CHECKSEQUENCEVERIFY] :
    List Opcode).all (fun opcode => !opcode.isUpgradeableNop) = true := by
  native_decide

example : ({} : ScriptFlags).discourageUpgradableNops = false := by rfl

-- Policy-disabled NOPs execute the suffix and preserve every byte and alternate item.
example : nops.all (fun opcode =>
    run [.op opcode, .pushNum 7] [opaqueBytes, ByteArray.empty] false [opaqueBytes] 0 ==
      some (.success [scriptNum 7, opaqueBytes, ByteArray.empty] [opaqueBytes] 0)) = true := by
  native_decide

-- The policy check needs no stack inputs and stops before suffix execution.
example : nops.all (fun opcode =>
    ([[], [opaqueBytes]] : List Stack).all fun stack =>
      run [.op opcode, .pushNum 1] stack true [opaqueBytes] 0 ==
        some (.failure .discourageUpgradableNops)) = true := by
  native_decide

-- Plain NOP accepts the same policy flag.
example : run [.op .OP_NOP, .pushNum 1] [opaqueBytes] true [opaqueBytes] 0 =
    some (.success [trueElement, opaqueBytes] [opaqueBytes] 0) := by
  native_decide

-- RETURN reports its error with an empty, true, false or nonnumeric stack.
example : [false, true].all (fun discourage =>
    ([[], [trueElement], [falseElement], [opaqueBytes]] : List Stack).all fun stack =>
      run [.op .OP_RETURN, .pushNum 1] stack discourage [opaqueBytes] 0 ==
        some (.failure .opReturn)) = true := by
  native_decide

-- Earlier executed failures determine the result.
example : nops.all (fun opcode =>
    run [.op .OP_RETURN, .op opcode] [] true == some (.failure .opReturn) &&
    run [.op opcode, .op .OP_RETURN] [] true == some (.failure .discourageUpgradableNops) &&
    run [.pushNum 0, .op .OP_VERIFY, .op opcode] [] true == some (.failure .verify) &&
    run [.op opcode, .op .OP_RETURN] [] false == some (.failure .opReturn)) = true := by
  native_decide

example : nops.all (fun opcode =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := [opaqueBytes], altStack := [opaqueBytes],
          conditions := [true, true], weight := 0 } {} ctx with
    | .error _ => false
    | .ok next => next.stack == [opaqueBytes] && next.altStack == [opaqueBytes] &&
        next.conditions == [true, true] && next.weight == 0) = true := by
  native_decide

-- Inactive branches skip upgradeable NOP policy and RETURN.
example : (nops ++ [Opcode.OP_RETURN]).all (fun opcode =>
    run [.pushNum 0, .op .OP_IF, .op opcode, .op .OP_ENDIF]
      [opaqueBytes] true [opaqueBytes] 0 == some (.success [opaqueBytes] [opaqueBytes] 0)) =
    true := by
  native_decide

example : (nops ++ [Opcode.OP_RETURN]).all (fun opcode =>
    match executeRuntimeElement oracle (.op opcode)
        { stack := [opaqueBytes], altStack := [opaqueBytes],
          conditions := [true, false], weight := 0 }
        { discourageUpgradableNops := true } ctx with
    | .error _ => false
    | .ok next => next.stack == [opaqueBytes] && next.altStack == [opaqueBytes] &&
        next.conditions == [true, false] && next.weight == 0) = true := by
  native_decide

-- Successful NOPs preserve the count at the combined-stack boundary.
example : nops.all (fun opcode =>
    run [.op opcode] (List.replicate 999 trueElement) false [opaqueBytes] ==
      some (.success (List.replicate 999 trueElement) [opaqueBytes] 17) &&
    run [.op opcode] (List.replicate 1000 trueElement) false [opaqueBytes] ==
      some (.failure .stackSize)) = true := by
  native_decide

-- Active policy and RETURN failures take precedence over the shared stack limit.
example : nops.all (fun opcode =>
    run [.op opcode] (List.replicate 1000 trueElement) true [opaqueBytes] ==
      some (.failure .discourageUpgradableNops)) = true := by
  native_decide

example : run [.op .OP_RETURN] (List.replicate 1000 trueElement) false [opaqueBytes] =
    some (.failure .opReturn) := by
  native_decide

-- Skipped instructions still check the combined stack limit.
example : (nops ++ [Opcode.OP_RETURN]).all (fun opcode =>
    evaluateRuntime oracle [.op opcode]
      { stack := List.replicate 1000 trueElement, altStack := [opaqueBytes],
        conditions := [false], weight := 17 }
      { discourageUpgradableNops := true } ctx == .failure .stackSize) = true := by
  native_decide

example : (nops ++ [Opcode.OP_RETURN]).all (fun opcode =>
    ScriptElement.stackGrowthAllowance (.op opcode) == 0 &&
      opcode.fixedMainStackInputs? == some 0) = true := by
  native_decide

end LeanMiniscript.Script
