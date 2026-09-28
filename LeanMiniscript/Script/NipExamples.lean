import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! NIP regressions serialize and deserialize each script before runtime
execution. Expected stacks retain raw bytes, including non-minimal numbers. -/

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

private def byteFixtures : List (Stack × Stack) :=
  [([⟨#[0xaa]⟩, ⟨#[0xbb]⟩], [⟨#[0xaa]⟩]),
   ([⟨#[]⟩, ⟨#[0xbb]⟩], [⟨#[]⟩]),
   ([⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩], [⟨#[0x80]⟩]),
   ([⟨#[1, 0, 0, 0, 0]⟩, ⟨#[]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩],
    [⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], [⟨#[0xaa]⟩, ⟨#[0xcc]⟩]),
   ([⟨#[]⟩, ⟨#[]⟩, ⟨#[0x80]⟩], [⟨#[]⟩, ⟨#[0x80]⟩]),
   ([⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩], [⟨#[1, 0]⟩, ⟨#[0xbb]⟩])]

-- NIP preserves the exact top and lower bytes under both minimalData settings.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_NIP] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Neither an alt-stack item nor a suffix push can supply NIP's missing input.
example : [false, true].all (fun minimal =>
    ([[], [⟨#[]⟩], [⟨#[1, 0, 0, 0, 0]⟩]] : List Stack).all fun stack =>
      run [.op .OP_NIP, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

example : run [.op .OP_NIP, .op .OP_SWAP]
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0x80]⟩] true [⟨#[0xdd]⟩] 0 =
    some (.success [⟨#[0xcc]⟩, ⟨#[0xaa]⟩, ⟨#[0x80]⟩] [⟨#[0xdd]⟩] 0) := by
  native_decide

example : run [.op .OP_NIP, .op .OP_VERIFY, .pushNum 1]
    [ByteArray.empty, trueElement] = some (.failure .verify) := by
  native_decide

-- Source-order inactive execution skips underflow and keeps every stack byte.
example : ([[], [⟨#[0x80]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]] : List Stack).all
    (fun stack => run [.pushNum 0, .op .OP_IF, .op .OP_NIP, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

-- Observe condition-stack and budget preservation at the individual step.
example : ((runtimeStep oracle (.op .OP_NIP)
    { stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, true], weight := 0 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0xaa]⟩, ⟨#[0xcc]⟩], [⟨#[0xdd]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_NIP)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0xdd]⟩], [true, false, true], 17) := by
  native_decide

-- The low-level runtime checks the stack after NIP reduces its count by one.
-- Initial witness bounds are checked separately by the full-witness entry.
example : run [.op .OP_NIP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 999 ByteArray.empty) =
    some (.success (⟨#[0xaa]⟩ :: List.replicate 999 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_NIP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 998 ByteArray.empty)
    true [⟨#[0xdd]⟩] =
    some (.success (⟨#[0xaa]⟩ :: List.replicate 998 ByteArray.empty) [⟨#[0xdd]⟩] 17) := by
  native_decide

-- A suffix cannot repair an oversized result; underflow is checked earlier.
example : run [.op .OP_NIP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 999 ByteArray.empty)
    true [⟨#[0xdd]⟩] = some (.failure .stackSize) := by
  native_decide

example : ([[], [trueElement]] : List Stack).all (fun stack =>
    run [.op .OP_NIP, .pushNum 1] stack true (List.replicate 1001 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

-- Inactive NIP keeps the stack but still enforces the combined limit.
example : evaluateRuntime oracle [.op .OP_NIP]
    { stack := List.replicate 1000 trueElement, altStack := [trueElement],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_NIP) = 0 := rfl

end LeanMiniscript.Script
