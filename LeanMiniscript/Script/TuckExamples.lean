import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! TUCK regressions pass through serialization and deserialization before
runtime execution. Expected stacks specify insertion order and raw bytes. -/

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
  [([⟨#[0xaa]⟩, ⟨#[0xbb]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩]),
   ([⟨#[]⟩, ⟨#[0xbb]⟩], [⟨#[]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[]⟩], [⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[0xaa]⟩]),
   ([⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩],
    [⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩]),
   ([⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩],
    [⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩],
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xcc]⟩]),
   ([⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩],
    [⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[1, 0]⟩, ⟨#[0xbb]⟩])]

-- Neither input is decoded as a number under either minimalData setting.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_TUCK] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

example : [false, true].all (fun minimal =>
    ([[], [⟨#[]⟩], [⟨#[1, 0, 0, 0, 0]⟩]] : List Stack).all fun stack =>
      run [.op .OP_TUCK, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- The original top moves to the alt stack; its inserted copy remains below.
example : run [.op .OP_TUCK, .op .OP_TOALTSTACK]
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩] true [⟨#[0xdd]⟩] 0 =
    some (.success [⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xcc]⟩] [⟨#[0xaa]⟩, ⟨#[0xdd]⟩] 0) := by
  native_decide

example : run [.op .OP_TUCK, .op .OP_VERIFY, .pushNum 1]
    [ByteArray.empty, trueElement] = some (.failure .verify) := by
  native_decide

example : ([[], [⟨#[0x80]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]] : List Stack).all
    (fun stack => run [.pushNum 0, .op .OP_IF, .op .OP_TUCK, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_TUCK)
    { stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, true], weight := 0 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xcc]⟩], [⟨#[0xdd]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_TUCK)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0xdd]⟩], [true, false, true], 17) := by
  native_decide

-- Combined stack size 999 grows to exactly 1000, including alt-stack items.
example : run [.op .OP_TUCK]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 997 ByteArray.empty) =
    some (.success (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xaa]⟩ ::
      List.replicate 997 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_TUCK]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 996 ByteArray.empty)
    true [⟨#[0xdd]⟩] =
    some (.success (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xaa]⟩ ::
      List.replicate 996 ByteArray.empty) [⟨#[0xdd]⟩] 17) := by
  native_decide

-- A suffix DROP cannot rescue the intermediate 1001-item failure.
example : run [.op .OP_TUCK, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 998 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_TUCK, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 997 ByteArray.empty)
    true [⟨#[0xdd]⟩] = some (.failure .stackSize) := by
  native_decide

-- Underflow is checked before the oversized alternate stack.
example : ([[], [trueElement]] : List Stack).all (fun stack =>
    run [.op .OP_TUCK, .pushNum 1] stack true (List.replicate 1001 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_TUCK, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

-- Inactive instructions retain the shared stack-size check.
example : evaluateRuntime oracle [.op .OP_TUCK, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_TUCK) = 1 := rfl
example : OneItemGrowth [.op .OP_TUCK] := by
  simp [ScriptElement.stackGrowthAllowance]
example : serializeScript [.op .OP_TUCK] = .ok ⟨#[0x7d]⟩ := rfl
example : deserializeScript ⟨#[0x7d]⟩ = .ok [.op .OP_TUCK] := by
  exact deserializeScript_serializeScript_of_normalized
    [.op .OP_TUCK] ⟨#[0x7d]⟩ (by rfl) (by rfl)

end LeanMiniscript.Script
