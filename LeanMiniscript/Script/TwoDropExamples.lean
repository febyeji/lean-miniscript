import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! 2DROP regressions pass through the codec before runtime execution.
The remaining main stack and alternate stack retain their exact bytes. -/

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
  [([⟨#[0xaa]⟩, ⟨#[0xbb]⟩], []),
   ([⟨#[]⟩, ⟨#[]⟩], []),
   ([⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩], []),
   ([⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩],
    [⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩]),
   ([⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩, ⟨#[0xcc]⟩],
    [⟨#[0xcc]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩],
    [⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩]),
   ([⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩], [⟨#[0xbb]⟩])]

-- No ScriptNum decoding is performed on either discarded input.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_2DROP] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- The alternate stack and suffix cannot supply a missing main-stack input.
example : [false, true].all (fun minimal =>
    ([[], [⟨#[]⟩], [⟨#[1, 0, 0, 0, 0]⟩]] : List Stack).all fun stack =>
      run [.op .OP_2DROP, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

example : run [.op .OP_2DROP, .op .OP_SWAP]
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0x80]⟩] true [⟨#[0xdd]⟩] 0 =
    some (.success [⟨#[0x80]⟩, ⟨#[0xcc]⟩] [⟨#[0xdd]⟩] 0) := by
  native_decide

example : run [.op .OP_2DROP, .op .OP_VERIFY, .pushNum 1]
    [trueElement, trueElement, ByteArray.empty] = some (.failure .verify) := by
  native_decide

example : run [.op .OP_2DROP, .op .OP_VERIFY, .pushNum 1]
    [trueElement, trueElement] = some (.failure .stackUnderflow) := by
  native_decide

example : ([[], [⟨#[0x80]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]] : List Stack).all
    (fun stack => run [.pushNum 0, .op .OP_IF, .op .OP_2DROP, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2DROP)
    { stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, true], weight := 0 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0xcc]⟩], [⟨#[0xdd]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2DROP)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0xdd]⟩], [true, false, true], 17) := by
  native_decide

-- The low-level entry checks the combined count after both removals.
-- Full-witness entry checks the initial witness bounds separately.
example : run [.op .OP_2DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 1000 ByteArray.empty) =
    some (.success (List.replicate 1000 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_2DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 999 ByteArray.empty)
    true [⟨#[0xdd]⟩] =
    some (.success (List.replicate 999 ByteArray.empty) [⟨#[0xdd]⟩] 17) := by
  native_decide

-- Two separate DROP instructions check the intermediate 1001-item stack.
example : run [.op .OP_DROP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 1000 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

-- At a valid 1000-item input, the result has 998 items.
example : run [.op .OP_2DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 998 ByteArray.empty) =
    some (.success (List.replicate 998 ByteArray.empty) [] 17) := by
  native_decide

-- An oversized result fails before the suffix can remove another item.
example : run [.op .OP_2DROP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 1001 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_2DROP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 1000 ByteArray.empty)
    true [⟨#[0xdd]⟩] = some (.failure .stackSize) := by
  native_decide

example : ([[], [trueElement]] : List Stack).all (fun stack =>
    run [.op .OP_2DROP, .pushNum 1] stack true (List.replicate 1001 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2DROP, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2DROP, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_2DROP) = 0 := rfl
example : OneItemGrowth [.op .OP_2DROP] := by
  simp [ScriptElement.stackGrowthAllowance]
example : serializeScript [.op .OP_2DROP] = .ok ⟨#[0x6d]⟩ := rfl
example : deserializeScript ⟨#[0x6d]⟩ = .ok [.op .OP_2DROP] := by
  exact deserializeScript_serializeScript_of_normalized
    [.op .OP_2DROP] ⟨#[0x6d]⟩ (by rfl) (by rfl)

end LeanMiniscript.Script
