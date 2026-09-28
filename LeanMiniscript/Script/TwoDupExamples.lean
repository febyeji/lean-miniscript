import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.RuntimeStackBounds

namespace LeanMiniscript.Script

/-! 2DUP regressions serialize and deserialize scripts before runtime execution.
The expected stacks use top-first order and retain the original raw bytes. -/

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
  [([⟨#[0xaa]⟩, ⟨#[0xbb]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩]),
   ([⟨#[]⟩, ⟨#[0xbb]⟩], [⟨#[]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩, ⟨#[0xbb]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[]⟩], [⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[0xaa]⟩, ⟨#[]⟩]),
   ([⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩],
    [⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩]),
   ([⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩],
    [⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩],
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩])]

example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_2DUP] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Underflow terminates before a suffix push, regardless of the item's encoding.
example : [false, true].all (fun minimal =>
    ([[], [⟨#[]⟩], [⟨#[1, 0, 0, 0, 0]⟩]] : List Stack).all fun stack =>
      run [.op .OP_2DUP, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- Moving both copies to the alternate stack exposes the unchanged original.
example : run [.op .OP_2DUP, .op .OP_TOALTSTACK, .op .OP_TOALTSTACK]
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩] true [⟨#[0xdd]⟩] 0 =
    some (.success [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]
      [⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xdd]⟩] 0) := by
  native_decide

example : run [.op .OP_2DUP, .op .OP_VERIFY, .pushNum 1]
    [ByteArray.empty, trueElement] = some (.failure .verify) := by
  native_decide

example : ([[], [⟨#[0x80]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩],
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]] : List Stack).all
    (fun stack => run [.pushNum 0, .op .OP_IF, .op .OP_2DUP, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2DUP)
    { stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, true], weight := 0 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩],
      [⟨#[0xdd]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2DUP)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0xdd]⟩], [true, false, true], 17) := by
  native_decide

-- Active execution grows 998 combined items to the allowed limit of 1000.
example : run [.op .OP_2DUP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 996 ByteArray.empty) =
    some (.success (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ ::
      List.replicate 996 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_2DUP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate 995 ByteArray.empty)
    true [⟨#[0xdd]⟩] =
    some (.success (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ ::
      List.replicate 995 ByteArray.empty) [⟨#[0xdd]⟩] 17) := by
  native_decide

-- Starting at 999 or 1000 fails after copying, before a suffix DROP.
example : [997, 998].all (fun count => run [.op .OP_2DUP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate count ByteArray.empty) ==
    some (.failure .stackSize)) = true := by
  native_decide

example : [996, 997].all (fun count => run [.op .OP_2DUP, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: List.replicate count ByteArray.empty)
    true [⟨#[0xdd]⟩] == some (.failure .stackSize)) = true := by
  native_decide

example : ([[], [trueElement]] : List Stack).all (fun stack =>
    run [.op .OP_2DUP, .pushNum 1] stack true (List.replicate 1001 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2DUP, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2DUP, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

-- The static allowance accounts for both copies; the length-only premise excludes 2DUP.
example : ScriptElement.stackGrowthAllowance (.op .OP_2DUP) = 2 := rfl

example : stackGrowthAllowance [.op .OP_2DUP, .op .OP_DROP] = 2 := rfl

example : ¬ OneItemGrowth [.op .OP_2DUP] := by
  simp [ScriptElement.stackGrowthAllowance]

-- The weighted budget is exact for 998 initial items and one 2DUP.
example : (List.replicate 998 trueElement).length +
    stackGrowthAllowance [.op .OP_2DUP] = maxStackSize := by
  native_decide

end LeanMiniscript.Script
