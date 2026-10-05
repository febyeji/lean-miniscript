import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.RuntimeStackBounds

namespace LeanMiniscript.Script

/-! 3DUP regressions serialize and deserialize scripts before runtime execution.
All expected stacks use top-first order and retain the original raw bytes. -/

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

private def inputStack : Stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]

private def copiedStack : Stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩]

private def byteFixtures : List (Stack × Stack) :=
  [(inputStack, copiedStack),
   (inputStack ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩], copiedStack ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩]),
   ([⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0, 0x80]⟩],
    [⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0, 0x80]⟩]),
   ([⟨#[1, 0, 0, 0, 0]⟩, ⟨#[1, 0]⟩, ⟨#[0x80]⟩],
    [⟨#[1, 0, 0, 0, 0]⟩, ⟨#[1, 0]⟩, ⟨#[0x80]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[1, 0]⟩, ⟨#[0x80]⟩])]

-- Copy order, lower stack, negative zero and long/nonminimal bytes are retained.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_3DUP] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Every input length below 3 fails before a suffix with either flag setting.
example : [false, true].all (fun minimal => (List.range 3).all fun count =>
    run [.op .OP_3DUP, .pushNum 1] (List.replicate count ⟨#[1, 0, 0, 0, 0]⟩)
      minimal [trueElement] == some (.failure .stackUnderflow)) = true := by
  native_decide

-- Moving every copy to the alternate stack exposes the unchanged original.
example : run [.op .OP_3DUP, .op .OP_TOALTSTACK, .op .OP_TOALTSTACK, .op .OP_TOALTSTACK]
    (inputStack ++ [⟨#[0x11]⟩]) true [⟨#[0x22]⟩] 0 =
    some (.success (inputStack ++ [⟨#[0x11]⟩]) [⟨#[0xcc]⟩, ⟨#[0xbb]⟩, ⟨#[0xaa]⟩, ⟨#[0x22]⟩] 0) := by
  native_decide

example : run [.op .OP_3DUP, .op .OP_VERIFY, .pushNum 1]
    [⟨#[]⟩, ⟨#[1]⟩, ⟨#[1]⟩] = some (.failure .verify) := by
  native_decide

example : (List.range 5).all (fun count =>
    let stack : Stack := List.replicate count ⟨#[0x80]⟩
    run [.pushNum 0, .op .OP_IF, .op .OP_3DUP, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_3DUP)
    { stack := inputStack, altStack := [⟨#[0x11]⟩], conditions := [true, true], weight := 0 }
    {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some (copiedStack, [⟨#[0x11]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_3DUP)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0x11]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0x11]⟩], [true, false, true], 17) := by
  native_decide

-- Active execution grows 997 combined items to the allowed limit of 1000.
example : run [.op .OP_3DUP] (inputStack ++ List.replicate 994 ByteArray.empty) =
    some (.success (copiedStack ++ List.replicate 994 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_3DUP] (inputStack ++ List.replicate 993 ByteArray.empty)
    true [⟨#[0x11]⟩] =
    some (.success (copiedStack ++ List.replicate 993 ByteArray.empty) [⟨#[0x11]⟩] 17) := by
  native_decide

-- Each larger initial count through 1000 fails before a suffix DROP.
example : [995, 996, 997].all (fun count =>
    run [.op .OP_3DUP, .op .OP_DROP] (inputStack ++ List.replicate count ByteArray.empty) ==
      some (.failure .stackSize)) = true := by
  native_decide

example : [994, 995, 996].all (fun count =>
    run [.op .OP_3DUP, .op .OP_DROP] (inputStack ++ List.replicate count ByteArray.empty)
      true [⟨#[0x11]⟩] == some (.failure .stackSize)) = true := by
  native_decide

-- Underflow precedes the shared resource check for every short main stack.
example : (List.range 3).all (fun count =>
    run [.op .OP_3DUP, .pushNum 1] (List.replicate count trueElement)
      true (List.replicate 1001 trueElement) == some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_3DUP, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

example : evaluateRuntime oracle [.op .OP_3DUP, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_3DUP) = 3 := rfl
example : stackGrowthAllowance [.op .OP_3DUP, .op .OP_DROP] = 3 := rfl
example : ¬ OneItemGrowth [.op .OP_3DUP] := by
  simp [ScriptElement.stackGrowthAllowance]

example : (List.replicate 997 trueElement).length +
    stackGrowthAllowance [.op .OP_3DUP] = maxStackSize := by
  native_decide

example : serializeScript [.op .OP_3DUP] = .ok ⟨#[0x6f]⟩ := rfl
example : deserializeScript ⟨#[0x6f]⟩ = .ok [.op .OP_3DUP] := by
  exact deserializeScript_serializeScript_of_normalized
    [.op .OP_3DUP] ⟨#[0x6f]⟩ (by rfl) (by rfl)

end LeanMiniscript.Script
