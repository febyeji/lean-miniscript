import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! 2ROT regressions pass through the codec before runtime execution.
All stack fixtures use top-first order. -/

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

private def six : Stack :=
  [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩, ⟨#[0xee]⟩, ⟨#[0xff]⟩]

private def rotatedSix : Stack :=
  [⟨#[0xee]⟩, ⟨#[0xff]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩]

private def byteFixtures : List (Stack × Stack) :=
  [(six, rotatedSix),
   (six ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩], rotatedSix ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩]),
   ([⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩,
      ⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩, ⟨#[0, 0x80]⟩],
    [⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩,
      ⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0, 0x80]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩, ⟨#[0xdd]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩],
    [⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩, ⟨#[0xdd]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[0xcc]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩],
    [⟨#[]⟩, ⟨#[]⟩, ⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[0xcc]⟩, ⟨#[]⟩])]

-- Pair order, lower stack, negative zero and long/nonminimal bytes are retained.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_2ROT] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Every input length below six fails before the suffix, with either flag setting.
example : [false, true].all (fun minimal => (List.range 6).all fun count =>
    run [.op .OP_2ROT, .pushNum 1] (List.replicate count ⟨#[1, 0, 0, 0, 0]⟩)
      minimal [trueElement] == some (.failure .stackUnderflow)) = true := by
  native_decide

example : run [.op .OP_2ROT, .op .OP_TOALTSTACK]
    (six ++ [⟨#[0x11]⟩]) true [⟨#[0x22]⟩] 0 =
    some (.success [⟨#[0xff]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩, ⟨#[0x11]⟩]
      [⟨#[0xee]⟩, ⟨#[0x22]⟩] 0) := by
  native_decide

example : run [.op .OP_2ROT, .op .OP_VERIFY, .pushNum 1]
    [trueElement, trueElement, trueElement, trueElement, ByteArray.empty, trueElement] =
    some (.failure .verify) := by
  native_decide

-- Three rotations restore each of the three pairs and the lower stack.
example : run [.op .OP_2ROT, .op .OP_2ROT, .op .OP_2ROT]
    (six ++ [⟨#[0x80]⟩]) true [trueElement] =
    some (.success (six ++ [⟨#[0x80]⟩]) [trueElement] 17) := by
  native_decide

example : (List.range 8).all (fun count =>
    let stack : Stack := List.replicate count ⟨#[0x80]⟩
    run [.pushNum 0, .op .OP_IF, .op .OP_2ROT, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2ROT)
    { stack := six, altStack := [⟨#[0x11]⟩], conditions := [true, true], weight := 0 }
    {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some (rotatedSix, [⟨#[0x11]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2ROT)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0x11]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0x11]⟩], [true, false, true], 17) := by
  native_decide

-- Rotation preserves the combined stack count at the allowed limit.
example : run [.op .OP_2ROT] (six ++ List.replicate 994 ByteArray.empty) =
    some (.success (rotatedSix ++ List.replicate 994 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_2ROT] (six ++ List.replicate 993 ByteArray.empty)
    true [⟨#[0x11]⟩] =
    some (.success (rotatedSix ++ List.replicate 993 ByteArray.empty) [⟨#[0x11]⟩] 17) := by
  native_decide

-- An oversized result fails before the suffix can remove an item.
example : run [.op .OP_2ROT, .op .OP_DROP] (six ++ List.replicate 995 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_2ROT, .op .OP_DROP] (six ++ List.replicate 994 ByteArray.empty)
    true [⟨#[0x11]⟩] = some (.failure .stackSize) := by
  native_decide

-- Underflow precedes the shared resource check for every short main stack.
example : (List.range 6).all (fun count =>
    run [.op .OP_2ROT, .pushNum 1] (List.replicate count trueElement)
      true (List.replicate 1001 trueElement) == some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2ROT, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2ROT, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_2ROT) = 0 := rfl
example : OneItemGrowth [.op .OP_2ROT] := by
  simp [ScriptElement.stackGrowthAllowance]
example : serializeScript [.op .OP_2ROT] = .ok ⟨#[0x71]⟩ := rfl
example : deserializeScript ⟨#[0x71]⟩ = .ok [.op .OP_2ROT] := by
  exact deserializeScript_serializeScript_of_normalized
    [.op .OP_2ROT] ⟨#[0x71]⟩ (by rfl) (by rfl)

end LeanMiniscript.Script
