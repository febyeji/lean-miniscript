import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! 2SWAP regressions pass through the codec before runtime execution.
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

private def four : Stack :=
  [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩]

private def swappedFour : Stack :=
  [⟨#[0xcc]⟩, ⟨#[0xdd]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩]

private def byteFixtures : List (Stack × Stack) :=
  [(four, swappedFour),
   (four ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩], swappedFour ++ [⟨#[0x11]⟩, ⟨#[0x22]⟩]),
   ([⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0, 0x80]⟩],
    [⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[0, 0x80]⟩]),
   ([⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩,
      ⟨#[]⟩, ⟨#[0x80]⟩],
    [⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[0xff, 0xff, 0xff, 0x7f]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[]⟩, ⟨#[]⟩],
    [⟨#[]⟩, ⟨#[]⟩, ⟨#[0xaa]⟩, ⟨#[]⟩])]

-- Pair order, lower stack, negative zero and long/nonminimal bytes are retained.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_2SWAP] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Every input length below four fails before the suffix, with either flag setting.
example : [false, true].all (fun minimal => (List.range 4).all fun count =>
    run [.op .OP_2SWAP, .pushNum 1] (List.replicate count ⟨#[1, 0, 0, 0, 0]⟩)
      minimal [trueElement] == some (.failure .stackUnderflow)) = true := by
  native_decide

example : run [.op .OP_2SWAP, .op .OP_TOALTSTACK]
    (four ++ [⟨#[0x11]⟩]) true [⟨#[0x22]⟩] 0 =
    some (.success [⟨#[0xdd]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0x11]⟩]
      [⟨#[0xcc]⟩, ⟨#[0x22]⟩] 0) := by
  native_decide

example : run [.op .OP_2SWAP, .op .OP_VERIFY, .pushNum 1]
    [trueElement, trueElement, ByteArray.empty, trueElement] =
    some (.failure .verify) := by
  native_decide

-- Two exchanges restore both pairs and the lower stack.
example : run [.op .OP_2SWAP, .op .OP_2SWAP]
    (four ++ [⟨#[0x80]⟩]) true [trueElement] =
    some (.success (four ++ [⟨#[0x80]⟩]) [trueElement] 17) := by
  native_decide

example : (List.range 6).all (fun count =>
    let stack : Stack := List.replicate count ⟨#[0x80]⟩
    run [.pushNum 0, .op .OP_IF, .op .OP_2SWAP, .op .OP_ENDIF]
      stack true [⟨#[0xdd]⟩] 0 == some (.success stack [⟨#[0xdd]⟩] 0)) = true := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2SWAP)
    { stack := four, altStack := [⟨#[0x11]⟩], conditions := [true, true], weight := 0 }
    {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some (swappedFour, [⟨#[0x11]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_2SWAP)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0x11]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0x11]⟩], [true, false, true], 17) := by
  native_decide

-- Exchanging pairs preserves the combined stack count at the allowed limit.
example : run [.op .OP_2SWAP] (four ++ List.replicate 996 ByteArray.empty) =
    some (.success (swappedFour ++ List.replicate 996 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_2SWAP] (four ++ List.replicate 995 ByteArray.empty)
    true [⟨#[0x11]⟩] =
    some (.success (swappedFour ++ List.replicate 995 ByteArray.empty) [⟨#[0x11]⟩] 17) := by
  native_decide

-- An oversized result fails before the suffix can remove an item.
example : run [.op .OP_2SWAP, .op .OP_DROP] (four ++ List.replicate 997 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_2SWAP, .op .OP_DROP] (four ++ List.replicate 996 ByteArray.empty)
    true [⟨#[0x11]⟩] = some (.failure .stackSize) := by
  native_decide

-- Underflow precedes the shared resource check for every short main stack.
example : (List.range 4).all (fun count =>
    run [.op .OP_2SWAP, .pushNum 1] (List.replicate count trueElement)
      true (List.replicate 1001 trueElement) == some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2SWAP, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

example : evaluateRuntime oracle [.op .OP_2SWAP, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_2SWAP) = 0 := rfl
example : OneItemGrowth [.op .OP_2SWAP] := by
  simp [ScriptElement.stackGrowthAllowance]
example : serializeScript [.op .OP_2SWAP] = .ok ⟨#[0x72]⟩ := rfl
example : deserializeScript ⟨#[0x72]⟩ = .ok [.op .OP_2SWAP] := by
  exact deserializeScript_serializeScript_of_normalized
    [.op .OP_2SWAP] ⟨#[0x72]⟩ (by rfl) (by rfl)

end LeanMiniscript.Script
