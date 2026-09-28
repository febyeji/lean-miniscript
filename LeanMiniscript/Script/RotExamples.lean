import LeanMiniscript.Script.Codec.ExecutionProofs
import LeanMiniscript.Script.StackGrowthAllowance

namespace LeanMiniscript.Script

/-! ROT regressions serialize and deserialize each script before runtime
execution. The stacks below use top-first order and preserve raw bytes. -/

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
  [([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], [⟨#[0xcc]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩]),
   ([⟨#[]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩], [⟨#[0xcc]⟩, ⟨#[]⟩, ⟨#[0xbb]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[]⟩, ⟨#[0xcc]⟩], [⟨#[0xcc]⟩, ⟨#[0xaa]⟩, ⟨#[]⟩]),
   ([⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩], [⟨#[]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩]),
   ([⟨#[0x80]⟩, ⟨#[1, 0]⟩, ⟨#[1, 0, 0, 0, 0]⟩],
    [⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[1, 0]⟩]),
   ([⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[0]⟩, ⟨#[0xaa, 0x55]⟩],
    [⟨#[0]⟩, ⟨#[1, 0, 0, 0, 0]⟩, ⟨#[0x80]⟩, ⟨#[0xaa, 0x55]⟩]),
   ([⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[0xbb]⟩, ⟨#[]⟩, ⟨#[0xcc]⟩],
    [⟨#[0xbb]⟩, ⟨#[1, 0]⟩, ⟨#[0, 0x80]⟩, ⟨#[]⟩, ⟨#[0xcc]⟩])]

-- Rotation retains every byte and the lower stack under both flag settings.
example : [false, true].all (fun minimal => byteFixtures.all fun (input, expected) =>
    run [.op .OP_ROT] input minimal [⟨#[0x80]⟩, ⟨#[0xdd]⟩] ==
      some (.success expected [⟨#[0x80]⟩, ⟨#[0xdd]⟩] 17)) = true := by
  native_decide

-- Zero, one and two items fail before any suffix, including malformed numbers.
example : [false, true].all (fun minimal =>
    ([[], [⟨#[]⟩], [⟨#[1, 0, 0, 0, 0]⟩], [⟨#[0x80]⟩, ⟨#[1, 0]⟩]] : List Stack).all
      fun stack => run [.op .OP_ROT, .pushNum 1] stack minimal [trueElement] ==
        some (.failure .stackUnderflow)) = true := by
  native_decide

-- The continuation receives the third item at the top, with the tail intact.
example : run [.op .OP_ROT, .op .OP_TOALTSTACK]
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩] true [⟨#[0xee]⟩] 0 =
    some (.success [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xdd]⟩] [⟨#[0xcc]⟩, ⟨#[0xee]⟩] 0) := by
  native_decide

example : run [.op .OP_ROT, .op .OP_VERIFY, .pushNum 1]
    [trueElement, trueElement, ByteArray.empty] = some (.failure .verify) := by
  native_decide

-- Inactive source-order execution skips underflow and preserves every stack.
example : ([[], [⟨#[0x80]⟩], [⟨#[0xaa]⟩, ⟨#[0xbb]⟩],
    [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩]] : List Stack).all
    (fun stack => run [.pushNum 0, .op .OP_IF, .op .OP_ROT, .op .OP_ENDIF]
      stack true [⟨#[0xee]⟩] 0 == some (.success stack [⟨#[0xee]⟩] 0)) = true := by
  native_decide

-- Observe condition-stack and signature-budget preservation at one step.
example : ((runtimeStep oracle (.op .OP_ROT)
    { stack := [⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xcc]⟩, ⟨#[0xdd]⟩], altStack := [⟨#[0xee]⟩],
      conditions := [true, true], weight := 0 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0xcc]⟩, ⟨#[0xaa]⟩, ⟨#[0xbb]⟩, ⟨#[0xdd]⟩], [⟨#[0xee]⟩], [true, true], 0) := by
  native_decide

example : ((runtimeStep oracle (.op .OP_ROT)
    { stack := [⟨#[0x80]⟩], altStack := [⟨#[0xdd]⟩],
      conditions := [true, false, true], weight := 17 } {} ctx).toOption.map
    fun state => (state.stack, state.altStack, state.conditions, state.weight)) =
    some ([⟨#[0x80]⟩], [⟨#[0xdd]⟩], [true, false, true], 17) := by
  native_decide

-- Rotation keeps the combined count at the allowed limit of 1000.
example : run [.op .OP_ROT]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xcc]⟩ :: List.replicate 997 ByteArray.empty) =
    some (.success (⟨#[0xcc]⟩ :: ⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ ::
      List.replicate 997 ByteArray.empty) [] 17) := by
  native_decide

example : run [.op .OP_ROT]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xcc]⟩ :: List.replicate 996 ByteArray.empty)
    true [⟨#[0xdd]⟩] =
    some (.success (⟨#[0xcc]⟩ :: ⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ ::
      List.replicate 996 ByteArray.empty) [⟨#[0xdd]⟩] 17) := by
  native_decide

-- An oversized count fails before a following DROP could reduce it.
example : run [.op .OP_ROT, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xcc]⟩ :: List.replicate 998 ByteArray.empty) =
    some (.failure .stackSize) := by
  native_decide

example : run [.op .OP_ROT, .op .OP_DROP]
    (⟨#[0xaa]⟩ :: ⟨#[0xbb]⟩ :: ⟨#[0xcc]⟩ :: List.replicate 997 ByteArray.empty)
    true [⟨#[0xdd]⟩] = some (.failure .stackSize) := by
  native_decide

-- Underflow precedes the resource check even with an oversized alternate stack.
example : ([[], [trueElement], [trueElement, trueElement]] : List Stack).all (fun stack =>
    run [.op .OP_ROT, .pushNum 1] stack true (List.replicate 1001 trueElement) ==
      some (.failure .stackUnderflow)) = true := by
  native_decide

example : evaluateRuntime oracle [.op .OP_ROT, .op .OP_ENDIF]
    { stack := List.replicate 999 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx =
    .success (List.replicate 999 trueElement) [⟨#[0xdd]⟩] 17 := by
  native_decide

-- Skipped instructions also check an already oversized combined stack.
example : evaluateRuntime oracle [.op .OP_ROT, .op .OP_ENDIF]
    { stack := List.replicate 1000 trueElement, altStack := [⟨#[0xdd]⟩],
      conditions := [false], weight := 17 } {} ctx = .failure .stackSize := by
  native_decide

example : ScriptElement.stackGrowthAllowance (.op .OP_ROT) = 0 := rfl

end LeanMiniscript.Script
