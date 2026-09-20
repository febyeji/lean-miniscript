import LeanMiniscript.Properties.ResourceBounds

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript

/-! Core-compatible path-sensitive resource boundary fixtures. -/

private def compressedKey : PubKey :=
  PubKey.ofBytes ⟨#[0x02] ++ (List.replicate 32 0x11).toArray⟩

private def xOnlyKey : PubKey :=
  PubKey.ofBytes ⟨(List.replicate 32 0x22).toArray⟩

private def wrapN : Nat → CoreFragment → CoreFragment
  | 0, fragment => fragment
  | n + 1, fragment => .n (wrapN n fragment)

private def signedKey : CoreFragment := .c (.pk_k compressedKey)

/-- CHECKSIG is already part of the static non-push opcode count. -/
private def ops201Checksig : CoreFragment := wrapN 200 signedKey
private def ops202Checksig : CoreFragment := wrapN 201 signedKey

example : maxSatisfactionOpCount ops201Checksig = some 201 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh ops201Checksig = true := by
  native_decide

example : maxSatisfactionOpCount ops202Checksig = some 202 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh ops202Checksig = false := by
  native_decide

private def twentyKeyMulti : CoreFragment :=
  .multi 19 (List.replicate 20 compressedKey)

/-- Alternative CHECKMULTISIG branches contribute their maximum dynamic key
    count, rather than the sum of both mutually exclusive branches. -/
private def exclusiveOps201 : CoreFragment :=
  wrapN 176 (.or_i twentyKeyMulti twentyKeyMulti)

private def exclusiveOps202 : CoreFragment :=
  wrapN 177 (.or_i twentyKeyMulti twentyKeyMulti)

example : (opPathBounds exclusiveOps201).sat = some 20 := by
  native_decide

example : maxSatisfactionOpCount exclusiveOps201 = some 201 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh exclusiveOps201 = true := by
  native_decide

example : maxSatisfactionOpCount exclusiveOps202 = some 202 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh exclusiveOps202 = false := by
  native_decide

/-- Five sequential 19-of-20 multisignatures consume exactly 100 initial
    witness items while remaining below the script-size and opcode limits. -/
private def p2wshStack100 : CoreFragment :=
  .and_v (.v twentyKeyMulti)
    (.and_v (.v twentyKeyMulti)
      (.and_v (.v twentyKeyMulti)
        (.and_v (.v twentyKeyMulti) twentyKeyMulti)))

/-- Appending one signature raises only the initial-stack requirement to 101. -/
private def p2wshStack101 : CoreFragment :=
  .and_v (.v p2wshStack100) signedKey

example : maxSatisfactionInitialStack p2wshStack100 = some 100 := by
  native_decide

example : (resourceUsage p2wshStack100).scriptSize = some 3429 := by
  native_decide

example : maxSatisfactionOpCount p2wshStack100 = some 109 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh p2wshStack100 = true := by
  native_decide

example : maxSatisfactionInitialStack p2wshStack101 = some 101 := by
  native_decide

example : (resourceUsage p2wshStack101).scriptSize = some 3465 := by
  native_decide

example : maxSatisfactionOpCount p2wshStack101 = some 111 := by
  native_decide

example : resourceLimitsSatisfied .p2wsh p2wshStack101 = false := by
  native_decide

private def tapscriptMulti999 : CoreFragment :=
  .multi_a 1 (List.replicate 999 xOnlyKey)

private def tapscriptMulti1000 : CoreFragment :=
  .multi_a 1 (List.replicate 1000 xOnlyKey)

example : maxSatisfactionExecutionStack tapscriptMulti999 = some 1000 := by
  native_decide

example : (resourceUsage tapscriptMulti999).scriptSize = some 33968 := by
  native_decide

example : resourceLimitsSatisfied .tapscript tapscriptMulti999 = true := by
  native_decide

example : maxSatisfactionExecutionStack tapscriptMulti1000 = some 1001 := by
  native_decide

example : resourceLimitsSatisfied .tapscript tapscriptMulti1000 = false := by
  native_decide

example : scriptSizeWithinContextLimit .p2wsh 3600 = true := by
  native_decide

example : scriptSizeWithinContextLimit .p2wsh 3601 = false := by
  native_decide

example : scriptSizeWithinContextLimit .tapscript 329482 = true := by
  native_decide

example : scriptSizeWithinContextLimit .tapscript 329483 = false := by
  native_decide

/-- The executable size analysis fixes pk_h's opaque formal HASH160 boundary at
    the protocol-mandated 20 bytes. -/
example :
    (match resourceSerializedScriptSize (.pk_h compressedKey) with
    | .ok size => size == 24
    | .error _ => false) = true := by
  native_decide

end LeanMiniscript.Properties
