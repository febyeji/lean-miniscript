import LeanMiniscript.Extraction.TapscriptFrameRecovery

/-! Qualified calls and dot notation on the Tapscript execution context. -/

namespace LeanMiniscript.Extraction.TapscriptFrameRecoveryExamples

open LeanMiniscript.Miniscript LeanMiniscript.Script TapscriptWitness

variable {root child env flags args other consumed}
  (ctx : ExecutionContext root child env flags args other consumed)

section

variable {inner : CoreFragment} {part : Witness} (keys : ∀ k ∈ inner.keys, k ∈ child.keys)
  (locks : ∀ l ∈ inner.hashLocks, l ∈ child.hashLocks) (items : ∀ i ∈ part, i ∈ consumed)

example : ExecutionContext root inner env flags args other part :=
  LeanMiniscript.Extraction.TapscriptWitness.ExecutionContext.restrict ctx keys locks items

example : ExecutionContext root inner env flags args other part :=
  ctx.restrict keys locks items

end

section

variable {sig : StackElement} {key : PubKey} (present : key ∈ child.keys) (member : sig ∈ consumed)
  (checked : checkSigWithEncoding checkSig checkSchnorrSig flags env.txCtx sig key.bytes = .ok true)

example : env.signatureFor key = some sig :=
  LeanMiniscript.Extraction.TapscriptWitness.ExecutionContext.signature ctx present member checked

example : env.signatureFor key = some sig :=
  ctx.signature present member checked

end

section

variable {item : StackElement} {lock : HashLock} (present : lock ∈ child.hashLocks)
  (member : item ∈ consumed) (matched : lock.Matches item)

example : env.preimageFor lock = some item :=
  LeanMiniscript.Extraction.TapscriptWitness.ExecutionContext.preimage ctx present member matched

example : env.preimageFor lock = some item :=
  ctx.preimage present member matched

end

end LeanMiniscript.Extraction.TapscriptFrameRecoveryExamples
