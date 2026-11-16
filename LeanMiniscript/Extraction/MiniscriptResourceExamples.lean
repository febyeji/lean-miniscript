import LeanMiniscript.Extraction.MiniscriptObligations
import LeanMiniscript.Extraction.MiniscriptDissatisfactionCounterexample

namespace LeanMiniscript.Extraction.MiniscriptResourceExamples

open LeanMiniscript.Miniscript LeanMiniscript.Properties LeanMiniscript.Script

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- The ordinary API also exposes unsigned candidates rejected by the final API.
example (env : SatEnv) : satisfy .one env = some [] ∧ satisfyFinal .one env = none := by
  constructor <;> rfl

example (env : SatEnv) (flags : ScriptFlags)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags) :
    ∃ result resources stackLimit dynamicLimit,
      EvalResources (compile .one) [] [] flags env.txCtx [result] [] resources ∧
      castToBool result = true ∧
      (stackPathBounds .one).sat = some stackLimit ∧
      (opPathBounds .one).sat = some dynamicLimit ∧
      Int.ofNat resources.peakStackItems ≤ stackLimit.exec + 1 ∧
      resources.executedMultiSigKeys ≤ dynamicLimit := by
  have valid : ValidMiniscript .p2wsh .one :=
    ⟨_, by decide, (inferTyped .p2wsh .one).get (by decide) |>.property⟩
  exact satisfy_evalResources_le valid sound encodings version modeled rfl

private def key : PubKey := PubKey.ofBytes ⟨#[2] ++ Array.replicate 32 17⟩
private def signedEdge : SaneFragment .p2wsh :=
  (checkSane .p2wsh (DissatisfactionCounterexample.wrapN 200 (.c (.pk_k key)))).toOption.get
    (by decide)

-- The ordinary satisfaction path reaches exactly the 201-opcode boundary.
example : nonPushOpCount signedEdge.compile = 201 := by decide

private theorem edgeGenerated (env : SatEnv) (signature : ByteArray)
    (available : env.signatureFor key = some signature) :
    satisfy signedEdge.checked.fragment env = some [signature] := by
  change (keyCandidates key [] env).sat.usableWitness? = some [signature]
  simp [keyCandidates, available, CandidateResult.usable, CandidateResult.usableWitness?]

example (env : SatEnv) (flags : ScriptFlags) (oracle : CryptoOracle)
    (signature : ByteArray) (available : env.signatureFor key = some signature)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags) (agreement : oracle.RefinesModel) :
    Witness.ItemsBounded [signature] ∧ ∃ top remaining,
      evaluateWithRuntimeLimits oracle signedEdge.compile [signature] [] flags env.txCtx 0 =
        .success [top] [] remaining ∧ castToBool top = true := by
  have generated := edgeGenerated env signature available
  have pushes : ∀ element ∈ signedEdge.compile, element.pushSize ≤ maxScriptElementSize := by
    decide
  obtain ⟨top, remaining, completed, truth, _⟩ :=
    signedEdge.p2wsh_satisfy_runtime_complete_witness sound encodings version modeled
      generated agreement pushes
  exact ⟨satisfy_itemsBounded signedEdge.validMiniscript sound encodings version modeled
    generated, top, remaining, completed, truth⟩

-- An absent satisfaction path still has a bounded generated dissatisfaction at 201.
example (env : SatEnv) (flags : ScriptFlags) (oracle : CryptoOracle)
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags) (agreement : oracle.RefinesModel) :
    ∃ top remaining,
      evaluateWithRuntimeLimits oracle DissatisfactionCounterexample.edgeSane.compile
        [] [] flags env.txCtx 0 = .success [top] [] remaining ∧ castToBool top = false := by
  have pushes : ∀ element ∈ DissatisfactionCounterexample.edgeSane.compile,
      element.pushSize ≤ maxScriptElementSize := by decide
  obtain ⟨top, remaining, completed, truth, _⟩ :=
    DissatisfactionCounterexample.edgeSane.p2wsh_dissatisfy_runtime_complete_witness
      sound encodings version modeled (DissatisfactionCounterexample.edgeGenerated env)
      agreement pushes
  exact ⟨top, remaining, completed, truth⟩

-- Normal obligation imports expose the exact unchanged public proposition.
example : P2WSHResourceLimits := p2wshResourceLimits

end LeanMiniscript.Extraction.MiniscriptResourceExamples
