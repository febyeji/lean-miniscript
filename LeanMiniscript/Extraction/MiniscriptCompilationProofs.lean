import LeanMiniscript.Extraction.MiniscriptCompilation
import LeanMiniscript.Extraction.BitcoinCoreSatisfactionProofs
import LeanMiniscript.Extraction.BitcoinCoreWitnessV0Proofs
import LeanMiniscript.Properties.ResourceBoundsProofs

/-! Proofs of the Miniscript compilation obligations in `MiniscriptCompilation`. -/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open LeanMiniscript.Properties

/-- A generated final satisfaction of a sane P2WSH fragment passes Core's
VerifyScript from the witness-v0 output of its compiled bytes. Sanity bounds
the serialized script by 3600 bytes; the generated runtime execution and
encoding contracts supply the remaining witness-v0 resource bounds. -/
theorem p2wshSatisfaction : P2WSHSatisfaction := by
  intro sane bytes scriptPubKey suffix env flags ctx oracles keyPath arguments
    ⟨serialized, hashes⟩ ⟨spend, rest, programTruth⟩
    ⟨enabled, _, _, _, modeled, sound, encodings, context, agreement⟩ generated
  subst spend rest
  change (oracles .witnessV0 bytes).RefinesModel at agreement
  have small := compile_pushSize_le (fun data => by rw [hashes data]; decide)
    sane.checked.wellFormed
  have encoded : CoreTapscriptEncoding bytes 0 (compile sane.checked.fragment) :=
    CoreTapscriptEncoding.of_serializeScript _ bytes
      (fun element member => by have := small element member; omega) serialized
  have pushes : ∀ element ∈ sane.compile, element.pushSize ≤ maxScriptElementSize :=
    fun element member => Nat.le_trans (small element member) (by decide)
  have version : ModeledContextVersion .p2wsh env.txCtx := by
    simp [ModeledContextVersion, context, compiledScriptContext]
  have sizes := satisfyFinal_itemsBounded sane.validMiniscript sound encodings version
    modeled generated
  have scriptSize : bytes.size ≤ 10000 := by
    have limits := sane.withinResourceLimits
    simp only [WithinResourceLimits, resourceLimitsSatisfied, Bool.and_eq_true] at limits
    have compiledLimit := limits.1.1
    change serializeScript (compileWithKeyHash modelKeyHash sane.checked.fragment) =
      .ok bytes at serialized
    rw [compiledScriptSizeWithinLimit,
      resourceSerializedScriptSize_eq_compileWithKeyHash modelKeyHash
        (fun key => hashes key.bytes), Script.serializedScriptSize, serialized] at compiledLimit
    simp only [Except.map, scriptSizeWithinContextLimit, saneScriptSizeLimit,
      MAX_STANDARD_P2WSH_SCRIPT_SIZE, decide_eq_true_eq] at compiledLimit
    omega
  obtain ⟨top, remaining, completed, truth⟩ :=
    sane.p2wsh_satisfyFinal_runtime_complete_witness sound encodings version modeled
      generated agreement pushes
  exact verifyCoreScripts_of_witnessV0_runtime flags ctx oracles keyPath arguments bytes
    (compile sane.checked.fragment) enabled encoded scriptSize sizes programTruth
    (by simpa [SaneFragment.compile, compileChecked, context, compiledScriptContext,
      coreWitnessV0Context, Witness.toInitialStack] using completed) truth

/-- A generated final satisfaction of a sane Tapscript fragment passes Core's
VerifyScript from an output that commits to the compiled bytes. The compiled
pushes are at most 33 bytes, so the serialized bytes decode to the compiled
script; the sane-fragment runtime theorem runs the satisfaction to a truthy
singleton within the validation-weight budget. -/
theorem tapscriptSatisfaction : TapscriptSatisfaction := by
  intro sane bytes scriptPubKey suffix env flags ctx oracles keyPath arguments
    ⟨serialized, hashes⟩ ⟨output, control, root, spend, rest, committed, outputTruth⟩
    ⟨enabled, taproot, locktime, sequence, modeled, sound, encodings, context, agreement⟩
    generated
  subst spend rest
  change (oracles .tapscript bytes).RefinesModel at agreement
  have small := compile_pushSize_le (fun data => by rw [hashes data]; decide)
    sane.checked.wellFormed
  have encoded : CoreTapscriptEncoding bytes 0 (compile sane.checked.fragment) :=
    CoreTapscriptEncoding.of_serializeScript _ bytes
      (fun element member => by have := small element member; omega) serialized
  have pushes : ∀ element ∈ sane.compile, element.pushSize ≤ maxScriptElementSize :=
    fun element member => Nat.le_trans (small element member) (by decide)
  have version : ModeledContextVersion .tapscript env.txCtx := by
    simp [ModeledContextVersion, context, compiledScriptContext]
  have sizes := satisfyFinal_itemsBounded sane.validMiniscript sound encodings version
    modeled generated
  have leafContext : env.txCtx =
      coreTapscriptContext ctx (coreTaprootRequest arguments bytes control) := by
    rw [context]
    rfl
  obtain ⟨top, remaining, completed, truth, count⟩ :=
    sane.tapscript_satisfyFinal_runtime_complete_witness sound encodings version modeled
      generated agreement pushes (fullWitness := arguments ++ [bytes, control])
      (List.sublist_append_left _ _)
  rw [leafContext] at completed
  exact verifyCoreScripts_of_taproot_runtime flags ctx oracles keyPath arguments bytes control
    output root (compile sane.checked.fragment) enabled (taproot rfl) committed outputTruth
    encoded count sizes
    (by simpa [SaneFragment.compile, compileChecked, coreTaprootRequest, initialValidationWeight,
      validationWeightOffset, Nat.add_comm, Witness.toInitialStack] using completed)
    truth

end LeanMiniscript.Extraction
