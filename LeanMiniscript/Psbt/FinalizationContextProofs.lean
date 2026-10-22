import LeanMiniscript.Psbt.FinalizedFieldsProofs
import LeanMiniscript.Psbt.ExtractionProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

/-- Input fields used to reconstruct the transaction and resolve its UTXOs. -/
structure InputContext where
  nonWitnessUtxo : Option Transaction
  witnessUtxo : Option TxOutput
  previousTxid : Option ByteArray
  outputIndex : Option UInt32
  sequence : Option UInt32
  requiredTimeLocktime : Option UInt32
  requiredHeightLocktime : Option UInt32

def InputFields.context (input : InputFields) : InputContext :=
  ⟨input.nonWitnessUtxo, input.witnessUtxo, input.previousTxid, input.outputIndex,
    input.sequence, input.requiredTimeLocktime, input.requiredHeightLocktime⟩

/-- The input key types that determine transaction reconstruction or UTXO lookup. -/
def contextKeyTypes : List Nat := [0x00, 0x01, 0x0e, 0x0f, 0x10, 0x11, 0x12]

private theorem inputStep_preserves_context {version : Nat} {before after : InputFields}
    {record : Record} (irrelevant : ∀ key ∈ contextKeyTypes, record.keyType? ≠ some key)
    (read : inputStep version before record = .ok after) : after.context = before.context := by
  unfold inputStep at read
  rw [bind_eq_ok] at read
  rcases read with ⟨⟨keyType, keyData⟩, key, read⟩
  have notKey (wanted : Nat) (member : wanted ∈ contextKeyTypes) : (keyType == wanted) = false := by
    have := irrelevant wanted member
    simpa [Record.keyType?, key] using this
  have h0 := notKey 0 (by simp [contextKeyTypes])
  have h1 := notKey 1 (by simp [contextKeyTypes])
  have h14 := notKey 14 (by simp [contextKeyTypes])
  have h15 := notKey 15 (by simp [contextKeyTypes])
  have h16 := notKey 16 (by simp [contextKeyTypes])
  have h17 := notKey 17 (by simp [contextKeyTypes])
  have h18 := notKey 18 (by simp [contextKeyTypes])
  simp only [KeyType.inNonWitnessUtxo, KeyType.inWitnessUtxo, KeyType.inPreviousTxid,
    KeyType.inOutputIndex, KeyType.inSequence, KeyType.inRequiredTimeLocktime,
    KeyType.inRequiredHeightLocktime, h0, h1, h14, h15, h16, h17, h18,
    Bool.false_eq_true, if_false] at read
  repeat' first
    | (cases read; rfl)
    | (rw [bind_eq_ok] at read; rcases read with ⟨_, _, read⟩)
    | (rw [ite_eq_ok] at read; rcases read with ⟨_, read⟩ | ⟨_, read⟩)
    | split at read

private theorem inputStep_context_congr {version : Nat} {left right left' right' : InputFields}
    {record : Record} (same : left.context = right.context)
    (read : inputStep version left record = .ok left')
    (other : inputStep version right record = .ok right') : left'.context = right'.context := by
  by_cases relevant : ∃ key ∈ contextKeyTypes, record.keyType? = some key
  · obtain ⟨keyType, member, found⟩ := relevant
    cases key : splitKey record.key with
    | error error => simp [inputStep, key, bind, Except.bind] at read
    | ok pair =>
      rcases pair with ⟨actual, keyData⟩
      simp [Record.keyType?, key] at found
      subst actual
      simp only [InputFields.context, InputContext.mk.injEq] at same
      simp [contextKeyTypes] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [inputStep, key, bind, Except.bind, KeyType.inNonWitnessUtxo,
          KeyType.inWitnessUtxo, KeyType.inPartialSig, KeyType.inSighashType,
          KeyType.inRedeemScript, KeyType.inWitnessScript, KeyType.inBip32Derivation,
          KeyType.inFinalScriptSig, KeyType.inFinalScriptWitness, KeyType.inRipemd160,
          KeyType.inSha256, KeyType.inHash160, KeyType.inHash256, KeyType.inPreviousTxid,
          KeyType.inOutputIndex, KeyType.inSequence, KeyType.inRequiredTimeLocktime,
          KeyType.inRequiredHeightLocktime, Nat.reduceBEq, Bool.false_eq_true,
          if_true, if_false, Bool.or_false, pure, Except.pure] at read other
        repeat' (split at read <;> simp_all [InputFields.context, throw, throwThe, MonadExceptOf.throw])
        all_goals subst left'; subst right'; simp_all
  · have irrelevant : ∀ key ∈ contextKeyTypes, record.keyType? ≠ some key := by
      simpa using relevant
    exact (inputStep_preserves_context irrelevant read).trans
      (same.trans (inputStep_preserves_context irrelevant other).symm)

private theorem dropped_context {record : Record} (dropped : keepAfterFinalize record = false) :
    ∀ key ∈ contextKeyTypes, record.keyType? ≠ some key := by
  intro key member found
  have retained : [0, 1, 14, 15, 16, 17, 18].contains key = true := by
    simpa [contextKeyTypes] using member
  simp only [keepAfterFinalize, found, retained, Bool.true_or, Bool.true_eq_false] at dropped

private theorem fold_filter_context {version : Nat} {map : KeyValueMap}
    {left right left' right' : InputFields} (same : left.context = right.context)
    (read : map.foldlM (inputStep version) left = .ok left')
    (other : (map.filter keepAfterFinalize).foldlM (inputStep version) right = .ok right') :
    left'.context = right'.context := by
  induction map generalizing left right with
  | nil => cases read; cases other; exact same
  | cons record rest ih =>
    rw [List.foldlM_cons, bind_eq_ok] at read
    rcases read with ⟨next, step, read⟩
    cases kept : keepAfterFinalize record with
    | false =>
      simp only [List.filter_cons, kept, Bool.false_eq_true, if_false] at other
      exact ih ((inputStep_preserves_context (dropped_context kept) step).trans same) read other
    | true =>
      simp only [List.filter_cons, kept, if_true, List.foldlM_cons] at other
      rw [bind_eq_ok] at other
      rcases other with ⟨next', step', other⟩
      exact ih (inputStep_context_congr same step step') read other

private theorem fold_irrelevant_context {version : Nat} {map : KeyValueMap}
    {before after : InputFields}
    (irrelevant : ∀ record ∈ map, ∀ key ∈ contextKeyTypes, record.keyType? ≠ some key)
    (read : map.foldlM (inputStep version) before = .ok after) : after.context = before.context := by
  induction map generalizing before with
  | nil => cases read; rfl
  | cons record rest ih =>
    rw [List.foldlM_cons, bind_eq_ok] at read
    rcases read with ⟨next, step, read⟩
    exact (ih (fun r h => irrelevant r (by simp [h])) read).trans
      (inputStep_preserves_context (irrelevant record (by simp)) step)

private theorem decodeInput_fold {version : Nat} {map : KeyValueMap} {input : InputFields}
    (read : decodeInput version map = .ok input) :
    map.foldlM (inputStep version) {} = .ok input := by
  unfold decodeInput at read
  rw [bind_eq_ok] at read
  rcases read with ⟨fields, folded, read⟩
  repeat' (split at read <;> try simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure])
  all_goals cases read <;> exact folded

/-- Replacing signing material with final fields preserves transaction and UTXO fields. -/
theorem decodeInput_finalizedInputMap_context {version : Nat} {map : KeyValueMap}
    {final : FinalInput} {before after : InputFields}
    (read : decodeInput version map = .ok before)
    (written : decodeInput version (finalizedInputMap map final) = .ok after) :
    before.context = after.context := by
  have original := decodeInput_fold read
  have updated := decodeInput_fold written
  unfold finalizedInputMap at updated
  rw [List.append_assoc, List.foldlM_append, bind_eq_ok] at updated
  rcases updated with ⟨middle, kept, finals⟩
  have same := fold_filter_context rfl original kept
  refine same.trans (fold_irrelevant_context ?_ finals).symm
  intro record member key inKeys
  simp only [List.mem_append] at member
  rcases member with sig | witness
  · split at sig <;> simp_all only [List.not_mem_nil, List.mem_singleton]
    subst record
    change some (7 : Nat) ≠ some key
    intro equal
    have := Option.some.inj equal
    subst key
    simp [contextKeyTypes] at inKeys
  · split at witness <;> simp_all only [List.not_mem_nil, List.mem_singleton]
    subst record
    change some (8 : Nat) ≠ some key
    intro equal
    have := Option.some.inj equal
    subst key
    simp [contextKeyTypes] at inKeys

/-- Decoded information used by transaction construction and UTXO lookup. -/
structure DecodedPsbt.SameContext (before after : DecodedPsbt) : Prop where
  global : before.global = after.global
  outputs : before.outputs = after.outputs
  inputs : before.inputs.map InputFields.context = after.inputs.map InputFields.context

theorem DecodedPsbt.SameContext.refl (decoded : DecodedPsbt) : decoded.SameContext decoded :=
  ⟨rfl, rfl, rfl⟩

theorem DecodedPsbt.SameContext.trans {first second third : DecodedPsbt}
    (left : first.SameContext second) (right : second.SameContext third) :
    first.SameContext third :=
  ⟨left.global.trans right.global, left.outputs.trans right.outputs, left.inputs.trans right.inputs⟩

private theorem decode_components {psbt : Psbt} {decoded : DecodedPsbt}
    (read : psbt.decode = .ok decoded) :
    decodeGlobal psbt.global = .ok decoded.global ∧
      psbt.inputs.mapM (decodeInput decoded.global.psbtVersion) = .ok decoded.inputs ∧
      psbt.outputs.mapM (decodeOutput decoded.global.psbtVersion) = .ok decoded.outputs := by
  unfold Psbt.decode at read
  rw [bind_eq_ok] at read
  rcases read with ⟨global, globalRead, read⟩
  split at read
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at read
  · rw [bind_eq_ok] at read
    rcases read with ⟨inputs, inputsRead, read⟩
    rw [bind_eq_ok] at read
    rcases read with ⟨outputs, outputsRead, read⟩
    cases read
    exact ⟨globalRead, inputsRead, outputsRead⟩

private theorem decode_context_of_maps {left right : Psbt} {before after : DecodedPsbt}
    (global : left.global = right.global) (outputs : left.outputs = right.outputs)
    (length : left.inputs.length = right.inputs.length)
    (maps : ∀ (index : Nat) (a b : KeyValueMap), left.inputs[index]? = some a → right.inputs[index]? = some b →
      ∀ (version : Nat) (x y : InputFields), decodeInput version a = .ok x → decodeInput version b = .ok y →
        x.context = y.context)
    (read : left.decode = .ok before) (written : right.decode = .ok after) :
    before.SameContext after := by
  obtain ⟨globalRead, inputsRead, outputsRead⟩ := decode_components read
  obtain ⟨globalWritten, inputsWritten, outputsWritten⟩ := decode_components written
  have sameGlobal : before.global = after.global := by
    rw [global] at globalRead
    exact Except.ok.inj (globalRead.symm.trans globalWritten)
  have sameOutputs : before.outputs = after.outputs := by
    rw [outputs, sameGlobal] at outputsRead
    exact Except.ok.inj (outputsRead.symm.trans outputsWritten)
  refine ⟨sameGlobal, sameOutputs, List.ext_getElem? fun index => ?_⟩
  have leftLength := length_of_mapM_ok inputsRead
  have rightLength := length_of_mapM_ok inputsWritten
  by_cases range : index < left.inputs.length
  · have rightRange : index < right.inputs.length := by omega
    have found := List.getElem?_eq_getElem range
    have found' := List.getElem?_eq_getElem rightRange
    obtain ⟨input, selected, inputRead⟩ := getElem?_of_mapM_ok inputsRead found
    obtain ⟨input', selected', inputWritten⟩ := getElem?_of_mapM_ok inputsWritten found'
    rw [sameGlobal] at inputRead
    simp only [List.getElem?_map, selected, selected', Option.map_some]
    exact congrArg some (maps index _ _ found found' _ _ _ inputRead inputWritten)
  · have beforeRange : before.inputs.length ≤ index := by omega
    have afterRange : after.inputs.length ≤ index := by omega
    simp [List.getElem?_eq_none_iff.mpr beforeRange, List.getElem?_eq_none_iff.mpr afterRange]

/-- Finalizing one input preserves the decoded transaction and UTXO fields. -/
theorem Psbt.finalizeInput_context {config : FinalizerConfig} {psbt result : Psbt}
    {index : Nat} {descriptor : OutputDescriptor} {before after : DecodedPsbt}
    (read : psbt.decode = .ok before) (written : result.decode = .ok after)
    (finalized : psbt.finalizeInput config index descriptor = .ok result) :
    before.SameContext after := by
  obtain ⟨_, _, _, _, outcome⟩ := Psbt.finalizeInput_spec finalized
  rcases outcome with ⟨_, rfl⟩ | ⟨final, _, _, rfl⟩
  · have same := Except.ok.inj (read.symm.trans written)
    subst after
    exact .refl before
  · apply decode_context_of_maps (left := psbt)
      (right := { psbt with inputs := psbt.inputs.modify index (finalizedInputMap · final) })
      rfl rfl (by simp) ?_ read written
    intro i a b found found' version x y hx hy
    by_cases same : index = i
    · simp [found, same] at found'
      subst b
      exact decodeInput_finalizedInputMap_context hx hy
    · simp [found, same] at found'
      subst b
      have equal := Except.ok.inj (hx.symm.trans hy)
      subst y
      rfl

private theorem finalize_fold_context (config : FinalizerConfig)
    (jobs : List (Option OutputDescriptor × Nat)) {psbt result : Psbt} {before after : DecodedPsbt}
    (read : psbt.decode = .ok before) (written : result.decode = .ok after)
    (finalized : jobs.foldlM (fun stage job => match job.1 with
      | none => pure stage
      | some descriptor => stage.finalizeInput config job.2 descriptor) psbt = .ok result) :
    before.SameContext after := by
  induction jobs generalizing psbt before with
  | nil =>
    cases finalized
    have same := Except.ok.inj (read.symm.trans written)
    subst after
    exact .refl before
  | cons job rest ih =>
    rcases job with ⟨descriptor, index⟩
    cases descriptor with
    | none =>
      simp only [List.foldlM_cons, pure, Except.pure, bind, Except.bind] at finalized
      exact ih read finalized
    | some descriptor =>
      rw [List.foldlM_cons, bind_eq_ok] at finalized
      rcases finalized with ⟨next, step, finalized⟩
      obtain ⟨decoded, nextRead⟩ := Psbt.finalizeInput_decodes step
      exact (Psbt.finalizeInput_context read nextRead step).trans (ih nextRead finalized)

/-- Every stage of whole-PSBT finalization preserves the transaction and UTXO fields. -/
theorem Psbt.finalize_context {config : FinalizerConfig} {psbt result : Psbt}
    {descriptors : List (Option OutputDescriptor)} {before after : DecodedPsbt}
    (read : psbt.decode = .ok before) (written : result.decode = .ok after)
    (finalized : psbt.finalize config descriptors = .ok result) :
    before.SameContext after :=
  finalize_fold_context config descriptors.zipIdx read written finalized

private def contextLocktime (fallback : Option UInt32) (inputs : List InputContext) : Option UInt32 :=
  let constrained := inputs.filter (fun input =>
    input.requiredTimeLocktime.isSome || input.requiredHeightLocktime.isSome)
  if constrained.isEmpty then some (fallback.getD 0)
  else if constrained.all (fun input => input.requiredHeightLocktime.isSome) then
    some (constrained.foldl (fun best input => max best (input.requiredHeightLocktime.getD 0)) 0)
  else if constrained.all (fun input => input.requiredTimeLocktime.isSome) then
    some (constrained.foldl (fun best input => max best (input.requiredTimeLocktime.getD 0)) 0)
  else none

private theorem determineLocktime_context (fallback : Option UInt32) (inputs : List InputFields) :
    determineLocktime fallback inputs = contextLocktime fallback (inputs.map InputFields.context) := by
  simp [determineLocktime, contextLocktime, List.filter_map, List.all_map, List.foldl_map,
    InputFields.context, Function.comp_def]

private def InputContext.txInput (input : InputContext) : TxInput :=
  { previousOutput := { txid := input.previousTxid.getD ByteArray.empty,
                        index := input.outputIndex.getD 0 }
    sequence := input.sequence.getD 0xffffffff }

/-- The unsigned transaction is identical, including v2 input fields and determined locktime. -/
theorem DecodedPsbt.SameContext.unsignedTransaction {before after : DecodedPsbt}
    (same : before.SameContext after) : before.unsignedTransaction = after.unsignedTransaction := by
  have inputs := congrArg (List.map InputContext.txInput) same.inputs
  simp only [List.map_map, Function.comp_def, InputContext.txInput, InputFields.context] at inputs
  unfold DecodedPsbt.unsignedTransaction
  rw [same.global, same.outputs, determineLocktime_context, determineLocktime_context, same.inputs]
  simp only [inputs]

theorem DecodedPsbt.SameContext.spentOutput {before after : DecodedPsbt}
    (same : before.SameContext after) (index : Nat) :
    before.spentOutput index = after.spentOutput index := by
  have inputs := congrArg (fun xs => xs[index]?) same.inputs
  simp only [List.getElem?_map] at inputs
  unfold DecodedPsbt.spentOutput DecodedPsbt.input
  rw [same.unsignedTransaction]
  cases left : before.inputs[index]? <;> cases right : after.inputs[index]? <;>
    simp only [left, right, Option.map_none, Option.map_some, Option.some.injEq,
      Option.some_ne_none] at inputs
  all_goals first
    | contradiction
    | rfl
    | skip
  simp only [InputFields.context, InputContext.mk.injEq] at inputs
  simp only [bind, Except.bind]
  rcases inputs with ⟨utxo, witness, _⟩
  rw [utxo, witness]

theorem DecodedPsbt.SameContext.spentOutputs {before after : DecodedPsbt}
    (same : before.SameContext after) : before.spentOutputs = after.spentOutputs := by
  have length := congrArg List.length same.inputs
  simp only [List.length_map] at length
  have spent : before.spentOutput = after.spentOutput := funext same.spentOutput
  simp only [DecodedPsbt.spentOutputs, length, spent]

/-- Finalization preserves both the unsigned transaction and every resolved UTXO. -/
theorem Psbt.finalize_preserves_transaction {config : FinalizerConfig} {psbt result : Psbt}
    {descriptors : List (Option OutputDescriptor)} {before after : DecodedPsbt}
    (read : psbt.decode = .ok before) (written : result.decode = .ok after)
    (finalized : psbt.finalize config descriptors = .ok result) :
    before.unsignedTransaction = after.unsignedTransaction ∧
      before.spentOutputs = after.spentOutputs := by
  have same := Psbt.finalize_context read written finalized
  exact ⟨same.unsignedTransaction, same.spentOutputs⟩

end LeanMiniscript.Psbt
