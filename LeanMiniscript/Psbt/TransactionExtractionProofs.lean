import LeanMiniscript.Psbt.FinalizedFieldsProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-- Typed decoding preserves the input count and the global map. -/
theorem Psbt.decode_shape {psbt : Psbt} {decoded : DecodedPsbt}
    (read : psbt.decode = .ok decoded) :
    decodeGlobal psbt.global = .ok decoded.global ∧
      decoded.global.counts = (psbt.inputs.length, psbt.outputs.length) ∧
      decoded.inputs.length = psbt.inputs.length := by
  unfold Psbt.decode at read
  cases hg : decodeGlobal psbt.global with
  | error error => simp [hg, bind, Except.bind] at read
  | ok global =>
    simp only [hg, bind, Except.bind] at read
    split at read
    · simp [throw, throwThe, MonadExceptOf.throw] at read
    · rename_i counts
      cases hi : psbt.inputs.mapM (decodeInput global.psbtVersion) with
      | error error => simp [hi] at read
      | ok inputs =>
        simp only [hi] at read
        cases ho : psbt.outputs.mapM (decodeOutput global.psbtVersion) with
        | error error => simp [ho] at read
        | ok outputs =>
          simp only [ho, pure, Except.pure, Except.ok.injEq] at read
          subst decoded
          exact ⟨rfl, by simpa using counts, length_of_mapM_ok hi⟩

theorem Psbt.unsignedTransaction_inputCount {psbt : Psbt} {decoded : DecodedPsbt}
    {tx : Transaction} (read : psbt.decode = .ok decoded)
    (unsigned : decoded.unsignedTransaction = .ok tx) :
    tx.inputs.size = decoded.inputs.length := by
  obtain ⟨_, counts, length⟩ := Psbt.decode_shape read
  unfold DecodedPsbt.unsignedTransaction at unsigned
  cases stored : decoded.global.unsignedTx with
  | some original =>
    simp only [stored, Except.ok.injEq] at unsigned
    subst tx
    simpa [GlobalFields.counts, stored, length] using congrArg Prod.fst counts
  | none =>
    simp only [stored] at unsigned
    split at unsigned
    · contradiction
    · cases unsigned; simp

private theorem getElem?_zip_some {α β : Type} {xs : List α} {ys : List β}
    {index : Nat} {x : α} {y : β}
    (hx : xs[index]? = some x) (hy : ys[index]? = some y) :
    (xs.zip ys)[index]? = some (x, y) := by
  induction xs generalizing ys index with
  | nil => simp at hx
  | cons head tail ih =>
    cases ys with
    | nil => simp at hy
    | cons other rest =>
      cases index with
      | zero => simpa using And.intro hx hy
      | succ index => exact ih hx hy

/-- The extractor reads one final pair per decoded input before assembling
transaction inputs. This stage requires no unsigned-input count assumption. -/
private theorem finalTransaction_parts {decoded : DecodedPsbt} {tx : WitnessTransaction}
    (extracted : decoded.finalTransaction = .ok tx) :
    ∃ (unsigned : Transaction) (finals : List (ByteArray × List ByteArray)),
      decoded.unsignedTransaction = .ok unsigned ∧
      finals.length = decoded.inputs.length ∧
      (∀ (index : Nat) (input : InputFields), decoded.inputs[index]? = some input →
        input.isFinalized = true ∧
          finals[index]? = some (input.finalInput.scriptSig, input.finalInput.witness)) ∧
      tx = {
        transaction := { unsigned with inputs := ((unsigned.inputs.toList.zip finals).map
          (fun pair => { pair.1 with scriptSig := pair.2.1 })).toArray }
        witnesses := finals.map (·.2) } := by
  unfold DecodedPsbt.finalTransaction at extracted
  rw [bind_eq_ok] at extracted
  rcases extracted with ⟨unsigned, read, extracted⟩
  have unsignedEq : decoded.unsignedTransaction = .ok unsigned := by
    cases h : decoded.unsignedTransaction <;> simp_all [liftPsbt, Except.mapError]
  rw [bind_eq_ok] at extracted
  rcases extracted with ⟨finals, computed, extracted⟩
  refine ⟨unsigned, finals, unsignedEq, ?_, ?_, (Except.ok.inj extracted).symm⟩
  · simpa using length_of_mapM_ok computed
  · intro index input found
    have range : index < decoded.inputs.length := (List.getElem?_eq_some_iff.mp found).1
    have rangeFound : (List.range decoded.inputs.length)[index]? = some index := by simp [range]
    obtain ⟨pair, selected, result⟩ := getElem?_of_mapM_ok computed rangeFound
    simp only [DecodedPsbt.input, found, bind, Except.bind, pure, Except.pure] at result
    split at result
    · simp [throw, throwThe, MonadExceptOf.throw] at result
    · rename_i ready
      simp only [Except.ok.injEq] at result
      subst pair
      refine ⟨?_, selected⟩
      cases hs : input.finalScriptSig <;> cases hw : input.finalScriptWitness <;>
        simp_all [InputFields.isFinalized]

/-- Extraction copies the decoded witness at each input index. -/
theorem DecodedPsbt.finalTransaction_witness {decoded : DecodedPsbt}
    {tx : WitnessTransaction} {index : Nat} {input : InputFields}
    (extracted : decoded.finalTransaction = .ok tx)
    (found : decoded.inputs[index]? = some input) :
    tx.witnesses[index]? = some (input.finalScriptWitness.getD []) := by
  obtain ⟨unsigned, finals, _, _, fields, rfl⟩ := finalTransaction_parts extracted
  simp [List.getElem?_map, (fields index input found).2, InputFields.finalInput]

/-- Extraction preserves transaction fields and fills every input's
scriptSig and witness from its decoded final fields. -/
theorem DecodedPsbt.finalTransaction_spec {decoded : DecodedPsbt} {tx : WitnessTransaction}
    (counted : ∀ unsigned, decoded.unsignedTransaction = .ok unsigned →
      unsigned.inputs.size = decoded.inputs.length)
    (extracted : decoded.finalTransaction = .ok tx) :
    ∃ unsigned, decoded.unsignedTransaction = .ok unsigned ∧
      tx.transaction.version = unsigned.version ∧
      tx.transaction.outputs = unsigned.outputs ∧
      tx.transaction.locktime = unsigned.locktime ∧
      tx.transaction.inputs.size = decoded.inputs.length ∧
      tx.witnesses.length = decoded.inputs.length ∧
      ∀ (index : Nat) (input : InputFields), decoded.inputs[index]? = some input →
        input.isFinalized = true ∧
        (∃ original : TxInput, unsigned.inputs[index]? = some original ∧
          tx.transaction.inputs[index]? = some
            { original with scriptSig := input.finalInput.scriptSig }) ∧
        tx.witnesses[index]? = some input.finalInput.witness := by
  obtain ⟨unsigned, finals, unsignedEq, length, fields, rfl⟩ := finalTransaction_parts extracted
  have count := counted unsigned unsignedEq
  refine ⟨unsigned, unsignedEq, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [count, length]
  · simp [length]
  · intro index input found
    have range : index < decoded.inputs.length := (List.getElem?_eq_some_iff.mp found).1
    obtain ⟨ready, selected⟩ := fields index input found
    have original : unsigned.inputs.toList[index]? = some unsigned.inputs[index] := by
      simp [show index < unsigned.inputs.size by omega]
    refine ⟨ready, ⟨unsigned.inputs[index], ?_, ?_⟩, ?_⟩
    · simp
    · simp only [List.getElem?_toArray, List.getElem?_map,
        getElem?_zip_some original selected, Option.map_some]
    · simp [List.getElem?_map, selected]

/-- Successful extraction returns exactly the serialized final transaction. -/
theorem Psbt.extract_spec {psbt : Psbt} {bytes : ByteArray}
    (extracted : psbt.extract = .ok bytes) :
    ∃ decoded tx, psbt.decode = .ok decoded ∧ decoded.finalTransaction = .ok tx ∧
      bytes = serializeWitnessTransaction tx.transaction tx.witnesses := by
  unfold Psbt.extract at extracted
  cases hd : psbt.decode with
  | error error => simp [hd, liftPsbt, Except.mapError, bind, Except.bind] at extracted
  | ok decoded =>
    simp only [hd, liftPsbt, Except.mapError, bind, Except.bind] at extracted
    cases ht : decoded.finalTransaction with
    | error error => simp [ht] at extracted
    | ok tx =>
      simp only [ht, pure, Except.pure, Except.ok.injEq] at extracted
      exact ⟨decoded, tx, rfl, ht, extracted.symm⟩

end LeanMiniscript.Psbt
