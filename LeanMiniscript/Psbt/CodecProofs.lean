import LeanMiniscript.Psbt.Codec
import LeanMiniscript.Bitcoin.DeserializationProofs

namespace LeanMiniscript.Psbt

open LeanMiniscript.Bitcoin

/-! Exact re-reading of serialized key-value maps and PSBT framing. The
whole-PSBT theorem is parameterized by the function deriving map counts from
the global map; `Psbt.Fields` instantiates it with BIP174/BIP370 counts. -/

private theorem liftDecode_ok {α : Type} (value : α) :
    liftDecode (.ok value : Except DecodeError α) = .ok value := rfl

private theorem readCompactSize_zero (rest : List UInt8) :
    readCompactSize (0 :: rest) = .ok (0, rest) := rfl

theorem Record.encode_length_pos (record : Record) : 0 < record.encode.length := by
  unfold Record.encode encodeByteVector
  have := compactSize_ne_nil record.key.size
  cases h : compactSize record.key.size with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem KeyValueMap.length_lt_encode_length (map : KeyValueMap) :
    map.length < map.encode.length := by
  induction map with
  | nil => simp [KeyValueMap.encode]
  | cons record records ih =>
    have := record.encode_length_pos
    simp only [KeyValueMap.encode, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    omega

/-- A well-formed map reads back exactly, with any suffix left unread, for any
fuel exceeding its record count. -/
theorem decodeMapFuel_encode {map : KeyValueMap} (wellFormed : map.WellFormed)
    {fuel : Nat} (enough : map.length < fuel) (rest : List UInt8) :
    decodeMapFuel fuel (map.encode ++ rest) = .ok (map, rest) := by
  induction map generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp [decodeMapFuel, KeyValueMap.encode, readCompactSize_zero, liftDecode_ok,
        bind, Except.bind, pure, Except.pure]
  | cons record records ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      obtain ⟨formed, unique⟩ := wellFormed
      have recordFormed := formed record (by simp)
      obtain ⟨keyPos, keyBound, valueBound⟩ := recordFormed
      have tailFormed : KeyValueMap.WellFormed records :=
        ⟨fun r member => formed r (by simp [member]), (List.nodup_cons.mp unique).2⟩
      have fresh : record.key ∉ records.map Record.key := (List.nodup_cons.mp unique).1
      have tail := ih tailFormed (fuel := fuel) (by simp at enough; omega)
      have keyLength : record.key.data.toList.length = record.key.size := by simp
      have taken := takeExact_append record.key.data.toList
        (encodeByteVector record.value ++ (KeyValueMap.encode records ++ rest))
      rw [keyLength] at taken
      have keyNonzero : record.key.size ≠ 0 := by omega
      have absent : records.any (fun r => decide (r.key = record.key)) = false := by
        simp only [List.any_eq_false, decide_eq_true_eq]
        intro r member same
        exact fresh (same ▸ List.mem_map_of_mem member)
      have shape : KeyValueMap.encode (record :: records) ++ rest =
          compactSize record.key.size ++ (record.key.data.toList ++
            (encodeByteVector record.value ++ (KeyValueMap.encode records ++ rest))) := by
        simp [KeyValueMap.encode, Record.encode, encodeByteVector]
      rw [shape]
      simp only [decodeMapFuel, readCompactSize_compactSize keyBound, liftDecode_ok,
        bind, Except.bind, keyNonzero, if_false, taken,
        readByteVector_encode valueBound, tail]
      have rebuilt : (⟨record.key.data.toList.toArray⟩ : ByteArray) = record.key := by simp
      simp only [rebuilt, absent]
      rfl

theorem decodeMap_encode {map : KeyValueMap} (wellFormed : map.WellFormed)
    (rest : List UInt8) :
    decodeMap (map.encode ++ rest) = .ok (map, rest) := by
  unfold decodeMap
  apply decodeMapFuel_encode wellFormed
  have := map.length_lt_encode_length
  simp only [List.length_append]
  omega

theorem decodeMaps_encode {maps : List KeyValueMap}
    (wellFormed : ∀ map ∈ maps, map.WellFormed) (rest : List UInt8) :
    decodeMaps maps.length (maps.flatMap KeyValueMap.encode ++ rest) = .ok (maps, rest) := by
  induction maps with
  | nil => rfl
  | cons map maps ih =>
    have tail := ih (fun m member => wellFormed m (by simp [member]))
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeMaps,
      decodeMap_encode (wellFormed map (by simp)), bind, Except.bind, tail]
    rfl

/-- Serialized well-formed PSBTs read back exactly whenever the count function
agrees with the stored input and output maps. -/
theorem decodePsbtWith_encode
    (counts : KeyValueMap → Except PsbtError (Nat × Nat)) {psbt : Psbt}
    (wellFormed : psbt.WellFormed)
    (counted : counts psbt.global = .ok (psbt.inputs.length, psbt.outputs.length)) :
    decodePsbtWith counts psbt.encode = .ok psbt := by
  obtain ⟨globalFormed, inputsFormed, outputsFormed⟩ := wellFormed
  have global := decodeMap_encode globalFormed
    (psbt.inputs.flatMap KeyValueMap.encode ++ psbt.outputs.flatMap KeyValueMap.encode)
  have inputs := decodeMaps_encode inputsFormed (psbt.outputs.flatMap KeyValueMap.encode)
  have outputs := decodeMaps_encode outputsFormed []
  simp only [List.append_nil] at outputs
  have header : psbt.encode.take 5 = magicBytes := by simp [Psbt.encode, magicBytes]
  have body : psbt.encode.drop 5 = psbt.global.encode ++
      (psbt.inputs.flatMap KeyValueMap.encode ++ psbt.outputs.flatMap KeyValueMap.encode) := by
    simp [Psbt.encode, magicBytes]
  simp only [decodePsbtWith, header, body, ne_eq, not_true_eq_false, if_false, global,
    bind, Except.bind, counted, inputs, outputs]
  rfl

theorem Psbt.serialize_data (psbt : Psbt) : psbt.serialize.data.toList = psbt.encode := by
  simp [Psbt.serialize]

/-! ## Accepted bytes are canonical

The reader accepts only the serialization of what it returns, and what it
returns is well formed. Together with `decodePsbtWith_encode`, framing is a
bijection between accepted byte strings and well-formed maps. -/

private theorem liftDecode_eq_ok {α : Type} {result : Except DecodeError α} {value : α}
    (lifted : liftDecode result = .ok value) : result = .ok value := by
  cases result <;> simp_all [liftDecode, Except.mapError]

theorem decodeMapFuel_ok {fuel : Nat} {bytes rest : List UInt8} {map : KeyValueMap}
    (read : decodeMapFuel fuel bytes = .ok (map, rest)) :
    bytes = map.encode ++ rest ∧ map.WellFormed := by
  induction fuel generalizing bytes map rest with
  | zero => simp [decodeMapFuel] at read
  | succ fuel ih =>
    unfold decodeMapFuel at read
    cases lengthRead : liftDecode (readCompactSize bytes) with
    | error error => simp [lengthRead, bind, Except.bind] at read
    | ok pair =>
      obtain ⟨keyLength, afterLength⟩ := pair
      obtain ⟨lengthSplit, _⟩ := readCompactSize_ok (liftDecode_eq_ok lengthRead)
      simp only [lengthRead, bind, Except.bind] at read
      by_cases empty : keyLength = 0
      · simp only [empty, if_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        subst empty
        refine ⟨by simpa [KeyValueMap.encode, compactSize] using lengthSplit, ?_, ?_⟩
        · simp
        · simp [KeyValueMap.Unique]
      · simp only [empty, if_false] at read
        cases keyRead : liftDecode (takeExact keyLength afterLength) with
        | error error => simp [keyRead] at read
        | ok pair =>
          obtain ⟨keyBytes, afterKey⟩ := pair
          obtain ⟨keySplit, keyLengthEq⟩ := takeExact_ok (liftDecode_eq_ok keyRead)
          simp only [keyRead] at read
          cases valueRead : liftDecode (readByteVector afterKey) with
          | error error => simp [valueRead] at read
          | ok pair =>
            obtain ⟨value, afterValue⟩ := pair
            obtain ⟨valueSplit, valueBound⟩ := readByteVector_ok (liftDecode_eq_ok valueRead)
            simp only [valueRead] at read
            cases tailRead : decodeMapFuel fuel afterValue with
            | error error => simp [tailRead] at read
            | ok pair =>
              obtain ⟨records, afterRecords⟩ := pair
              obtain ⟨tailSplit, tailFormed⟩ := ih tailRead
              simp only [tailRead] at read
              split at read
              · simp [throw, throwThe, MonadExceptOf.throw] at read
              · rename_i fresh
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
                obtain ⟨rfl, rfl⟩ := read
                have keySize : (⟨keyBytes.toArray⟩ : ByteArray).size = keyLength := by
                  simp [ByteArray.size, keyLengthEq]
                refine ⟨?_, ?_, ?_⟩
                · simp only [KeyValueMap.encode, List.flatMap_cons, Record.encode,
                    encodeByteVector, keySize] at tailSplit ⊢
                  rw [lengthSplit, keySplit, valueSplit, tailSplit]
                  simp [encodeByteVector]
                · intro record member
                  rcases List.mem_cons.mp member with same | inTail
                  · subst same
                    have := (readCompactSize_ok (liftDecode_eq_ok lengthRead)).2
                    exact ⟨by simp [keySize]; omega, by rw [keySize]; exact this,
                      valueBound⟩
                  · exact tailFormed.1 record inTail
                · unfold KeyValueMap.Unique
                  rw [List.map_cons, List.nodup_cons]
                  refine ⟨?_, tailFormed.2⟩
                  intro inTail
                  obtain ⟨other, member, same⟩ := List.mem_map.mp inTail
                  apply fresh
                  simp only [List.any_eq_true, decide_eq_true_eq]
                  exact ⟨other, member, same⟩

theorem decodeMap_ok {bytes rest : List UInt8} {map : KeyValueMap}
    (read : decodeMap bytes = .ok (map, rest)) : bytes = map.encode ++ rest ∧ map.WellFormed :=
  decodeMapFuel_ok read

theorem decodeMaps_ok {count : Nat} {bytes rest : List UInt8} {maps : List KeyValueMap}
    (read : decodeMaps count bytes = .ok (maps, rest)) :
    bytes = maps.flatMap KeyValueMap.encode ++ rest ∧ maps.length = count ∧
      ∀ map ∈ maps, map.WellFormed := by
  induction count generalizing bytes maps rest with
  | zero =>
    simp only [decodeMaps, Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    simp
  | succ count ih =>
    unfold decodeMaps at read
    cases first : decodeMap bytes with
    | error error => simp [first, bind, Except.bind] at read
    | ok pair =>
      obtain ⟨map, afterMap⟩ := pair
      obtain ⟨mapSplit, mapFormed⟩ := decodeMap_ok first
      simp only [first, bind, Except.bind] at read
      cases others : decodeMaps count afterMap with
      | error error => simp [others] at read
      | ok pair =>
        obtain ⟨maps', afterMaps⟩ := pair
        obtain ⟨mapsSplit, mapsLength, mapsFormed⟩ := ih others
        simp only [others, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        refine ⟨by simp [mapSplit, mapsSplit], by simp [mapsLength], ?_⟩
        intro m member
        rcases List.mem_cons.mp member with same | inTail
        · exact same ▸ mapFormed
        · exact mapsFormed m inTail

/-- Accepted bytes are exactly the serialization of the decoded maps, and
the decoded maps are well formed and agree with the count function. -/
theorem decodePsbtWith_ok (counts : KeyValueMap → Except PsbtError (Nat × Nat))
    {bytes : List UInt8} {psbt : Psbt} (read : decodePsbtWith counts bytes = .ok psbt) :
    bytes = psbt.encode ∧ psbt.WellFormed ∧
      counts psbt.global = .ok (psbt.inputs.length, psbt.outputs.length) := by
  unfold decodePsbtWith at read
  split at read
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at read
  · rename_i header
    simp only [ne_eq, Decidable.not_not] at header
    cases globalRead : decodeMap (bytes.drop 5) with
    | error error => simp [globalRead, bind, Except.bind] at read
    | ok pair =>
      obtain ⟨global, afterGlobal⟩ := pair
      obtain ⟨globalSplit, globalFormed⟩ := decodeMap_ok globalRead
      simp only [globalRead, bind, Except.bind] at read
      cases counted : counts global with
      | error error => simp [counted] at read
      | ok pair =>
        obtain ⟨inputCount, outputCount⟩ := pair
        simp only [counted] at read
        cases inputsRead : decodeMaps inputCount afterGlobal with
        | error error => simp [inputsRead] at read
        | ok pair =>
          obtain ⟨inputs, afterInputs⟩ := pair
          obtain ⟨inputsSplit, inputsLength, inputsFormed⟩ := decodeMaps_ok inputsRead
          simp only [inputsRead] at read
          cases outputsRead : decodeMaps outputCount afterInputs with
          | error error => simp [outputsRead] at read
          | ok pair =>
            obtain ⟨outputs, afterOutputs⟩ := pair
            obtain ⟨outputsSplit, outputsLength, outputsFormed⟩ := decodeMaps_ok outputsRead
            simp only [outputsRead] at read
            split at read
            · simp [throw, throwThe, MonadExceptOf.throw] at read
            · rename_i finished
              simp only [ne_eq, Decidable.not_not] at finished
              simp only [pure, Except.pure, Except.ok.injEq] at read
              subst read
              refine ⟨?_, ⟨globalFormed, inputsFormed, outputsFormed⟩, ?_⟩
              · rw [← List.take_append_drop 5 bytes, header, globalSplit, inputsSplit,
                  outputsSplit, finished]
                simp [Psbt.encode]
              · simp [counted, inputsLength, outputsLength]

end LeanMiniscript.Psbt
