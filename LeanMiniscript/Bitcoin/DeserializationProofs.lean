import LeanMiniscript.Bitcoin.Deserialization

namespace LeanMiniscript.Bitcoin

/-! Round trips for the fixed-width, CompactSize and byte-vector readers. -/

theorem unsignedLE_length (width value : Nat) : (unsignedLE width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [unsignedLE, ih]

theorem decodeLE_unsignedLE (width value : Nat) :
    decodeLE (unsignedLE width value) = value % 256 ^ width := by
  induction width generalizing value with
  | zero => simp [unsignedLE, decodeLE, Nat.mod_one]
  | succ width ih =>
    have byte : (UInt8.ofNat value).toNat = value % 256 := UInt8.toNat_ofNat'
    simp only [unsignedLE, decodeLE, ih, byte]
    rw [Nat.pow_succ', Nat.mod_mul]

theorem takeExact_append (bytes rest : List UInt8) :
    takeExact bytes.length (bytes ++ rest) = .ok (bytes, rest) := by
  simp [takeExact]

theorem compactSize_ne_nil (value : Nat) : compactSize value ≠ [] := by
  unfold compactSize
  split <;> (try split) <;> (try split) <;> simp

/-- Every value representable by Core's uint64 CompactSize reads back exactly,
including the canonical-width check. -/
theorem readCompactSize_compactSize {value : Nat} (bound : value < 2 ^ 64)
    (rest : List UInt8) :
    readCompactSize (compactSize value ++ rest) = .ok (value, rest) := by
  unfold compactSize
  by_cases small : value < 253
  · have : value % 256 = value := Nat.mod_eq_of_lt (by omega)
    simp [small, readCompactSize, this]
  · by_cases two : value ≤ 65535
    · have length := unsignedLE_length 2 value
      have decoded : decodeLE (unsignedLE 2 value) = value := by
        rw [decodeLE_unsignedLE]; exact Nat.mod_eq_of_lt (by omega)
      have taken := takeExact_append (unsignedLE 2 value) rest
      rw [length] at taken
      simp only [small, two, if_false, if_true, List.cons_append, readCompactSize]
      simp [taken, decoded, small]
    · by_cases four : value ≤ 4294967295
      · have length := unsignedLE_length 4 value
        have decoded : decodeLE (unsignedLE 4 value) = value := by
          rw [decodeLE_unsignedLE]; exact Nat.mod_eq_of_lt (by omega)
        have taken := takeExact_append (unsignedLE 4 value) rest
        rw [length] at taken
        simp only [small, two, four, if_false, if_true, List.cons_append, readCompactSize]
        have notMinimal : ¬ value < 65536 := by omega
        simp [taken, decoded, notMinimal]
      · have length := unsignedLE_length 8 value
        have decoded : decodeLE (unsignedLE 8 value) = value := by
          rw [decodeLE_unsignedLE]; exact Nat.mod_eq_of_lt (by omega)
        have taken := takeExact_append (unsignedLE 8 value) rest
        rw [length] at taken
        simp only [small, two, four, if_false, List.cons_append, readCompactSize]
        have notMinimal : ¬ value < 4294967296 := by omega
        simp [taken, decoded, notMinimal]

theorem serializeByteVector_data (bytes : ByteArray) :
    (serializeByteVector bytes).data.toList = encodeByteVector bytes := by
  simp [serializeByteVector, encodeByteVector, ByteArray.data_append]

theorem readByteVector_encode {bytes : ByteArray} (bound : bytes.size < 2 ^ 64)
    (rest : List UInt8) :
    readByteVector (encodeByteVector bytes ++ rest) = .ok (bytes, rest) := by
  have taken := takeExact_append bytes.data.toList rest
  have length : bytes.data.toList.length = bytes.size := by simp
  rw [length] at taken
  unfold readByteVector encodeByteVector
  rw [List.append_assoc, readCompactSize_compactSize bound]
  simp only [taken]

/-! ## Accepted encodings are canonical

Every successful read consumed exactly the canonical encoding of its result,
so re-serializing a read value reproduces the consumed bytes. -/

theorem decodeLE_lt (bytes : List UInt8) : decodeLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [decodeLE]
  | cons byte rest ih =>
    have := byte.toNat_lt
    simp only [decodeLE, List.length_cons, Nat.pow_succ']
    omega

theorem unsignedLE_decodeLE (bytes : List UInt8) :
    unsignedLE bytes.length (decodeLE bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have small := byte.toNat_lt
    have low : (UInt8.ofNat (byte.toNat + 256 * decodeLE rest)) = byte := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      omega
    have high : (byte.toNat + 256 * decodeLE rest) / 256 = decodeLE rest := by omega
    simp only [List.length_cons, unsignedLE, decodeLE, low, high, ih]

theorem takeExact_ok {count : Nat} {bytes taken rest : List UInt8}
    (read : takeExact count bytes = .ok (taken, rest)) :
    bytes = taken ++ rest ∧ taken.length = count := by
  unfold takeExact at read
  split at read
  · rename_i enough
    simp only [Except.ok.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨(List.take_append_drop count bytes).symm, by simp; omega⟩
  · simp at read

/-- A successful CompactSize read consumed the canonical encoding of the
value, which is below 2^64. -/
theorem readCompactSize_ok {bytes rest : List UInt8} {value : Nat}
    (read : readCompactSize bytes = .ok (value, rest)) :
    bytes = compactSize value ++ rest ∧ value < 2 ^ 64 := by
  cases bytes with
  | nil => simp [readCompactSize] at read
  | cons tag tail =>
    have tagBound := tag.toNat_lt
    unfold readCompactSize at read
    by_cases small : tag.toNat < 253
    · simp only [small, if_true, Except.ok.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      have tagEq : UInt8.ofNat tag.toNat = tag := UInt8.ofNat_toNat
      refine ⟨?_, by omega⟩
      simp [compactSize, small, tagEq]
    · simp only [small, if_false] at read
      cases takenEq : takeExact (if tag.toNat = 253 then 2 else if tag.toNat = 254 then 4 else 8)
          tail with
      | error error => simp [takenEq] at read
      | ok pair =>
        obtain ⟨taken, after⟩ := pair
        simp only [takenEq] at read
        obtain ⟨split, length⟩ := takeExact_ok takenEq
        have roundTrip := unsignedLE_decodeLE taken
        have bound := decodeLE_lt taken
        subst split
        by_cases two : tag.toNat = 253
        · simp only [two, if_true] at length read
          rw [length] at roundTrip bound
          by_cases low : decodeLE taken < 253
          · simp [low] at read
          · simp only [low, if_false, Except.ok.injEq, Prod.mk.injEq] at read
            obtain ⟨rfl, rfl⟩ := read
            have tagEq : tag = 0xfd := UInt8.toNat_inj.mp (by simpa using two)
            refine ⟨?_, by omega⟩
            simp only [compactSize]
            rw [if_neg (by omega), if_pos (by omega), roundTrip, tagEq]
            rfl
        · by_cases four : tag.toNat = 254
          · have notTwo : (254 : Nat) ≠ 253 := by decide
            simp only [four, notTwo, if_false, if_true] at length read
            rw [length] at roundTrip bound
            by_cases low : decodeLE taken < 65536
            · simp [low] at read
            · simp only [low, if_false, Except.ok.injEq, Prod.mk.injEq] at read
              obtain ⟨rfl, rfl⟩ := read
              have tagEq : tag = 0xfe := UInt8.toNat_inj.mp (by simpa using four)
              refine ⟨?_, by omega⟩
              simp only [compactSize]
              rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), roundTrip, tagEq]
              rfl
          · simp only [two, four, if_false] at length
            simp only [two, four, if_false] at read
            rw [length] at roundTrip bound
            by_cases low : decodeLE taken < 4294967296
            · simp [low] at read
            · simp only [low, if_false, Except.ok.injEq, Prod.mk.injEq] at read
              obtain ⟨rfl, rfl⟩ := read
              have tagEq : tag = 0xff := UInt8.toNat_inj.mp (by simp; omega)
              refine ⟨?_, by omega⟩
              simp only [compactSize]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), roundTrip, tagEq]
              rfl

theorem readByteVector_ok {bytes rest : List UInt8} {vector : ByteArray}
    (read : readByteVector bytes = .ok (vector, rest)) :
    bytes = encodeByteVector vector ++ rest ∧ vector.size < 2 ^ 64 := by
  unfold readByteVector at read
  split at read
  · simp at read
  · rename_i count after counted
    obtain ⟨countSplit, countBound⟩ := readCompactSize_ok counted
    split at read
    · simp at read
    · rename_i data remaining taken
      obtain ⟨dataSplit, dataLength⟩ := takeExact_ok taken
      simp only [Except.ok.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      have size : (⟨data.toArray⟩ : ByteArray).size = count := by
        simp [ByteArray.size, dataLength]
      refine ⟨?_, by omega⟩
      simp only [encodeByteVector, size, countSplit, dataSplit, List.append_assoc]

/-! ## Witness stacks -/

theorem serializeWitness_foldl_data (items : List ByteArray) (start : ByteArray) :
    (items.foldl (fun bytes item => bytes ++ serializeByteVector item) start).data.toList =
      start.data.toList ++ items.flatMap encodeByteVector := by
  induction items generalizing start with
  | nil => simp
  | cons item items ih =>
    simp only [List.foldl_cons, ih, List.flatMap_cons, ByteArray.data_append, Array.toList_append,
      serializeByteVector_data, List.append_assoc]

theorem readMany_readByteVector (items : List ByteArray)
    (bounded : ∀ item ∈ items, item.size < 2 ^ 64) (rest : List UInt8) :
    readMany readByteVector items.length (items.flatMap encodeByteVector ++ rest) =
      .ok (items, rest) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany,
      readByteVector_encode (bounded item (by simp)), bind, Except.bind,
      ih (fun other member => bounded other (by simp [member]))]
    rfl

/-- The serialized witness stack written by finalizers decodes to the same
items, as `PSBT_IN_FINAL_SCRIPTWITNESS` values are read. -/
theorem decodeAll_readWitnessStack (items : List ByteArray)
    (count : items.length < 2 ^ 64) (bounded : ∀ item ∈ items, item.size < 2 ^ 64) :
    decodeAll readWitnessStack (serializeWitness items) = .ok items := by
  have data : (serializeWitness items).data.toList =
      compactSize items.length ++ (items.flatMap encodeByteVector ++ []) := by
    simp [serializeWitness, serializeWitness_foldl_data]
  simp only [decodeAll, readWitnessStack, data, readCompactSize_compactSize count,
    bind, Except.bind, readMany_readByteVector items bounded]
  rfl

end LeanMiniscript.Bitcoin
