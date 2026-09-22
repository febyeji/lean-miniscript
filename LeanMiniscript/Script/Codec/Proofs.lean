import LeanMiniscript.Script.Codec.Deserialization

namespace LeanMiniscript.Script

/-!
# Bitcoin Script codec proofs

The decoder inverts canonical serialization up to the explicit AST
normalization induced by Script's dedicated numeric push opcodes.
-/

theorem opcodeFromByte_opcodeByte (opcode : Opcode) :
    opcodeFromByte? (opcodeByte opcode).toNat = some opcode := by
  cases opcode <;> rfl

private theorem uint8ToNat_of_lt (n : Nat) (bound : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

private theorem uint16LE_toNat (n : Nat) (bound : n ≤ 65535) :
    (UInt8.ofNat n).toNat + 256 * (UInt8.ofNat (n / 256)).toNat = n := by
  simp only [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

private theorem uint32LE_toNat (n : Nat) (bound : n ≤ 4294967295) :
    (UInt8.ofNat n).toNat + 256 * (UInt8.ofNat (n / 256)).toNat +
      65536 * (UInt8.ofNat (n / 65536)).toNat +
      16777216 * (UInt8.ofNat (n / 16777216)).toNat = n := by
  simp only [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem deserializeScriptList_opcode (opcode : Opcode)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (opcodeByte opcode :: suffix) offset =
      (deserializeScriptList suffix (offset + 1)).map
        (fun rest => .op opcode :: rest) := by
  rw [deserializeScriptList.eq_def]
  cases opcode <;> rfl

theorem deserializeScriptList_zero (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (0x00 :: suffix) offset =
      (deserializeScriptList suffix (offset + 1)).map
        (fun rest => .pushNum 0 :: rest) := by
  rw [deserializeScriptList.eq_def]
  rfl

theorem deserializeScriptList_negOne (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (0x4f :: suffix) offset =
      (deserializeScriptList suffix (offset + 1)).map
        (fun rest => .pushNum (-1) :: rest) := by
  rw [deserializeScriptList.eq_def]
  rfl

theorem deserializeScriptList_smallPositive (value : Nat)
    (positive : 1 ≤ value) (atMost : value ≤ 16)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (UInt8.ofNat (0x50 + value) :: suffix) offset =
      (deserializeScriptList suffix (offset + 1)).map
        (fun rest => .pushNum value :: rest) := by
  rw [deserializeScriptList.eq_def]
  dsimp only
  rw [uint8ToNat_of_lt (0x50 + value) (by omega)]
  have notZero : ¬0x50 + value = 0 := by omega
  have notPush : ¬0x50 + value ≤ 75 := by omega
  have notPush1 : ¬0x50 + value = 0x4c := by omega
  have notPush2 : ¬0x50 + value = 0x4d := by omega
  have notPush4 : ¬0x50 + value = 0x4e := by omega
  have notNegOne : ¬0x50 + value = 0x4f := by omega
  have smallOpcode : 0x51 ≤ 0x50 + value ∧ 0x50 + value ≤ 0x60 := by
    omega
  rw [if_neg notZero, if_neg notPush, if_neg notPush1, if_neg notPush2,
    if_neg notPush4, if_neg notNegOne, if_pos smallOpcode]
  have castEq : ((0x50 + value : Nat) : Int) - 0x50 = value := by
    push_cast
    omega
  rw [castEq]
  cases deserializeScriptList suffix (offset + 1) <;> rfl

private theorem byteArray_eq_singleton_of_size_one (data : ByteArray)
    (sizeEq : data.size = 1) :
    data = ⟨#[data.get! 0]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using sizeEq
  · intro index leftBound rightBound
    have rightBound' : index < 1 := by simpa using rightBound
    have indexEq : index = 0 := by omega
    subst index
    simp [ByteArray.get!, sizeEq]

theorem deserializeScriptList_shortData (data : ByteArray)
    (nonempty : data.size ≠ 0)
    (small : data.size < 76) (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList
        (UInt8.ofNat data.size :: (data.data.toList ++ suffix)) offset =
      (deserializeScriptList suffix (offset + 1 + data.size)).map
        (fun rest => .pushData data :: rest) := by
  rw [deserializeScriptList.eq_def]
  dsimp only
  rw [uint8ToNat_of_lt data.size (by omega)]
  have le75 : data.size ≤ 75 := by omega
  have fits : data.size ≤ (data.data.toList ++ suffix).length := by simp
  rw [if_neg nonempty, if_pos le75, dif_pos fits]
  have takeEq :
      (data.data.toList ++ suffix).take data.size = data.data.toList := by
    simp
  have dropEq :
      (data.data.toList ++ suffix).drop data.size = suffix := by
    simp
  rw [takeEq, dropEq]
  have dataEq : (⟨data.data.toList.toArray⟩ : ByteArray) = data := by
    cases data
    simp
  rw [dataEq]
  cases deserializeScriptList suffix (offset + 1 + data.size) <;> rfl

theorem deserializeScriptList_pushData1 (data : ByteArray)
    (lower : 76 ≤ data.size) (upper : data.size ≤ 255)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList
        (0x4c :: UInt8.ofNat data.size :: (data.data.toList ++ suffix)) offset =
      (deserializeScriptList suffix (offset + 2 + data.size)).map
        (fun rest => .pushData data :: rest) := by
  rw [deserializeScriptList.eq_def]
  dsimp only
  rw [uint8ToNat_of_lt data.size (by omega)]
  have fits : data.size ≤ (data.data.toList ++ suffix).length := by simp
  rw [dif_pos fits]
  have takeEq :
      (data.data.toList ++ suffix).take data.size = data.data.toList := by
    simp
  have dropEq :
      (data.data.toList ++ suffix).drop data.size = suffix := by
    simp
  rw [takeEq, dropEq]
  have dataEq : (⟨data.data.toList.toArray⟩ : ByteArray) = data := by
    cases data
    simp
  rw [dataEq]
  cases deserializeScriptList suffix (offset + 2 + data.size) <;> rfl

theorem deserializeScriptList_pushData2 (data : ByteArray)
    (lower : 256 ≤ data.size) (upper : data.size ≤ 65535)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList
        (0x4d :: UInt8.ofNat data.size :: UInt8.ofNat (data.size / 256) ::
          (data.data.toList ++ suffix)) offset =
      (deserializeScriptList suffix (offset + 3 + data.size)).map
        (fun rest => .pushData data :: rest) := by
  rw [deserializeScriptList.eq_def]
  dsimp only
  rw [uint16LE_toNat data.size upper]
  have fits : data.size ≤ (data.data.toList ++ suffix).length := by simp
  rw [dif_pos fits]
  have takeEq :
      (data.data.toList ++ suffix).take data.size = data.data.toList := by
    simp
  have dropEq :
      (data.data.toList ++ suffix).drop data.size = suffix := by
    simp
  rw [takeEq, dropEq]
  have dataEq : (⟨data.data.toList.toArray⟩ : ByteArray) = data := by
    cases data
    simp
  rw [dataEq]
  cases deserializeScriptList suffix (offset + 3 + data.size) <;> rfl

theorem deserializeScriptList_pushData4 (data : ByteArray)
    (lower : 65536 ≤ data.size) (upper : data.size ≤ MAX_PUSHDATA_SIZE)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList
        (0x4e :: UInt8.ofNat data.size :: UInt8.ofNat (data.size / 256) ::
          UInt8.ofNat (data.size / 65536) ::
          UInt8.ofNat (data.size / 16777216) ::
          (data.data.toList ++ suffix)) offset =
      (deserializeScriptList suffix (offset + 5 + data.size)).map
        (fun rest => .pushData data :: rest) := by
  rw [deserializeScriptList.eq_def]
  dsimp only
  rw [uint32LE_toNat data.size upper]
  have fits : data.size ≤ (data.data.toList ++ suffix).length := by simp
  rw [dif_pos fits]
  have takeEq :
      (data.data.toList ++ suffix).take data.size = data.data.toList := by
    simp
  have dropEq :
      (data.data.toList ++ suffix).drop data.size = suffix := by
    simp
  rw [takeEq, dropEq]
  have dataEq : (⟨data.data.toList.toArray⟩ : ByteArray) = data := by
    cases data
    simp
  rw [dataEq]
  cases deserializeScriptList suffix (offset + 5 + data.size) <;> rfl

theorem deserializeScriptList_serializeLengthPrefixedPush_nonempty
    (data encoded : ByteArray)
    (nonempty : data.size ≠ 0)
    (serialized : serializeLengthPrefixedPush data = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => .pushData data :: rest) := by
  unfold serializeLengthPrefixedPush pushDataPrefix at serialized
  split at serialized
  next short =>
    change Except.ok
      (⟨([UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray) =
        Except.ok encoded at serialized
    injection serialized with encodedEq
    subst encoded
    have encodedBytes :
        (⟨([UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray).data.toList =
          UInt8.ofNat data.size :: data.data.toList := by
      rfl
    have encodedSize :
        (⟨([UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray).size =
          1 + data.size := by
      simp only [ByteArray.size, List.size_toArray, List.length_append,
        List.length_cons, List.length_nil, Array.length_toList]
    rw [encodedBytes, encodedSize]
    simpa only [List.cons_append, Nat.add_assoc] using
      deserializeScriptList_shortData data nonempty short suffix offset
  next notShort =>
    split at serialized
    next byteSize =>
      change Except.ok
        (⟨([0x4c, UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray) =
          Except.ok encoded at serialized
      injection serialized with encodedEq
      subst encoded
      have lower : 76 ≤ data.size := by omega
      have encodedBytes :
          (⟨([0x4c, UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray).data.toList =
            0x4c :: UInt8.ofNat data.size :: data.data.toList := by
        rfl
      have encodedSize :
          (⟨([0x4c, UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray).size =
            2 + data.size := by
        simp only [ByteArray.size, List.size_toArray, List.length_append,
          List.length_cons, List.length_nil, Array.length_toList]
      rw [encodedBytes, encodedSize]
      simpa only [List.cons_append, Nat.add_assoc] using
        deserializeScriptList_pushData1 data lower byteSize suffix offset
    next notByteSize =>
      split at serialized
      next wordSize =>
        change Except.ok
          (⟨((0x4d :: uint16LE data.size) ++ data.data.toList).toArray⟩ : ByteArray) =
            Except.ok encoded at serialized
        injection serialized with encodedEq
        subst encoded
        have lower : 256 ≤ data.size := by omega
        have encodedBytes :
            (⟨((0x4d :: uint16LE data.size) ++ data.data.toList).toArray⟩ : ByteArray).data.toList =
              0x4d :: UInt8.ofNat data.size :: UInt8.ofNat (data.size / 256) ::
                data.data.toList := by
          rfl
        have encodedSize :
            (⟨((0x4d :: uint16LE data.size) ++ data.data.toList).toArray⟩ : ByteArray).size =
              3 + data.size := by
          simp only [uint16LE, ByteArray.size, List.size_toArray,
            List.length_append, List.length_cons, List.length_nil,
            Array.length_toList]
        rw [encodedBytes, encodedSize]
        simpa only [List.cons_append, Nat.add_assoc] using
          deserializeScriptList_pushData2 data lower wordSize suffix offset
      next notWordSize =>
        split at serialized
        next dwordSize =>
          change Except.ok
            (⟨((0x4e :: uint32LE data.size) ++ data.data.toList).toArray⟩ : ByteArray) =
              Except.ok encoded at serialized
          injection serialized with encodedEq
          subst encoded
          have lower : 65536 ≤ data.size := by omega
          have encodedBytes :
              (⟨((0x4e :: uint32LE data.size) ++ data.data.toList).toArray⟩ : ByteArray).data.toList =
                0x4e :: UInt8.ofNat data.size :: UInt8.ofNat (data.size / 256) ::
                  UInt8.ofNat (data.size / 65536) ::
                  UInt8.ofNat (data.size / 16777216) :: data.data.toList := by
            rfl
          have encodedSize :
              (⟨((0x4e :: uint32LE data.size) ++ data.data.toList).toArray⟩ : ByteArray).size =
                5 + data.size := by
            simp only [uint32LE, ByteArray.size, List.size_toArray,
              List.length_append, List.length_cons, List.length_nil,
              Array.length_toList]
          rw [encodedBytes, encodedSize]
          simpa only [List.cons_append, Nat.add_assoc] using
            deserializeScriptList_pushData4 data lower dwordSize suffix offset
        next tooLarge =>
          change Except.error (SerializationError.pushDataTooLarge data.size) =
            Except.ok encoded at serialized
          contradiction

theorem deserializeScriptList_serializeLengthPrefixedPush_empty
    (data encoded : ByteArray)
    (empty : data.size = 0)
    (serialized : serializeLengthPrefixedPush data = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => .pushNum 0 :: rest) := by
  have dataBytes : data.data.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    change data.data.size = 0 at empty
    simpa only [Array.length_toList] using empty
  unfold serializeLengthPrefixedPush pushDataPrefix at serialized
  split at serialized
  next short =>
    change Except.ok
      (⟨([UInt8.ofNat data.size] ++ data.data.toList).toArray⟩ : ByteArray) =
        Except.ok encoded at serialized
    injection serialized with encodedEq
    subst encoded
    rw [empty, dataBytes]
    have zeroByte : UInt8.ofNat 0 = 0x00 := by rfl
    rw [zeroByte]
    simpa only [List.append_nil, List.singleton_append,
      ByteArray.size, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add] using deserializeScriptList_zero suffix offset
  next notShort =>
    omega

theorem deserializeScriptList_serializeLengthPrefixedPush
    (data encoded : ByteArray)
    (serialized : serializeLengthPrefixedPush data = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest =>
          (if data.size = 0 then .pushNum 0 else .pushData data) :: rest) := by
  by_cases empty : data.size = 0
  · simpa only [if_pos empty] using
      deserializeScriptList_serializeLengthPrefixedPush_empty
        data encoded empty serialized suffix offset
  · simpa only [if_neg empty] using
      deserializeScriptList_serializeLengthPrefixedPush_nonempty
        data encoded empty serialized suffix offset

theorem deserializeScriptList_serializePushData
    (data encoded : ByteArray)
    (serialized : serializePushData data = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => normalizeSerializedData data :: rest) := by
  unfold serializePushData at serialized
  split at serialized
  next oneByte =>
    dsimp only at serialized
    split at serialized
    next small =>
      change Except.ok (⟨#[UInt8.ofNat (0x50 + (data.get! 0).toNat)]⟩ : ByteArray) =
        Except.ok encoded at serialized
      injection serialized with encodedEq
      subst encoded
      have nonempty : data.size ≠ 0 := by omega
      have normalized :
          normalizeSerializedData data = .pushNum (data.get! 0).toNat := by
        simp only [normalizeSerializedData, if_neg nonempty, if_pos oneByte,
          if_pos small]
      rw [normalized]
      have encodedBytes :
          (⟨#[UInt8.ofNat (0x50 + (data.get! 0).toNat)]⟩ : ByteArray).data.toList =
            [UInt8.ofNat (0x50 + (data.get! 0).toNat)] := by
        rfl
      have encodedSize :
          (⟨#[UInt8.ofNat (0x50 + (data.get! 0).toNat)]⟩ : ByteArray).size = 1 := by
        rfl
      rw [encodedBytes, encodedSize]
      simpa only [List.singleton_append] using
        deserializeScriptList_smallPositive (data.get! 0).toNat
          small.1 small.2 suffix offset
    next notSmall =>
      split at serialized
      next negativeOne =>
        change Except.ok (⟨#[0x4f]⟩ : ByteArray) =
          Except.ok encoded at serialized
        injection serialized with encodedEq
        subst encoded
        have nonempty : data.size ≠ 0 := by omega
        have normalized : normalizeSerializedData data = .pushNum (-1) := by
          simp only [normalizeSerializedData, if_neg nonempty, if_pos oneByte,
            if_neg notSmall, if_pos negativeOne]
        rw [normalized]
        have encodedBytes :
            (⟨#[0x4f]⟩ : ByteArray).data.toList = [0x4f] := by
          rfl
        have encodedSize : (⟨#[0x4f]⟩ : ByteArray).size = 1 := by
          rfl
        rw [encodedBytes, encodedSize]
        simpa only [List.singleton_append] using
          deserializeScriptList_negOne suffix offset
      next ordinary =>
        have roundTrip := deserializeScriptList_serializeLengthPrefixedPush
          data encoded serialized suffix offset
        have nonempty : data.size ≠ 0 := by omega
        have normalized : normalizeSerializedData data = .pushData data := by
          simp only [normalizeSerializedData, if_neg nonempty, if_pos oneByte,
            if_neg notSmall, if_neg ordinary]
        rw [normalized]
        simpa only [if_neg nonempty] using roundTrip
  next notOneByte =>
    have roundTrip := deserializeScriptList_serializeLengthPrefixedPush
      data encoded serialized suffix offset
    by_cases empty : data.size = 0
    · have normalized : normalizeSerializedData data = .pushNum 0 := by
        simp only [normalizeSerializedData, if_pos empty]
      rw [normalized]
      simpa only [if_pos empty] using roundTrip
    · have normalized : normalizeSerializedData data = .pushData data := by
        simp only [normalizeSerializedData, if_neg empty, if_neg notOneByte]
      rw [normalized]
      simpa only [if_neg empty] using roundTrip

theorem deserializeScriptList_serializePushNum
    (value : Int) (encoded : ByteArray)
    (serialized : serializePushNum value = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => normalizeSerializedElement (.pushNum value) :: rest) := by
  unfold serializePushNum at serialized
  split at serialized
  next zero =>
    subst value
    change Except.ok (⟨#[0x00]⟩ : ByteArray) = Except.ok encoded at serialized
    injection serialized with encodedEq
    subst encoded
    have encodedBytes : (⟨#[0x00]⟩ : ByteArray).data.toList = [0x00] := by
      rfl
    have encodedSize : (⟨#[0x00]⟩ : ByteArray).size = 1 := by
      rfl
    have special :
        ((0 : Int) = 0 ∨ (0 : Int) = -1 ∨ (1 ≤ (0 : Int) ∧ (0 : Int) ≤ 16)) :=
      Or.inl rfl
    have normalized :
        normalizeSerializedElement (.pushNum (0 : Int)) = .pushNum 0 := by
      rw [normalizeSerializedElement, if_pos special]
    rw [encodedBytes, encodedSize]
    rw [normalized]
    simpa only [List.singleton_append] using
      deserializeScriptList_zero suffix offset
  next notZero =>
    split at serialized
    next negativeOne =>
      subst value
      change Except.ok (⟨#[0x4f]⟩ : ByteArray) = Except.ok encoded at serialized
      injection serialized with encodedEq
      subst encoded
      have encodedBytes : (⟨#[0x4f]⟩ : ByteArray).data.toList = [0x4f] := by
        rfl
      have encodedSize : (⟨#[0x4f]⟩ : ByteArray).size = 1 := by
        rfl
      have special :
          ((-1 : Int) = 0 ∨ (-1 : Int) = -1 ∨
            (1 ≤ (-1 : Int) ∧ (-1 : Int) ≤ 16)) :=
        Or.inr (Or.inl rfl)
      have normalized :
          normalizeSerializedElement (.pushNum (-1 : Int)) = .pushNum (-1) := by
        rw [normalizeSerializedElement, if_pos special]
      rw [encodedBytes, encodedSize]
      rw [normalized]
      simpa only [List.singleton_append] using
        deserializeScriptList_negOne suffix offset
    next notNegativeOne =>
      split at serialized
      next small =>
        change Except.ok (⟨#[UInt8.ofNat (0x50 + value.toNat)]⟩ : ByteArray) =
          Except.ok encoded at serialized
        injection serialized with encodedEq
        subst encoded
        have positive : 1 ≤ value.toNat := by omega
        have atMost : value.toNat ≤ 16 := by omega
        have natCast : (value.toNat : Int) = value := by omega
        have encodedBytes :
            (⟨#[UInt8.ofNat (0x50 + value.toNat)]⟩ : ByteArray).data.toList =
              [UInt8.ofNat (0x50 + value.toNat)] := by
          rfl
        have encodedSize :
            (⟨#[UInt8.ofNat (0x50 + value.toNat)]⟩ : ByteArray).size = 1 := by
          rfl
        have special :
            value = 0 ∨ value = -1 ∨ (1 ≤ value ∧ value ≤ 16) :=
          Or.inr (Or.inr small)
        rw [encodedBytes, encodedSize]
        simpa only [normalizeSerializedElement,
          if_pos special, List.singleton_append, natCast] using
          deserializeScriptList_smallPositive value.toNat positive atMost suffix offset
      next notSmall =>
        have roundTrip := deserializeScriptList_serializePushData
          (scriptNum value) encoded serialized suffix offset
        have notSpecial :
            ¬(value = 0 ∨ value = -1 ∨ (1 ≤ value ∧ value ≤ 16)) := by
          intro special
          rcases special with zero | negativeOne | small
          · exact notZero zero
          · exact notNegativeOne negativeOne
          · exact notSmall small
        simpa only [normalizeSerializedElement, if_neg notSpecial] using roundTrip

theorem deserializeScriptList_serializeElement
    (element : ScriptElement) (encoded : ByteArray)
    (serialized : serializeElement element = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => normalizeSerializedElement element :: rest) := by
  cases element with
  | op opcode =>
      change Except.ok (⟨#[opcodeByte opcode]⟩ : ByteArray) =
        Except.ok encoded at serialized
      injection serialized with encodedEq
      subst encoded
      have encodedBytes :
          (⟨#[opcodeByte opcode]⟩ : ByteArray).data.toList = [opcodeByte opcode] := by
        rfl
      have encodedSize : (⟨#[opcodeByte opcode]⟩ : ByteArray).size = 1 := by
        rfl
      rw [encodedBytes, encodedSize]
      simpa only [normalizeSerializedElement, List.singleton_append] using
        deserializeScriptList_opcode opcode suffix offset
  | pushData data =>
      exact deserializeScriptList_serializePushData
        data encoded serialized suffix offset
  | pushNum value =>
      exact deserializeScriptList_serializePushNum
        value encoded serialized suffix offset

private theorem except_map_map {α β γ ε : Type}
    (first : β → γ) (second : α → β)
    (result : Except ε α) :
    Except.map first (Except.map second result) =
      Except.map (fun value => first (second value)) result := by
  cases result <;> rfl

theorem deserializeScriptList_serializeScript
    (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded)
    (suffix : List UInt8) (offset : Nat) :
    deserializeScriptList (encoded.data.toList ++ suffix) offset =
      (deserializeScriptList suffix (offset + encoded.size)).map
        (fun rest => normalizeSerializedScript script ++ rest) := by
  induction script generalizing encoded offset with
  | nil =>
      change Except.ok ByteArray.empty = Except.ok encoded at serialized
      injection serialized with encodedEq
      subst encoded
      have emptyBytes : ByteArray.empty.data.toList = [] := by rfl
      have emptySize : ByteArray.empty.size = 0 := by rfl
      rw [emptyBytes, emptySize]
      simp only [List.nil_append, Nat.add_zero, normalizeSerializedScript,
        List.map_nil]
      cases deserializeScriptList suffix offset <;> rfl
  | cons element script ih =>
      simp only [serializeScript] at serialized
      cases elementSerialization : serializeElement element with
      | error error =>
          rw [elementSerialization] at serialized
          change Except.error error = Except.ok encoded at serialized
          contradiction
      | ok elementBytes =>
          rw [elementSerialization] at serialized
          cases scriptSerialization : serializeScript script with
          | error error =>
              rw [scriptSerialization] at serialized
              change Except.error error = Except.ok encoded at serialized
              contradiction
          | ok scriptBytes =>
              rw [scriptSerialization] at serialized
              change Except.ok (elementBytes ++ scriptBytes) =
                Except.ok encoded at serialized
              injection serialized with encodedEq
              subst encoded
              rw [ByteArray.toList_data_append, List.append_assoc]
              rw [deserializeScriptList_serializeElement element elementBytes
                elementSerialization]
              rw [ih scriptBytes scriptSerialization
                (offset + elementBytes.size)]
              simp only [ByteArray.size_append, normalizeSerializedScript,
                List.map_cons, Nat.add_assoc]
              rw [except_map_map]
              simp only [List.cons_append]

/-- Canonical serialization followed by deserialization returns the normalized
    Script AST. This accounts for wire encodings which erase the distinction
    between numeric pushes and their byte-vector representation. -/
theorem deserializeScript_serializeScript
    (script : Script) (encoded : ByteArray)
    (serialized : serializeScript script = .ok encoded) :
    deserializeScript encoded = .ok (normalizeSerializedScript script) := by
  have roundTrip := deserializeScriptList_serializeScript
    script encoded serialized [] 0
  unfold deserializeScript
  simp only [List.append_nil, Nat.zero_add] at roundTrip
  rw [roundTrip]
  rw [deserializeScriptList.eq_def]
  change Except.ok (normalizeSerializedScript script ++ []) =
    Except.ok (normalizeSerializedScript script)
  rw [List.append_nil]

/-- Scripts fixed by serialization normalization round-trip exactly. -/
theorem deserializeScript_serializeScript_of_normalized
    (script : Script) (encoded : ByteArray)
    (normalized : normalizeSerializedScript script = script)
    (serialized : serializeScript script = .ok encoded) :
    deserializeScript encoded = .ok script := by
  rw [← normalized]
  exact deserializeScript_serializeScript script encoded serialized

end LeanMiniscript.Script
