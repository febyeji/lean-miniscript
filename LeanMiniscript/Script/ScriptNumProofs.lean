import LeanMiniscript.Script.State

namespace LeanMiniscript.Script

private theorem byte_toNat_mod (n : Nat) :
    (UInt8.ofNat (n % 256)).toNat = n % 256 := by
  exact UInt8.toNat_ofNat_of_lt' (by
    simpa [UInt8.size] using Nat.mod_lt n (by omega : 0 < 256))

private theorem byte_ofNat_ne_zero {n : Nat} (nonzero : n % 256 ≠ 0) :
    UInt8.ofNat n ≠ 0 := by
  intro equal
  have natural := congrArg UInt8.toNat equal
  simp at natural
  exact nonzero natural

private theorem byte_ofNat_ne_128 {n : Nat} (notNegativeZero : n % 256 ≠ 128) :
    UInt8.ofNat n ≠ 128 := by
  intro equal
  have natural := congrArg UInt8.toNat equal
  simp at natural
  exact notNegativeZero natural

private theorem aux_zero (fuel : Nat) :
    scriptNumMagnitudeBytesAux fuel 0 = [] := by
  cases fuel <;> rfl

private theorem aux_unfold {fuel n : Nat} (fuelPos : 0 < fuel)
    (nPos : 0 < n) :
    scriptNumMagnitudeBytesAux fuel n =
      UInt8.ofNat (n % 256) ::
        scriptNumMagnitudeBytesAux (fuel - 1) (n / 256) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      rw [scriptNumMagnitudeBytesAux]
      rw [if_neg (by omega : n ≠ 0)]
      simp

private theorem aux_two {n : Nat} (lower : 256 ≤ n) (upper : n < 65536) :
    scriptNumMagnitudeBytesAux n n =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256)] := by
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  have tail : n / 256 / 256 = 0 := by omega
  rw [tail, aux_zero]

private theorem aux_three {n : Nat} (lower : 65536 ≤ n)
    (upper : n < 16777216) :
    scriptNumMagnitudeBytesAux n n =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
        UInt8.ofNat ((n / 256 / 256) % 256)] := by
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  have tail : n / 256 / 256 / 256 = 0 := by omega
  rw [tail, aux_zero]

private theorem aux_four {n : Nat} (lower : 16777216 ≤ n)
    (upper : n < 4294967296) :
    scriptNumMagnitudeBytesAux n n =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
        UInt8.ofNat ((n / 256 / 256) % 256),
        UInt8.ofNat ((n / 256 / 256 / 256) % 256)] := by
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  rw [aux_unfold (by omega) (by omega)]
  have tail : n / 256 / 256 / 256 / 256 = 0 := by omega
  rw [tail, aux_zero]

private theorem scriptNumBytes_ofNat_pos {n : Nat} (pos : 0 < n) :
    scriptNumBytes (Int.ofNat n) =
      if scriptNumNeedsSignByte (scriptNumMagnitudeBytesAux n n) then
        scriptNumMagnitudeBytesAux n n ++ [0]
      else scriptNumMagnitudeBytesAux n n := by
  have intNe : (Int.ofNat n) ≠ 0 := by
    change (n : Int) ≠ 0
    omega
  have abs : (Int.ofNat n).natAbs = n := rfl
  have nonneg' : ¬ (n : Int) < 0 := by omega
  rw [scriptNumBytes, if_neg intNe]
  simp only [abs]
  by_cases sign : scriptNumNeedsSignByte (scriptNumMagnitudeBytesAux n n)
  · simp [sign, nonneg']
  · simp [sign, nonneg']

private theorem bytes_lt128 {n : Nat} (pos : 0 < n) (bound : n < 128) :
    scriptNumBytes (Int.ofNat n) = [UInt8.ofNat (n % 256)] := by
  cases n with
  | zero => omega
  | succ k =>
      have intNe : (Int.ofNat (k + 1)) ≠ 0 := by
        change (k : Int) + 1 ≠ 0
        omega
      have abs : (Int.ofNat (k + 1)).natAbs = k + 1 := rfl
      have natNe : k + 1 ≠ 0 := by omega
      rw [scriptNumBytes, if_neg intNe]
      simp only [abs]
      rw [scriptNumMagnitudeBytesAux]
      rw [if_neg natNe]
      have hk : (k + 1) / 256 = 0 := Nat.div_eq_of_lt (by omega)
      rw [hk]
      rw [aux_zero]
      have natByteLt : ¬ 128 ≤ (k + 1) % 256 := by omega
      have nonneg' : ¬ (k : Int) + 1 < 0 := by omega
      simp [scriptNumNeedsSignByte, natByteLt, nonneg']

private theorem bytes_lt256_high {n : Nat} (lower : 128 ≤ n)
    (upper : n < 256) :
    scriptNumBytes (Int.ofNat n) = [UInt8.ofNat (n % 256), 0] := by
  rw [scriptNumBytes_ofNat_pos (by omega)]
  rw [show scriptNumMagnitudeBytesAux n n = [UInt8.ofNat (n % 256)] by
    rw [aux_unfold (by omega) (by omega)]
    have tail : n / 256 = 0 := by omega
    rw [tail, aux_zero]]
  have high : 128 ≤ n % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem bytes_two_low {n : Nat} (lower : 256 ≤ n)
    (upper : n < 32768) :
    scriptNumBytes (Int.ofNat n) =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256)] := by
  rw [scriptNumBytes_ofNat_pos (by omega), aux_two lower (by omega)]
  have high : ¬ 128 ≤ (n / 256) % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem bytes_two_high {n : Nat} (lower : 32768 ≤ n)
    (upper : n < 65536) :
    scriptNumBytes (Int.ofNat n) =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256), 0] := by
  rw [scriptNumBytes_ofNat_pos (by omega), aux_two (by omega) upper]
  have high : 128 ≤ (n / 256) % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem bytes_three_low {n : Nat} (lower : 65536 ≤ n)
    (upper : n < 8388608) :
    scriptNumBytes (Int.ofNat n) =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
        UInt8.ofNat ((n / 256 / 256) % 256)] := by
  rw [scriptNumBytes_ofNat_pos (by omega), aux_three lower (by omega)]
  have high : ¬ 128 ≤ (n / 256 / 256) % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem bytes_three_high {n : Nat} (lower : 8388608 ≤ n)
    (upper : n < 16777216) :
    scriptNumBytes (Int.ofNat n) =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
        UInt8.ofNat ((n / 256 / 256) % 256), 0] := by
  rw [scriptNumBytes_ofNat_pos (by omega), aux_three (by omega) upper]
  have high : 128 ≤ (n / 256 / 256) % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem bytes_four_low {n : Nat} (lower : 16777216 ≤ n)
    (upper : n < 2147483648) :
    scriptNumBytes (Int.ofNat n) =
      [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
        UInt8.ofNat ((n / 256 / 256) % 256),
        UInt8.ofNat ((n / 256 / 256 / 256) % 256)] := by
  rw [scriptNumBytes_ofNat_pos (by omega), aux_four lower (by omega)]
  have high : ¬ 128 ≤ (n / 256 / 256 / 256) % 256 := by omega
  simp [scriptNumNeedsSignByte, high]

private theorem decode_lt128 {n : Nat} (upper : n < 128)
    (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  by_cases zero : n = 0
  · subst n
    cases minimal <;> rfl
  · have pos : 0 < n := Nat.pos_of_ne_zero zero
    rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
    rw [bytes_lt128 pos upper]
    simp [decodeScriptNum, scriptNumIsMinimal, scriptNumIsNegative,
      clearScriptNumSignBit, decodeUnsignedLEAux]
    simp [ByteArray.size, List.size_toArray]
    have mod128Nat : n % 128 = n := Nat.mod_eq_of_lt upper
    have mod256Nat : n % 256 = n := Nat.mod_eq_of_lt (by omega)
    have mod128Int : (n : Int) % 128 = n := by omega
    have mod256Int : (n : Int) % 256 = n := by omega
    simp [mod128Nat, mod256Nat, mod128Int, mod256Int, zero,
      show ¬ 128 ≤ n by omega]

private theorem decode_lt256_high {n : Nat} (lower : 128 ≤ n)
    (upper : n < 256) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_lt256_high lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have mod256Nat : n % 256 = n := Nat.mod_eq_of_lt upper
  have mod256Int : (n : Int) % 256 = n := by omega
  simp [mod256Nat, mod256Int, lower]

private theorem decode_two_low {n : Nat} (lower : 256 ≤ n)
    (upper : n < 32768) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_two_low lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have qLtNat : n / 256 < 128 := by omega
  have qMod128Nat : n / 256 % 128 = n / 256 := Nat.mod_eq_of_lt qLtNat
  have qMod256Nat : n / 256 % 256 = n / 256 :=
    Nat.mod_eq_of_lt (by omega)
  have qMod128Int : (n : Int) / 256 % 128 = (n : Int) / 256 := by omega
  have qMod256Int : (n : Int) / 256 % 256 = (n : Int) / 256 := by omega
  have reconstruct : (n : Int) % 256 + (n : Int) / 256 * 256 = n := by
    omega
  simp [qMod128Nat, qMod256Nat, qMod128Int, qMod256Int,
    show n / 256 ≠ 0 by omega, show ¬128 ≤ n / 256 by omega,
    reconstruct]

private theorem decode_two_high {n : Nat} (lower : 32768 ≤ n)
    (upper : n < 65536) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_two_high lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have qLower : 128 ≤ n / 256 := by omega
  have qUpper : n / 256 < 256 := by omega
  have qMod256Nat : n / 256 % 256 = n / 256 :=
    Nat.mod_eq_of_lt qUpper
  have qMod256Int : (n : Int) / 256 % 256 = (n : Int) / 256 := by omega
  have reconstruct : (n : Int) % 256 + (n : Int) / 256 * 256 = n := by
    omega
  simp [qMod256Nat, qMod256Int, qLower, reconstruct]

private theorem decode_three_low {n : Nat} (lower : 65536 ≤ n)
    (upper : n < 8388608) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_three_low lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have qUpper : n / 256 / 256 < 128 := by omega
  have qMod128Nat : n / 256 / 256 % 128 = n / 256 / 256 :=
    Nat.mod_eq_of_lt qUpper
  have qMod256Nat : n / 256 / 256 % 256 = n / 256 / 256 :=
    Nat.mod_eq_of_lt (by omega)
  have qMod128Int : (n : Int) / 256 / 256 % 128 =
      (n : Int) / 256 / 256 := by omega
  have qMod256Int : (n : Int) / 256 / 256 % 256 =
      (n : Int) / 256 / 256 := by omega
  simp [qMod128Nat, qMod256Nat, qMod128Int, qMod256Int,
    show n / 256 / 256 ≠ 0 by omega,
    show ¬ 128 ≤ n / 256 / 256 by omega]
  omega

private theorem decode_three_high {n : Nat} (lower : 8388608 ≤ n)
    (upper : n < 16777216) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_three_high lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have qLower : 128 ≤ n / 256 / 256 := by omega
  have qUpper : n / 256 / 256 < 256 := by omega
  have qMod256Nat : n / 256 / 256 % 256 = n / 256 / 256 :=
    Nat.mod_eq_of_lt qUpper
  have qMod256Int : (n : Int) / 256 / 256 % 256 =
      (n : Int) / 256 / 256 := by omega
  have notLow : ¬ n / 256 / 256 < 128 := by omega
  have reconstruct :
      (n : Int) % 256 + ((n : Int) / 256 % 256 * 256 +
        (n : Int) / 256 / 256 * 65536) = n := by
    omega
  simp [qMod256Nat, qMod256Int, notLow, reconstruct]

private theorem decode_four_low {n : Nat} (lower : 16777216 ≤ n)
    (upper : n < 2147483648) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n) := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_four_low lower upper]
  simp [decodeScriptNum, ByteArray.size, scriptNumIsMinimal,
    scriptNumIsNegative, clearScriptNumSignBit, decodeUnsignedLEAux]
  have qUpper : n / 256 / 256 / 256 < 128 := by omega
  have qMod128Nat : n / 256 / 256 / 256 % 128 =
      n / 256 / 256 / 256 := Nat.mod_eq_of_lt qUpper
  have qMod256Nat : n / 256 / 256 / 256 % 256 =
      n / 256 / 256 / 256 := Nat.mod_eq_of_lt (by omega)
  have qMod128Int : (n : Int) / 256 / 256 / 256 % 128 =
      (n : Int) / 256 / 256 / 256 := by omega
  have qMod256Int : (n : Int) / 256 / 256 / 256 % 256 =
      (n : Int) / 256 / 256 / 256 := by omega
  simp [qMod128Nat, qMod256Nat, qMod128Int, qMod256Int,
    show n / 256 / 256 / 256 ≠ 0 by omega,
    show ¬ 128 ≤ n / 256 / 256 / 256 by omega]
  omega

/-- Every nonnegative natural below the signed four-byte boundary round-trips
    through its canonical Script-number encoding under either minimal-data
    mode. -/
theorem decodeScriptNum_scriptNat_of_lt {n : Nat}
    (bound : n < maxArithmeticScriptNatExclusive) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal maxArithmeticScriptNumBytes =
      .ok (Int.ofNat n) := by
  change n < 2147483648 at bound
  change decodeScriptNum (scriptNat n) minimal 4 = .ok (Int.ofNat n)
  by_cases h1 : n < 128
  · exact decode_lt128 h1 minimal
  by_cases h2 : n < 256
  · exact decode_lt256_high (by omega) h2 minimal
  by_cases h3 : n < 32768
  · exact decode_two_low (by omega) h3 minimal
  by_cases h4 : n < 65536
  · exact decode_two_high (by omega) h4 minimal
  by_cases h5 : n < 8388608
  · exact decode_three_low (by omega) h5 minimal
  by_cases h6 : n < 16777216
  · exact decode_three_high (by omega) h6 minimal
  exact decode_four_low (by omega) bound minimal

/-- Increasing the accepted byte limit preserves a successful Script-number
    decode. The minimality requirement and decoded value are unchanged. -/
theorem decodeScriptNum_mono {bytes : StackElement} {requireMinimal : Bool}
    {small large : Nat} {value : Int} (le : small ≤ large)
    (decoded : decodeScriptNum bytes requireMinimal small = .ok value) :
    decodeScriptNum bytes requireMinimal large = .ok value := by
  unfold decodeScriptNum at decoded ⊢
  split at decoded
  · contradiction
  · split at decoded
    · contradiction
    · split
      · omega
      · exact decoded

namespace ArithmeticScriptNatSafe

/-- The semantic four-byte bound is sufficient for the executable arithmetic
    Script-number guard. -/
theorem of_lt {n : Nat} (bound : n < maxArithmeticScriptNatExclusive) :
    ArithmeticScriptNatSafe n := by
  exact ⟨bound, decodeScriptNum_scriptNat_of_lt bound false,
    decodeScriptNum_scriptNat_of_lt bound true⟩

/-- Runtime element sizes are far below the signed four-byte boundary, so the
    canonical encoding of any bounded size is safe for arithmetic opcodes. -/
theorem of_le_maxScriptElementSize {n : Nat}
    (bound : n ≤ maxScriptElementSize) : ArithmeticScriptNatSafe n := by
  apply of_lt
  change n < 2147483648
  change n ≤ 520 at bound
  omega

end ArithmeticScriptNatSafe

/-- A size bounded by the Script element limit has the exact canonical
    arithmetic decode under either minimal-data mode. -/
theorem decodeScriptNum_scriptNat_of_le_maxScriptElementSize {n : Nat}
    (bound : n ≤ maxScriptElementSize) (minimal : Bool) :
    decodeScriptNum (scriptNat n) minimal maxArithmeticScriptNumBytes =
      .ok (Int.ofNat n) :=
  (ArithmeticScriptNatSafe.of_le_maxScriptElementSize bound).decode minimal

private theorem truth_lt128 {n : Nat} (pos : 0 < n) (upper : n < 128) :
    castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_lt128 pos upper]
  have nonzero : UInt8.ofNat (n % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  have notNegativeZero : UInt8.ofNat (n % 256) ≠ 128 :=
    byte_ofNat_ne_128 (by omega)
  simp [castToBool, ByteArray.size, nonzero, notNegativeZero]

private theorem truth_lt256_high {n : Nat} (lower : 128 ≤ n)
    (upper : n < 256) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_lt256_high lower upper]
  have nonzero : UInt8.ofNat (n % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  simp [castToBool, ByteArray.size, nonzero]

private theorem truth_two_low {n : Nat} (lower : 256 ≤ n)
    (upper : n < 32768) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_two_low lower upper]
  have nonzero : UInt8.ofNat (n / 256 % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  have notNegativeZero : UInt8.ofNat (n / 256 % 256) ≠ 128 :=
    byte_ofNat_ne_128 (by omega)
  simp [castToBool, ByteArray.size, nonzero, notNegativeZero]

private theorem truth_two_high {n : Nat} (lower : 32768 ≤ n)
    (upper : n < 65536) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_two_high lower upper]
  have nonzero : UInt8.ofNat (n / 256 % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  simp [castToBool, ByteArray.size, nonzero]

private theorem truth_three_low {n : Nat} (lower : 65536 ≤ n)
    (upper : n < 8388608) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_three_low lower upper]
  have nonzero : UInt8.ofNat (n / 256 / 256 % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  have notNegativeZero : UInt8.ofNat (n / 256 / 256 % 256) ≠ 128 :=
    byte_ofNat_ne_128 (by omega)
  simp [castToBool, ByteArray.size, nonzero, notNegativeZero]

private theorem truth_three_high {n : Nat} (lower : 8388608 ≤ n)
    (upper : n < 16777216) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_three_high lower upper]
  have nonzero : UInt8.ofNat (n / 256 / 256 % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  simp [castToBool, ByteArray.size, nonzero]

private theorem truth_four_low {n : Nat} (lower : 16777216 ≤ n)
    (upper : n < 2147483648) : castToBool (scriptNat n) = true := by
  rw [show scriptNat n = ⟨(scriptNumBytes (Int.ofNat n)).toArray⟩ by rfl]
  rw [bytes_four_low lower upper]
  have nonzero : UInt8.ofNat (n / 256 / 256 / 256 % 256) ≠ 0 :=
    byte_ofNat_ne_zero (by omega)
  have notNegativeZero : UInt8.ofNat (n / 256 / 256 / 256 % 256) ≠ 128 :=
    byte_ofNat_ne_128 (by omega)
  simp [castToBool, ByteArray.size, nonzero, notNegativeZero]

/-- A positive canonical natural below the signed four-byte boundary is truthy. -/
theorem castToBool_scriptNat_of_pos_of_lt {n : Nat} (pos : 0 < n)
    (bound : n < maxArithmeticScriptNatExclusive) :
    castToBool (scriptNat n) = true := by
  change n < 2147483648 at bound
  by_cases h1 : n < 128
  · exact truth_lt128 pos h1
  by_cases h2 : n < 256
  · exact truth_lt256_high (by omega) h2
  by_cases h3 : n < 32768
  · exact truth_two_low (by omega) h3
  by_cases h4 : n < 65536
  · exact truth_two_high (by omega) h4
  by_cases h5 : n < 8388608
  · exact truth_three_low (by omega) h5
  by_cases h6 : n < 16777216
  · exact truth_three_high (by omega) h6
  exact truth_four_low (by omega) bound

end LeanMiniscript.Script
