import LeanMiniscript.Miniscript.SurfaceParser

namespace LeanMiniscript.Miniscript

namespace SurfaceParser

/-!
# Surface parser proofs: atom rendering

Hex, natural-number, key, and hash atoms rendered by the pretty printer are
atom-safe and parse back to their original values.

Some helpers here were `private` in the former single-file `SurfaceParserProofs`
module. They are visible only so that sibling submodules can use them; treat
them as internal proof helpers, not stable API.
-/

private theorem hexNibble_hexDigit (n : Nat) (h : n < 16) :
    hexNibble? (LeanMiniscript.Script.hexDigit n) = some n := by
  have hAll : ∀ value : Fin 16,
      hexNibble? (LeanMiniscript.Script.hexDigit value.val) =
        some value.val := by
    decide
  exact hAll ⟨n, h⟩

private theorem byteHexValueUInt8 (byte : UInt8) :
    UInt8.ofNat (byte.toNat / 16) * 16 +
        UInt8.ofNat (byte.toNat % 16) = byte := by
  have hAll : ∀ value : Fin 256,
      UInt8.ofNat ((UInt8.ofNat value.val).toNat / 16) * 16 +
          UInt8.ofNat ((UInt8.ofNat value.val).toNat % 16) =
        UInt8.ofNat value.val := by
    set_option maxRecDepth 100000 in
      decide
  simpa using hAll ⟨byte.toNat, byte.toNat_lt⟩

private theorem decodeHexChars_byteHexChars_append
    (byte : UInt8) (chars : List Char) :
    decodeHexChars?
        (LeanMiniscript.Script.byteHexChars byte ++ chars) =
      match decodeHexChars? chars with
      | some tail => some (byte :: tail)
      | none => none := by
  have hHigh : byte.toNat / 16 < 16 := by
    have := byte.toNat_lt
    omega
  have hLow : byte.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
  simp [LeanMiniscript.Script.byteHexChars, decodeHexChars?,
    hexNibble_hexDigit, hHigh, hLow]
  rw [byteHexValueUInt8]
  cases decodeHexChars? chars <;> rfl

private theorem decodeHexChars_byteHexChars (bytes : List UInt8) :
    decodeHexChars?
        (bytes.flatMap LeanMiniscript.Script.byteHexChars) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      rw [List.flatMap_cons, decodeHexChars_byteHexChars_append, ih]

private theorem decodeHex_byteArrayHex (bytes : ByteArray) :
    decodeHex? (LeanMiniscript.Script.byteArrayHex bytes) = some bytes := by
  rcases bytes with ⟨data⟩
  simp [decodeHex?, LeanMiniscript.Script.byteArrayHex,
    decodeHexChars_byteHexChars]

private theorem byteArrayHex_length (bytes : ByteArray) :
    (LeanMiniscript.Script.byteArrayHex bytes).length = bytes.size * 2 := by
  rcases bytes with ⟨data⟩
  rw [LeanMiniscript.Script.byteArrayHex, String.length_ofList,
    List.length_flatMap]
  have hTwo : ∀ values : List UInt8,
      (values.map (fun _ => 2)).sum = values.length * 2 := by
    intro values
    induction values with
    | nil => rfl
    | cons _ values ih => simp [ih, Nat.succ_mul]; omega
  simpa only [LeanMiniscript.Script.byteHexChars, List.length_cons,
    List.length_nil, Nat.zero_add, Array.length_toList, ByteArray.size]
    using hTwo data.toList

theorem parseNatRaw_toString
    (role : String) (position value : Nat) :
    parseNatRaw role (.atom position (toString value)) = .ok value := by
  simp [parseNatRaw, rawAtom, Nat.toNat?_repr]
  rfl

theorem parseNatRaw_repr
    (role : String) (position value : Nat) :
    parseNatRaw role (.atom position value.repr) = .ok value := by
  simp [parseNatRaw, rawAtom, Nat.toNat?_repr]
  rfl

private theorem atomCharSafe_of_digit_or_underscore (char : Char)
    (h : char.isDigit ∨ char = '_') :
    SurfaceText.isSpace char = false ∧
      SurfaceText.isPunctuation char = false := by
  rcases h with hDigit | rfl
  · have hBounds := Char.isDigit_iff_toNat.mp hDigit
    constructor
    · unfold SurfaceText.isSpace
      split <;> simp_all <;> omega
    · unfold SurfaceText.isPunctuation
      split <;> simp_all <;> omega
  · decide

theorem atomSafe_toString (value : Nat) :
    SurfaceText.AtomSafe (toString value) := by
  have hNat := String.isNat_iff.mp (Nat.isNat_repr value)
  constructor
  · change value.repr.toList ≠ []
    intro hEmpty
    exact hNat.1 (String.toList_eq_nil_iff.mp hEmpty)
  · intro char hMem
    exact atomCharSafe_of_digit_or_underscore char (hNat.2.1 char hMem)

private theorem byteHexChars_atomCharsSafe (byte : UInt8) :
    ∀ char ∈ LeanMiniscript.Script.byteHexChars byte,
      SurfaceText.isSpace char = false ∧
        SurfaceText.isPunctuation char = false := by
  have hAll : ∀ value : Fin 256,
      ∀ char ∈ LeanMiniscript.Script.byteHexChars (UInt8.ofNat value.val),
        SurfaceText.isSpace char = false ∧
          SurfaceText.isPunctuation char = false := by
    set_option maxRecDepth 100000 in
      decide
  simpa using hAll ⟨byte.toNat, byte.toNat_lt⟩

theorem atomSafe_byteArrayHex (bytes : ByteArray)
    (hPositive : 0 < bytes.size) :
    SurfaceText.AtomSafe (LeanMiniscript.Script.byteArrayHex bytes) := by
  unfold SurfaceText.AtomSafe LeanMiniscript.Script.byteArrayHex
  simp only [String.toList_ofList]
  constructor
  · intro hEmpty
    have hData : bytes.data.toList ≠ [] := by
      intro hDataEmpty
      have hLength : bytes.data.toList.length = [].length :=
        congrArg List.length hDataEmpty
      have hSizeZero : bytes.size = 0 := by
        change bytes.data.size = 0
        simpa only [Array.length_toList, List.length_nil] using hLength
      omega
    cases hBytes : bytes.data.toList with
    | nil => exact hData hBytes
    | cons byte tail =>
        simp [hBytes, LeanMiniscript.Script.byteHexChars] at hEmpty
  · intro char hMem
    simp only [List.mem_flatMap] at hMem
    obtain ⟨byte, _, hChar⟩ := hMem
    exact byteHexChars_atomCharsSafe byte char hChar


private theorem resolveHexKey_prettyPubKey (key : PubKey)
    (hSize : key.size = 32 ∨ key.size = 33) :
    resolveHexKey (prettyPubKey key) = .ok key := by
  have hAllowed : key.bytes.size * 2 = 64 ∨ key.bytes.size * 2 = 66 := by
    simp [PubKey.size] at hSize
    omega
  simp [resolveHexKey, prettyPubKey, byteArrayHex_length, hAllowed,
    decodeHex_byteArrayHex, PubKey.ofBytes]
  rfl

private theorem normalizeKeyForContext_of_valid
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    normalizeKeyForContext context key = some key := by
  cases context <;>
    simp_all [normalizeKeyForContext, validResolvedPubKey,
      validCompressedPubKeyBytes]

theorem resolveKeyRaw_prettyPubKey
    (context : ScriptContext) (position : Nat) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    resolveKeyRaw context resolveHexKey
        (.atom position (prettyPubKey key)) = .ok key := by
  have hSize : key.size = 32 ∨ key.size = 33 := by
    cases context with
    | p2wsh =>
        right
        exact hValid.1
    | tapscript => exact Or.inl hValid
  simp [resolveKeyRaw, rawAtom, resolveHexKey_prettyPubKey key hSize,
    normalizeKeyForContext_of_valid context key hValid]
  rfl

theorem parseHashBytes_byteArrayHex
    (role : String) (expectedLength position : Nat) (bytes : ByteArray)
    (hSize : bytes.size = expectedLength) :
    parseHashBytes role expectedLength
        (.atom position (LeanMiniscript.Script.byteArrayHex bytes)) =
      .ok bytes := by
  have hLength :
      (LeanMiniscript.Script.byteArrayHex bytes).length = expectedLength * 2 := by
    rw [byteArrayHex_length, hSize]
  simp [parseHashBytes, rawAtom, hLength, decodeHex_byteArrayHex, hSize]
  rfl

end SurfaceParser

end LeanMiniscript.Miniscript
