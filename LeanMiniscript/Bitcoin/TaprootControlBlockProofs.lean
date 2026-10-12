import LeanMiniscript.Bitcoin.TaprootControlBlock

namespace LeanMiniscript.Bitcoin

private theorem appendFold_size (path : List ByteArray) (leading : ByteArray)
    (sizes : ∀ hash ∈ path, hash.size = 32) :
    (path.foldl (· ++ ·) leading).size = leading.size + 32 * path.length := by
  induction path generalizing leading with
  | nil => simp
  | cons hash rest ih =>
      rw [List.foldl_cons, ih _ (by intro item member; exact sizes item (by simp [member]))]
      simp only [List.length_cons, ByteArray.size_append]
      have hashSize := sizes hash (by simp)
      omega

private theorem appendFold_extract_prefix (path : List ByteArray) (leading : ByteArray)
    (start stop : Nat) (bound : stop ≤ leading.size) :
    (path.foldl (· ++ ·) leading).extract start stop = leading.extract start stop := by
  induction path generalizing leading with
  | nil => rfl
  | cons hash rest ih =>
      rw [List.foldl_cons, ih _ (by simp only [ByteArray.size_append]; omega),
        ByteArray.extract_append]
      have empty : hash.extract (start - leading.size) (stop - leading.size) =
          ByteArray.empty := by
        apply ByteArray.extract_eq_empty_iff.mpr
        omega
      simp [empty]

private theorem appendFold_chunks (path : List ByteArray) (leading : ByteArray)
    (sizes : ∀ hash ∈ path, hash.size = 32) :
    (List.range path.length).map (fun i =>
      (path.foldl (· ++ ·) leading).extract
        (leading.size + 32 * i) (leading.size + 32 * (i + 1))) = path := by
  induction path generalizing leading with
  | nil => simp
  | cons hash rest ih =>
      have hashSize := sizes hash (by simp)
      have restSizes : ∀ item ∈ rest, item.size = 32 := by
        intro item member
        exact sizes item (by simp [member])
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, Function.comp_def, List.foldl_cons]
      congr 1
      · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
        rw [appendFold_extract_prefix _ _ _ _ (by simp [hashSize])]
        exact ByteArray.extract_append_eq_right rfl (by simp [hashSize])
      · apply Eq.trans ?_ (ih (leading ++ hash) restSizes)
        apply congrArg (fun f => (List.range rest.length).map f)
        funext i
        congr 1 <;> simp only [ByteArray.size_append, hashSize] <;> omega

private theorem appendFold_eq (path : List ByteArray) (leading : ByteArray) :
    path.foldl (· ++ ·) leading = leading ++ path.foldl (· ++ ·) ByteArray.empty := by
  induction path generalizing leading with
  | nil => simp
  | cons hash rest ih =>
      simp only [List.foldl_cons, ByteArray.empty_append]
      rw [ih (leading ++ hash), ih hash, ByteArray.append_assoc]

/-- Parsing a serialized version-0xc0 control block recovers its key, parity,
and every sibling hash, including empty paths and the 128-sibling boundary. -/
theorem parseTaprootControlBlock_serialized
    (internalKey : ByteArray) (outputParity : Bool) (path : List ByteArray)
    (keySize : internalKey.size = 32) (depth : path.length ≤ 128)
    (sizes : ∀ hash ∈ path, hash.size = 32) :
    parseTaprootControlBlock (path.foldl (· ++ ·)
      (ByteArray.mk #[if outputParity then 0xc1 else 0xc0] ++ internalKey)) =
      .ok { leafVersion := 0xc0, outputParity, internalKey, merklePath := path } := by
  let leading := ByteArray.mk #[if outputParity then 0xc1 else 0xc0] ++ internalKey
  have prefixSize : leading.size = 33 := by
    rw [ByteArray.size_append]
    change 1 + internalKey.size = 33
    omega
  have size := appendFold_size path leading sizes
  rw [prefixSize] at size
  have count : ((path.foldl (· ++ ·) leading).size - 33) / 32 = path.length := by omega
  have valid : ¬((path.foldl (· ++ ·) leading).size < 33 ∨
      (path.foldl (· ++ ·) leading).size > 4129 ∨
      ((path.foldl (· ++ ·) leading).size - 33) % 32 ≠ 0) := by omega
  have key : (path.foldl (· ++ ·) leading).extract 1 33 = internalKey := by
    rw [appendFold_extract_prefix _ _ _ _ (by omega)]
    exact ByteArray.extract_append_eq_right rfl (by change 33 = 1 + internalKey.size; omega)
  have chunks := appendFold_chunks path leading sizes
  simp only [prefixSize] at chunks
  have first : (path.foldl (· ++ ·) leading)[0]! =
      (if outputParity then 0xc1 else 0xc0 : UInt8) := by
    rw [appendFold_eq]
    rw [getElem!_pos _ _ (by simp only [ByteArray.size_append, prefixSize]; omega)]
    rw [ByteArray.getElem_append_left (by omega)]
    change (ByteArray.mk #[if outputParity then 0xc1 else 0xc0] ++ internalKey)[0] = _
    rw [ByteArray.getElem_append_left (by change 0 < 1; decide)]
    rfl
  change parseTaprootControlBlock (path.foldl (· ++ ·) leading) = _
  unfold parseTaprootControlBlock
  simp only [Bool.or_eq_true, decide_eq_true_eq] at *
  rw [if_neg (by simpa only [or_assoc] using valid), first, key, count]
  have chunks' : (List.range path.length).map (fun i =>
      (path.foldl (· ++ ·) leading).extract (33 + 32 * i) (65 + 32 * i)) = path := by
    apply Eq.trans ?_ chunks
    apply congrArg (fun f => (List.range path.length).map f)
    funext i
    congr 1 <;> omega
  rw [chunks']
  cases outputParity <;> rfl

/-- The executable hash emits eight four-byte words. This states its output
length without a claim about SHA256's cryptographic properties. -/
theorem sha256_size (bytes : ByteArray) :
    (LeanHash160.SHA256.hash bytes).size = 32 := by
  change (List.foldl (LeanHash160.Internal.appendUInt32 .big) ByteArray.empty
    [_, _, _, _, _, _, _, _]).size = 32
  simp [List.foldl, LeanHash160.Internal.appendUInt32, ByteArray.size_push, List.range']

@[simp] theorem taggedHash_size (tag : String) (message : ByteArray) :
    (taggedHash tag message).size = 32 :=
  sha256_size _

@[simp] theorem tapleafHash_size (script : ByteArray) (version : UInt8) :
    (tapleafHash script version).size = 32 :=
  taggedHash_size _ _

@[simp] theorem tapbranchHash_size (left right : ByteArray) :
    (tapbranchHash left right).size = 32 :=
  taggedHash_size _ _

private theorem byteFold_injective (xs ys : List UInt8)
    (sizeEq : xs.length = ys.length)
    (valueEq : xs.foldr (fun byte value => 256 * value + byte.toNat) 0 =
      ys.foldr (fun byte value => 256 * value + byte.toNat) 0) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using sizeEq.symm
  | cons x xs ih =>
      cases ys with
      | nil => simp at sizeEq
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at sizeEq
          simp only [List.foldr_cons] at valueEq
          have xBound := x.toNat_lt
          have yBound := y.toNat_lt
          have digits : x.toNat = y.toNat := by omega
          have tails : xs.foldr (fun byte value => 256 * value + byte.toNat) 0 =
              ys.foldr (fun byte value => 256 * value + byte.toNat) 0 := by omega
          rw [UInt8.toNat_inj.mp digits, ih ys sizeEq tails]

/-- Big-endian decoding is injective for byte arrays of equal length. -/
theorem decodeBE_injective_of_size_eq {left right : ByteArray}
    (sizeEq : left.size = right.size)
    (valueEq : Secp256k1.decodeBE left = Secp256k1.decodeBE right) :
    left = right := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have lengths : left.data.toList.reverse.length = right.data.toList.reverse.length := by
    simpa only [List.length_reverse, Array.length_toList, ByteArray.size_data] using sizeEq
  have values : left.data.toList.reverse.foldr (fun byte value => 256 * value + byte.toNat) 0 =
      right.data.toList.reverse.foldr (fun byte value => 256 * value + byte.toNat) 0 := by
    rw [List.foldr_reverse, List.foldr_reverse, Array.foldl_toList, Array.foldl_toList]
    exact valueEq
  exact List.reverse_inj.mp (byteFold_injective _ _ lengths values)

/-- Sorting makes a branch independent of child order for equal-length hashes,
including identical child hashes. -/
theorem tapbranchHash_comm {left right : ByteArray}
    (sizeEq : left.size = right.size) :
    tapbranchHash left right = tapbranchHash right left := by
  unfold tapbranchHash
  rcases Nat.lt_trichotomy (Secp256k1.decodeBE left) (Secp256k1.decodeBE right) with
    less | equal | greater
  · simp [less, Nat.not_lt_of_ge (Nat.le_of_lt less)]
  · rw [decodeBE_injective_of_size_eq sizeEq equal]
  · simp [greater, Nat.not_lt_of_ge (Nat.le_of_lt greater)]

private theorem decodeDigits_prefix (width value count : Nat)
    (bound : value < 256 ^ width) (countBound : count ≤ width) :
    (List.range count).foldl (fun acc i =>
      256 * acc + (UInt8.ofNat (value / 256 ^ (width - 1 - i))).toNat) 0 =
      value / 256 ^ (width - count) := by
  induction count with
  | zero => simp [Nat.div_eq_of_lt bound]
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
      have exponent : width - count = (width - 1 - count) + 1 := by omega
      rw [exponent, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      simp only [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.div_add_mod]
      have same : width - 1 - count = width - (count + 1) := by omega
      rw [same]

/-- Fixed-width big-endian encoding recovers any value that fits in the width. -/
theorem decodeBE_fixedWidth (width value : Nat) (bound : value < 256 ^ width) :
    Secp256k1.decodeBE ⟨(List.range width).toArray.map
      (fun i => UInt8.ofNat (value / 256 ^ (width - 1 - i)))⟩ = value := by
  unfold Secp256k1.decodeBE
  rw [Array.foldl_map, List.foldl_toArray]
  simpa using decodeDigits_prefix width value width bound (by omega)

private theorem pointAdd_x_lt {left result : Nat × Nat} (right : Secp256k1.Point)
    (leftBound : left.1 < Secp256k1.field)
    (added : Secp256k1.pointAdd (some left) right = some result) :
    result.1 < Secp256k1.field := by
  rcases left with ⟨x, y⟩
  cases right with
  | none => cases added; exact leftBound
  | some point =>
      rcases point with ⟨u, v⟩
      simp only [Secp256k1.pointAdd] at added
      split at added
      · cases added
      · cases added
        exact Nat.mod_lt _ (by decide)

private theorem liftX_x_lt {x : Nat} {point : Nat × Nat}
    (lifted : Secp256k1.liftX x = some point) :
    point.1 < Secp256k1.field := by
  simp only [Secp256k1.liftX] at lifted
  split at lifted
  · cases lifted
  · split at lifted
    · cases lifted
    · cases lifted; omega

/-- Successful tweaking checks the internal-key width and returns a canonical
X coordinate. This states a numeric bound on the executable arithmetic. -/
theorem taprootTweakPoint_bounds {internalKey tweak : ByteArray} {point : Nat × Nat}
    (tweaked : taprootTweakPoint internalKey tweak = .ok point) :
    internalKey.size = 32 ∧ point.1 < Secp256k1.field := by
  unfold taprootTweakPoint at tweaked
  simp only [bind, Except.bind, pure, Except.pure] at tweaked
  split at tweaked
  · cases tweaked
  · rename_i keySize
    split at tweaked
    · cases tweaked
    · split at tweaked
      · cases tweaked
      · split at tweaked
        · cases tweaked
        · rename_i liftedPoint lifted
          split at tweaked
          · cases tweaked
          · rename_i result added
            cases tweaked
            exact ⟨by omega, pointAdd_x_lt _ (liftX_x_lt lifted) added⟩

/-- A serialized control block passes the executable commitment verifier when
the output bytes encode the same successful tweak. Hashing and curve operations
are shared with that verifier; their cryptographic correctness is not assumed. -/
theorem verifyTaprootControlBlock_serialized
    (internalKey outputKey script : ByteArray) (path : List ByteArray) (point : Nat × Nat)
    (depth : path.length ≤ 128) (sizes : ∀ hash ∈ path, hash.size = 32)
    (outputSize : outputKey.size = 32) (outputX : Secp256k1.decodeBE outputKey = point.1)
    (tweaked : taprootTweakPoint internalKey
      (taggedHash "TapTweak" (internalKey ++ path.foldl tapbranchHash (tapleafHash script 0xc0))) =
      .ok point) :
    verifyTaprootControlBlock outputKey script (path.foldl (· ++ ·)
      (ByteArray.mk #[if point.2 % 2 == 1 then 0xc1 else 0xc0] ++ internalKey)) =
      .ok {
        leafVersion := 0xc0
        leafHash := tapleafHash script 0xc0
        merkleRoot := path.foldl tapbranchHash (tapleafHash script 0xc0) } := by
  have keySize := (taprootTweakPoint_bounds tweaked).1
  rw [verifyTaprootControlBlock,
    parseTaprootControlBlock_serialized internalKey _ path keySize depth sizes]
  simp only [bind, Except.bind, outputSize, ne_eq, not_true_eq_false, ↓reduceIte,
    taprootControlMerkleRoot, tweaked]
  rcases point with ⟨x, y⟩
  simp [outputX, pure, Except.pure]

end LeanMiniscript.Bitcoin
