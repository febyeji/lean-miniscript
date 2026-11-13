import LeanMiniscript.Extraction.BitcoinCoreExecutionProofs

/-!
# Typed reading of script bytes

`decodeTypedScript?` reads script bytes as typed elements at Core's GetOp
boundaries. Every byte string has a reading (`decodeTypedScript?_isSome`), and
`decodeTypedScript` returns it.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- A raw instruction reads as a typed element when it encodes it, is the
byte of a `badOpcode` or an `illegalOpcode`, is the opcode and data of a
`nonminimalPush`, or is OP_CODESEPARATOR with its end offset. -/
def _root_.LeanMiniscript.Script.CoreRawInstruction.ReadsAs (instruction : CoreRawInstruction) :
    ScriptElement → Prop
  | .badOpcode opcode => instruction.opcode = opcode.byte ∧
      instruction.payload = ByteArray.empty
  | .illegalOpcode opcode => instruction.opcode = opcode.byte ∧
      instruction.payload = ByteArray.empty
  | .nonminimalPush push => instruction.opcode = push.opcode ∧
      instruction.payload = push.data
  | .codeSeparator nextOffset => instruction.opcode = 0xab ∧
      instruction.payload = ByteArray.empty ∧ nextOffset = instruction.nextOffset
  | element => instruction.Encodes element

instance (instruction : CoreRawInstruction) (element : ScriptElement) :
    Decidable (instruction.ReadsAs element) := by
  cases element <;> unfold CoreRawInstruction.ReadsAs <;> infer_instance

/-- The typed element a raw instruction reads as: a minimal push, a
`nonminimalPush`, a numeric constant, a modeled opcode, OP_CODESEPARATOR with
its end offset, or a `badOpcode` or `illegalOpcode` with the same byte.
`none` when the instruction reads as no typed element. -/
def typedElement? (instruction : CoreRawInstruction) : Option ScriptElement :=
  let value := instruction.opcode.toNat
  let candidate : Option ScriptElement :=
    if value ≤ 0x4e then
      if nonminimal : isNonminimalPush instruction.opcode instruction.payload then
        some (.nonminimalPush ⟨instruction.opcode, instruction.payload, nonminimal⟩)
      else some (.pushData instruction.payload)
    else if value == 0x4f then some (.pushNum (-1))
    else if 0x51 ≤ value && value ≤ 0x60 then some (.pushNum ((value : Int) - 0x50))
    else if value == 0xab then some (.codeSeparator instruction.nextOffset)
    else match opcodeFromByte? value with
      | some opcode => some (.op opcode)
      | none =>
          if bad : isBadOpcodeByte instruction.opcode then
            some (.badOpcode ⟨instruction.opcode, bad⟩)
          else if illegal : isIllegalOpcodeByte instruction.opcode then
            some (.illegalOpcode ⟨instruction.opcode, illegal⟩)
          else none
  match candidate with
  | some element => if instruction.ReadsAs element then some element else none
  | none => none

/-- Read `bytes` from `offset` to the end as typed elements, with Core's GetOp
boundaries. A push GetOp cannot read ends the reading as a `truncatedPush` of
the bytes from it to the end. `none` when an instruction has no typed
reading. -/
def decodeTypedScriptFrom (bytes : ByteArray) : Nat → Nat → Option Script
  | 0, _ => none
  | fuel + 1, offset =>
      if offset = bytes.size then some []
      else match readCoreRawInstruction bytes offset with
        | .error _ =>
            if truncated : offset < bytes.size ∧
                isTruncatedPush (bytes.extract offset bytes.size) then
              some [.truncatedPush ⟨bytes.extract offset bytes.size, truncated.2⟩]
            else none
        | .ok instruction =>
            if offset < bytes.size ∧ offset < instruction.nextOffset then
              match typedElement? instruction,
                  decodeTypedScriptFrom bytes fuel instruction.nextOffset with
              | some element, some rest => some (element :: rest)
              | _, _ => none
            else none

/-- The typed reading of a whole script. Every instruction advances, so
`bytes.size + 1` steps reach the end. -/
def decodeTypedScript? (bytes : ByteArray) : Option Script :=
  decodeTypedScriptFrom bytes (bytes.size + 1) 0

private theorem toList_loop (bytes : ByteArray) (i : Nat) (reversed : List UInt8) :
    ByteArray.toList.loop bytes i reversed = reversed.reverse ++ bytes.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bytes i reversed with
  | case1 i reversed inside ih =>
      rw [ih]
      have index : i < bytes.data.toList.length := by simpa using inside
      rw [List.drop_eq_getElem_cons index]
      simp [ByteArray.get!, getElem!_pos bytes.data i (by simpa using inside)]
  | case2 i reversed outside =>
      have : bytes.data.toList.length ≤ i := by simp; omega
      simp [List.drop_eq_nil_of_le this]

private theorem toList_extract_end (bytes : ByteArray) (offset : Nat) :
    (bytes.extract offset bytes.size).toList = bytes.data.toList.drop offset := by
  rw [ByteArray.toList, toList_loop, ByteArray.data_extract, Array.toList_extract]
  simp only [List.reverse_nil, List.nil_append, List.drop_zero]
  apply List.take_of_length_le
  simp

/-- The little-endian value of `width` bytes from `start`, as GetOp reads a
push length. -/
private abbrev littleEndian (bytes : ByteArray) (start width : Nat) : Nat :=
  (List.range width).foldl (fun size i => size + bytes[start + i]!.toNat * 256 ^ i) 0

private theorem foldl_add_start (g : Nat → Nat) (start : Nat) (indices : List Nat) :
    indices.foldl (fun size i => size + g i) start =
      start + indices.foldl (fun size i => size + g i) 0 := by
  induction indices generalizing start with
  | nil => simp
  | cons i rest ih => simp only [List.foldl_cons]; rw [ih, ih (0 + g i)]; omega

private theorem littleEndian_lt (bytes : ByteArray) (start width : Nat) :
    littleEndian bytes start width < 256 ^ width := by
  induction width with
  | zero => simp [littleEndian]
  | succ width ih =>
      simp only [littleEndian, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at ih ⊢
      have byte := UInt8.toNat_lt bytes[start + width]!
      have scaled : bytes[start + width]!.toNat * 256 ^ width ≤ 255 * 256 ^ width :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.pow_succ]
      omega

private theorem littleEndian_succ (bytes : ByteArray) (start width : Nat) :
    littleEndian bytes start (width + 1) =
      bytes[start]!.toNat + 256 * littleEndian bytes (start + 1) width := by
  simp only [littleEndian, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  rw [foldl_add_start]
  congr 1
  · simp
  · induction width with
    | zero => simp
    | succ width ih =>
        simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
        rw [ih, Nat.pow_succ, show start + (width + 1) = start + 1 + width by omega]
        simp only [Nat.mul_add, Nat.mul_comm]
        rw [Nat.mul_assoc]

/-- `isTruncatedPush` reads the length field of the bytes as GetOp does. -/
private theorem foldr_take_drop (bytes : ByteArray) (start width : Nat)
    (fits : start + width ≤ bytes.size) :
    ((bytes.data.toList.drop start).take width).foldr
        (fun byte size => byte.toNat + 256 * size) 0 = littleEndian bytes start width := by
  induction width generalizing start with
  | zero => simp [littleEndian]
  | succ width ih =>
      have index : start < bytes.data.toList.length := by simp; omega
      rw [List.drop_eq_getElem_cons index, List.take_succ_cons, List.foldr_cons,
        ih (start + 1) (by omega), littleEndian_succ]
      simp only [getElem!_pos bytes start (by omega), ByteArray.getElem_eq_getElem_data,
        Array.getElem_toList]
      rfl

/-- GetOp reads an instruction that starts inside the bytes and ends after its
start, at or before their end. -/
theorem readCoreRawInstruction_bounds {bytes : ByteArray} {offset : Nat}
    {instruction : CoreRawInstruction}
    (read : readCoreRawInstruction bytes offset = .ok instruction) :
    offset < bytes.size ∧ offset < instruction.nextOffset ∧
      instruction.nextOffset ≤ bytes.size := by
  unfold readCoreRawInstruction at read
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at read
  repeat' (split at read)
  all_goals first
    | (cases read; done)
    | (cases read; refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> omega)

/-- An opcode above OP_PUSHDATA4 carries no data. -/
theorem readCoreRawInstruction_high {bytes : ByteArray} {offset : Nat}
    {instruction : CoreRawInstruction}
    (read : readCoreRawInstruction bytes offset = .ok instruction)
    (high : 0x4e < instruction.opcode.toNat) : instruction.payload = ByteArray.empty := by
  unfold readCoreRawInstruction at read
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at read
  repeat' (split at read)
  all_goals first
    | (cases read; done)
    | (cases read; rfl)
    | (cases read; simp only at high; omega)

/-- A push carries as many bytes as its length field holds. -/
theorem readCoreRawInstruction_push {bytes : ByteArray} {offset : Nat}
    {instruction : CoreRawInstruction}
    (read : readCoreRawInstruction bytes offset = .ok instruction) :
    (instruction.opcode.toNat ≤ 0x4b → instruction.payload.size = instruction.opcode.toNat) ∧
    (instruction.opcode.toNat = 0x4c → instruction.payload.size < 0x100) ∧
    (instruction.opcode.toNat = 0x4d → instruction.payload.size < 0x10000) ∧
    instruction.payload.size < 0x100000000 := by
  have one := littleEndian_lt bytes (offset + 1) 1
  have two := littleEndian_lt bytes (offset + 1) 2
  have four := littleEndian_lt bytes (offset + 1) 4
  simp only [littleEndian, Nat.reducePow] at one two four
  unfold readCoreRawInstruction at read
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at read
  repeat' (split at read)
  all_goals first
    | (cases read; done)
    | (cases read
       simp only [ByteArray.size_extract, ByteArray.size_empty, beq_iff_eq,
         not_true_eq_false] at * <;> omega)

/-- Where GetOp fails inside the bytes, they hold a truncated push from there
to the end. -/
theorem readCoreRawInstruction_truncated {bytes : ByteArray} {offset : Nat} {error : ScriptError}
    (read : readCoreRawInstruction bytes offset = .error error) (inside : offset < bytes.size) :
    isTruncatedPush (bytes.extract offset bytes.size) = true := by
  have index : offset < bytes.data.toList.length := by simpa using inside
  have head : bytes.data.toList[offset] = bytes[offset]! := by
    rw [getElem!_pos bytes offset inside, ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    rfl
  have length : (bytes.data.toList.drop (offset + 1)).length = bytes.size - (offset + 1) := by
    simp
  rw [isTruncatedPush, toList_extract_end, List.drop_eq_getElem_cons index, head]
  dsimp only
  rw [length]
  unfold readCoreRawInstruction at read
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at read
  repeat' (split at read)
  all_goals first
    | (cases read; done)
    | omega
    | skip
  all_goals
    try simp only [beq_iff_eq, not_true_eq_false] at *
  all_goals
    repeat' split
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    first
      | omega
      | (rw [foldr_take_drop bytes (offset + 1) _ (by omega)]
         simp only [littleEndian] at *
         omega)

/-- Every byte above OP_PUSHDATA4 reads as a number, OP_CODESEPARATOR, a
modeled opcode with the same byte, or a `badOpcode` or `illegalOpcode`. -/
private def opcodeByteReads (value : Nat) : Bool :=
  value == 0x4f || (0x51 ≤ value && value ≤ 0x60) || value == 0xab ||
    match opcodeFromByte? value with
    | some opcode => (opcodeByte opcode).toNat == value
    | none => isBadOpcodeByte value.toUInt8 || isIllegalOpcodeByte value.toUInt8

private theorem opcodeByteReads_all : ∀ value, value < 256 → 0x4e < value →
    opcodeByteReads value = true := by
  decide +kernel

/-- Every instruction GetOp reads has a typed element. -/
theorem typedElement?_isSome {bytes : ByteArray} {offset : Nat}
    {instruction : CoreRawInstruction}
    (read : readCoreRawInstruction bytes offset = .ok instruction) :
    (typedElement? instruction).isSome = true := by
  have byte := UInt8.toNat_lt instruction.opcode
  by_cases push : instruction.opcode.toNat ≤ 0x4e
  · obtain ⟨short, one, two, four⟩ := readCoreRawInstruction_push read
    by_cases nonminimal : isNonminimalPush instruction.opcode instruction.payload = true
    · simp [typedElement?, push, nonminimal, CoreRawInstruction.ReadsAs]
    · have minimal : coreLegacyMinimalPush instruction.opcode.toNat instruction.payload = true := by
        cases isMinimal : isMinimalPush instruction.opcode.toNat instruction.payload
        · exfalso
          apply nonminimal
          simp only [isNonminimalPush, isMinimal, Bool.not_false, Bool.and_true]
          repeat' split
          all_goals
            try simp only [beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at *
          all_goals omega
        · exact isMinimal
      have encodes := CoreRawInstruction.encodes_pushData push minimal
      simp [typedElement?, push, nonminimal, CoreRawInstruction.ReadsAs, encodes]
  · have empty := readCoreRawInstruction_high read (by omega)
    have reads := opcodeByteReads_all instruction.opcode.toNat byte (by omega)
    by_cases negative : instruction.opcode.toNat = 0x4f
    · have encodes := CoreRawInstruction.encodes_pushNum empty (Or.inl negative)
      simp only [negative, ↓reduceIte] at encodes
      simp [typedElement?, negative, CoreRawInstruction.ReadsAs, encodes]
    · by_cases small : 0x51 ≤ instruction.opcode.toNat ∧ instruction.opcode.toNat ≤ 0x60
      · have encodes := CoreRawInstruction.encodes_pushNum empty (Or.inr small)
        simp only [negative, ↓reduceIte] at encodes
        simp [typedElement?, push, negative, small, CoreRawInstruction.ReadsAs, encodes]
      · by_cases separator : instruction.opcode.toNat = 0xab
        · have opcode : instruction.opcode = 0xab := UInt8.toNat_inj.mp separator
          simp [typedElement?, CoreRawInstruction.ReadsAs, opcode, empty]
        · cases modeled : opcodeFromByte? instruction.opcode.toNat with
          | some opcode =>
              simp [opcodeByteReads, negative, small, separator, modeled] at reads
              have same : instruction.opcode = opcodeByte opcode := (UInt8.toNat_inj.mp reads).symm
              simp [typedElement?, push, negative, small, separator, modeled,
                CoreRawInstruction.ReadsAs, CoreRawInstruction.Encodes, empty]
              exact same
          | none =>
              simp [opcodeByteReads, negative, small, separator, modeled] at reads
              by_cases bad : isBadOpcodeByte instruction.opcode = true
              · simp [typedElement?, push, negative, small, separator, modeled, bad,
                  CoreRawInstruction.ReadsAs, empty]
              · have illegal : isIllegalOpcodeByte instruction.opcode = true := by
                  simpa [bad] using reads
                simp [typedElement?, push, negative, small, separator, modeled, bad, illegal,
                  CoreRawInstruction.ReadsAs, empty]

/-- From an offset inside the bytes, enough fuel reads every remaining byte. -/
theorem decodeTypedScriptFrom_isSome (bytes : ByteArray) (fuel offset : Nat)
    (inside : offset ≤ bytes.size) (enough : bytes.size - offset < fuel) :
    (decodeTypedScriptFrom bytes fuel offset).isSome = true := by
  induction fuel generalizing offset with
  | zero => omega
  | succ fuel ih =>
      unfold decodeTypedScriptFrom
      by_cases finished : offset = bytes.size
      · simp [finished]
      · simp only [finished, ↓reduceIte]
        cases read : readCoreRawInstruction bytes offset with
        | error error =>
            have truncated := readCoreRawInstruction_truncated read (by omega)
            simp [show offset < bytes.size by omega, truncated]
        | ok instruction =>
            obtain ⟨start, advance, within⟩ := readCoreRawInstruction_bounds read
            have element := typedElement?_isSome read
            have rest := ih instruction.nextOffset within (by omega)
            simp only [start, advance, and_self, ↓reduceIte]
            cases typed : typedElement? instruction <;>
              cases decoded : decodeTypedScriptFrom bytes fuel instruction.nextOffset <;>
              simp_all

/-- Every byte string has a typed reading. -/
theorem decodeTypedScript?_isSome (bytes : ByteArray) : (decodeTypedScript? bytes).isSome = true :=
  decodeTypedScriptFrom_isSome bytes _ 0 (Nat.zero_le _) (by omega)

/-- The typed reading of a whole script. -/
def decodeTypedScript (bytes : ByteArray) : Script :=
  (decodeTypedScript? bytes).get (decodeTypedScript?_isSome bytes)

theorem decodeTypedScript?_eq (bytes : ByteArray) :
    decodeTypedScript? bytes = some (decodeTypedScript bytes) :=
  (Option.some_get _).symm

end LeanMiniscript.Extraction
