import LeanMiniscript.Psbt.CodecProofs
import LeanMiniscript.Psbt.Fields

namespace LeanMiniscript.Psbt

/-!
# Validated PSBT parsing round trips

`Psbt.parse` is framing followed by full field and version validation. A
well-formed PSBT that decodes is recovered exactly from its serialization,
and every accepted byte string is exactly the serialization of the PSBT it
yields, which is well formed and decodes.
-/

theorem globalCounts_of_decode {psbt : Psbt} {decoded : DecodedPsbt}
    (decodes : psbt.decode = .ok decoded) :
    globalCounts psbt.global = .ok (psbt.inputs.length, psbt.outputs.length) := by
  unfold Psbt.decode at decodes
  cases global : decodeGlobal psbt.global with
  | error error => simp [global, bind, Except.bind] at decodes
  | ok fields =>
    simp only [global, bind, Except.bind] at decodes
    split at decodes
    · simp [throw, throwThe, MonadExceptOf.throw] at decodes
    · rename_i same
      simp only [ne_eq, Decidable.not_not] at same
      simp [globalCounts, global, bind, Except.bind, pure, Except.pure, same]

/-- Serialization followed by validated parsing is the identity on
well-formed PSBTs that decode. -/
theorem Psbt.parse_serialize {psbt : Psbt} {decoded : DecodedPsbt}
    (formed : psbt.WellFormed) (decodes : psbt.decode = .ok decoded) :
    Psbt.parse psbt.serialize = .ok psbt := by
  unfold Psbt.parse
  rw [Psbt.serialize_data, decodePsbtWith_encode globalCounts formed (globalCounts_of_decode decodes)]
  simp [bind, Except.bind, decodes, pure, Except.pure]

/-- Every accepted byte string is the serialization of the parsed PSBT,
which is well formed and decodes. -/
theorem Psbt.serialize_parse {bytes : ByteArray} {psbt : Psbt}
    (parsed : Psbt.parse bytes = .ok psbt) :
    psbt.serialize = bytes ∧ psbt.WellFormed ∧ ∃ decoded, psbt.decode = .ok decoded := by
  unfold Psbt.parse at parsed
  cases framed : decodePsbtWith globalCounts bytes.data.toList with
  | error error => simp [framed, bind, Except.bind] at parsed
  | ok raw =>
    simp only [framed, bind, Except.bind] at parsed
    cases decodes : raw.decode with
    | error error => simp [decodes] at parsed
    | ok decoded =>
      simp only [decodes, pure, Except.pure, Except.ok.injEq] at parsed
      subst parsed
      obtain ⟨encoded, formed, _⟩ := decodePsbtWith_ok globalCounts framed
      refine ⟨?_, formed, decoded, decodes⟩
      apply ByteArray.ext
      rw [Psbt.serialize]
      simp [← encoded]

/-- Parsing a serialization of a parsed PSBT returns it again. -/
theorem Psbt.parse_idempotent {bytes : ByteArray} {psbt : Psbt}
    (parsed : Psbt.parse bytes = .ok psbt) : Psbt.parse psbt.serialize = .ok psbt := by
  rw [(Psbt.serialize_parse parsed).1]
  exact parsed

end LeanMiniscript.Psbt
