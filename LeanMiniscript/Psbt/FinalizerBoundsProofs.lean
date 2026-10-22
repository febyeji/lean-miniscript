import LeanMiniscript.Psbt.Finalizer
import LeanMiniscript.Psbt.ProofSupport

namespace LeanMiniscript.Psbt

/-- The length check returns its input exactly when its witness fits CompactSize. -/
theorem FinalInput.checkWitness_eq_ok {final result : FinalInput} :
    final.checkWitness = .ok result ↔ final = result ∧ final.WitnessFits := by
  unfold FinalInput.checkWitness
  split <;> simp_all [FinalInput.WitnessFits, List.all_eq_true]
  intro same
  subst result
  assumption

theorem checkWitness_bind_eq_ok {operation : Except FinalizeError FinalInput} {final : FinalInput} :
    (operation >>= FinalInput.checkWitness) = .ok final ↔
      operation = .ok final ∧ final.WitnessFits := by
  rw [bind_eq_ok]
  simp only [FinalInput.checkWitness_eq_ok]
  constructor
  · rintro ⟨value, produced, rfl, fits⟩
    exact ⟨produced, fits⟩
  · rintro ⟨produced, fits⟩
    exact ⟨final, produced, rfl, fits⟩

/-- Every generated final input satisfies the witness serialization bounds. -/
theorem DecodedPsbt.finalInput_witnessFits {config : FinalizerConfig} {decoded : DecodedPsbt}
    {index : Nat} {descriptor : LeanMiniscript.Miniscript.OutputDescriptor} {final : FinalInput}
    (produced : decoded.finalInput config index descriptor = .ok final) : final.WitnessFits := by
  unfold DecodedPsbt.finalInput at produced
  rw [bind_eq_ok] at produced
  rcases produced with ⟨input, _, produced⟩
  cases agreed : input.sighashTypesMatch with
  | false => simp [agreed, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at produced
  | true =>
    simp only [agreed, Bool.not_true, Bool.false_eq_true, if_false] at produced
    cases descriptor
    all_goals first
      | (solve | cases produced)
      | (rw [bind_eq_ok] at produced
         rcases produced with ⟨result, _, checked⟩
         obtain ⟨rfl, fits⟩ := FinalInput.checkWitness_eq_ok.mp checked
         exact fits)

end LeanMiniscript.Psbt
