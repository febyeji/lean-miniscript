import LeanMiniscript.Extraction.TapscriptWitnessMaterial
import LeanMiniscript.Miniscript.CompileAltStackProofs
import LeanMiniscript.Miniscript.SatisfactionProofs.Atomic

/-! Recovery of a Tapscript hash-lock frame under local public-material assumptions. -/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Miniscript

/-- A single item taken from an eligible witness meets each third-party clause. -/
theorem ThirdPartyWitness.singleton_of_mem {root : CoreFragment} {ctx : TxContext}
    {arguments other : Witness} (third : ThirdPartyWitness root ctx arguments other)
    {item : StackElement} (mem : item ∈ other) :
    ThirdPartyWitness root ctx arguments [item] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro x hx; obtain rfl := List.mem_singleton.mp hx
  · exact third.1 _ mem
  · exact third.2.1 _ mem
  · exact third.2.2.1 _ mem
  · exact third.2.2.2 _ mem

/-- Singleton eligibility on the published items is exactly the hypothesis for
    lookup recovery in every third-party witness, including unselected locks. -/
theorem hash_slot_recovery_iff {root : CoreFragment} {env : SatEnv} {arguments : Witness} :
    LocalHashSlotRecovery root env arguments ↔
      ∀ other, ThirdPartyWitness root env.txCtx arguments other → ∀ item ∈ other,
        ∀ lock ∈ root.hashLocks, lock.Matches item → env.preimageFor lock = some item := by
  constructor
  · intro recover other third item mem lock present matched
    exact recover item (third.2.2.1 item mem lock present matched)
      (third.singleton_of_mem mem) lock present matched
  · intro recover item _ eligible lock present matched
    exact recover [item] eligible item (.head _) lock present matched

namespace TapscriptWitness

private theorem size32_input {tailScript : Script} {input alt output finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext} (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval (.op .OP_SIZE :: .pushNum 32 :: .op .OP_EQUALVERIFY :: tailScript)
      input alt flags ctx (.success output finalAlt)) :
    ∃ item tail, input = item :: tail ∧ item.size = 32 := by
  cases run with
  | size x _ _ _ _ _ _ inner =>
    cases inner with
    | pushNum _ _ _ _ _ _ _ inner =>
      cases inner with
      | equalverify_success _ _ _ _ _ _ _ _ sizeEq _ =>
        have decoded := decodeScriptNum_scriptNat_of_le_maxScriptElementSize
          (bounded x (.head _)) false
        have fixed := decodeScriptNum_scriptNat_of_lt (n := 32) (by decide) false
        rw [← sizeEq] at decoded
        exact ⟨x, _, rfl, Int.ofNat_inj.mp (Except.ok.inj (decoded.symm.trans fixed))⟩
      | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => cases upgradable
  | upgradeableNop _ _ _ _ _ _ _ upgradable _ _ => cases upgradable

/-- All four hash-lock opcodes consume one matching 32-byte item on a true
    run and preserve the remainder of the stack. -/
theorem hashLock_frame {lock : HashLock} {input rest alt finalAlt : Stack} {top : StackElement}
    {flags : ScriptFlags} {ctx : TxContext} (bounded : ∀ item ∈ input, item.size ≤ maxScriptElementSize)
    (run : Eval (compile lock.fragment) input alt flags ctx (.success (top :: rest) finalAlt))
    (truth : castToBool top = true) :
    ∃ item, input = item :: rest ∧ lock.Matches item := by
  have sized : ∃ item tail, input = item :: tail ∧ item.size = 32 := by
    cases lock <;> exact size32_input bounded run
  obtain ⟨item, tail, rfl, size⟩ := sized
  by_cases digest : lock.digest item = lock.expected
  · have matched : lock.Matches item := ⟨size, digest⟩
    have same := Eval.result_unique run (hash_satisfaction_execution matched tail alt)
    cases same
    exact ⟨item, rfl, matched⟩
  · have mismatched : lock.Mismatches item := ⟨size, digest⟩
    have same := Eval.result_unique run (hash_dissatisfaction_execution mismatched tail alt)
    cases same
    contradiction

end TapscriptWitness
end LeanMiniscript.Extraction
