import LeanMiniscript.Miniscript.SatisfactionGeneratedRecursiveProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-! The recursive theorem replaces constructor-by-constructor contract
assembly once validation and typing have been established. -/

/-- A nested guarded conditional is closed by one recursive theorem call. -/
example {env : SatEnv} {flags : ScriptFlags}
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates
      (.andor (.d (.v .one)) .one .zero) env).SupportsGeneratedContract
      .tapscript (.andor (.d (.v .one)) .one .zero)
        ⟨.B, { o := true, d := true, u := true }⟩ flags env.txCtx := by
  have typed : HasType .tapscript (.andor (.d (.v .one)) .one .zero)
      ⟨.B, { o := true, d := true, u := true }⟩ := by
    exact .andor (.d_wrap (.v_wrap .one) rfl) rfl rfl .one .zero
      (by simp [branchBase]) rfl
  exact supportsGeneratedContract_of_wellFormed_hasType version modeled sound
    encodings typed (by native_decide)

/-- A concrete arithmetic-safe threshold reaches its recursively assembled
    source-order child contract. -/
example {env : SatEnv} {flags : ScriptFlags}
    (version : ModeledContextVersion .p2wsh env.txCtx)
    (modeled : ModeledContextFlags .p2wsh flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.thresh 1 [.zero]) env).SupportsGeneratedContract
      .p2wsh (.thresh 1 [.zero])
        ⟨.B, { z := true, d := true, u := true }⟩ flags env.txCtx := by
  have typed : HasType .p2wsh (.thresh 1 [.zero])
      ⟨.B, { z := true, d := true, u := true }⟩ := by
    exact .thresh .zero rfl rfl .nil trivial (by decide) (by decide)
  exact supportsGeneratedContract_of_wellFormed_hasType version modeled sound
    encodings typed (by native_decide)

/-- An arithmetic-unsafe typed threshold has an empty candidate pair; the
    recursive contract therefore supports both projections vacuously while
    retaining its global typing derivation. -/
example {scriptCtx : ScriptContext} {threshold : Nat}
    {fragments : List CoreFragment} {ty : MiniType}
    {env : SatEnv} {flags : ScriptFlags}
    (unsafeThreshold : ¬ ArithmeticScriptNatSafe threshold)
    (typed : HasType scriptCtx (.thresh threshold fragments) ty)
    (wellFormed : CoreFragment.WellFormed scriptCtx
      (.thresh threshold fragments))
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    satisfactionCandidates (.thresh threshold fragments) env = {} ∧
      (satisfactionCandidates
        (.thresh threshold fragments) env).SupportsGeneratedContract
        scriptCtx (.thresh threshold fragments) ty flags env.txCtx := by
  have invalid : ¬ candidateThresholdValid threshold fragments.length :=
    fun valid => unsafeThreshold valid.2.2
  constructor
  · exact satisfactionCandidates_thresh_invalid threshold fragments env invalid
  · exact supportsGeneratedContract_of_wellFormed_hasType version modeled
      sound encodings typed wellFormed

end LeanMiniscript.Miniscript
