import LeanMiniscript.Miniscript.Validation

namespace LeanMiniscript.Miniscript

/-!
# Executable validation

Decision procedures are separate from the declarative `WellFormed` predicates
so theorem-only consumers do not import the executable validation layer.
-/

namespace TimelockUsage

instance (usage : TimelockUsage) : Decidable usage.compatible := by
  unfold compatible
  infer_instance

end TimelockUsage

namespace CoreFragment

/-- Executable decision procedure for public-key list validity. -/
def allKeysValidDecidable (ctx : ScriptContext) (keys : List PubKey) :
    Decidable (allKeysValid ctx keys) := by
  cases keys with
  | nil =>
      simp only [allKeysValid]
      infer_instance
  | cons key keys =>
      letI := allKeysValidDecidable ctx keys
      simp only [allKeysValid, validResolvedPubKey]
      cases ctx <;> infer_instance

mutual
  /-- Executable decision procedure for fragment-list well-formedness. -/
  def allWellFormedDecidable (ctx : ScriptContext) (fragments : List CoreFragment) :
      Decidable (allWellFormed ctx fragments) := by
    cases fragments with
    | nil =>
        simp only [allWellFormed]
        infer_instance
    | cons fragment fragments =>
        letI := wellFormedDecidable ctx fragment
        letI := allWellFormedDecidable ctx fragments
        simp only [allWellFormed]
        infer_instance

  /-- Executable decision procedure for core-fragment well-formedness. -/
  def wellFormedDecidable (ctx : ScriptContext) (fragment : CoreFragment) :
      Decidable (WellFormed ctx fragment) := by
    cases fragment with
    | zero | one | pk_k | pk_h | older | after | sha256 | hash256 |
        ripemd160 | hash160 =>
        simp only [WellFormed, validResolvedPubKey, validTimelockArg,
          validHash256, validHash160]
        cases ctx <;> infer_instance
    | and_v x y | and_b x y | or_b x y | or_c x y | or_d x y | or_i x y =>
        letI := wellFormedDecidable ctx x
        letI := wellFormedDecidable ctx y
        simp only [WellFormed, andTimelocksCompatible]
        infer_instance
    | andor x y z =>
        letI := wellFormedDecidable ctx x
        letI := wellFormedDecidable ctx y
        letI := wellFormedDecidable ctx z
        simp only [WellFormed, andorTimelocksCompatible]
        infer_instance
    | a x | s x | c x | d x | v x | j x | n x =>
        simpa only [WellFormed] using wellFormedDecidable ctx x
    | thresh _ fragments =>
        letI := allWellFormedDecidable ctx fragments
        simp only [WellFormed, validThreshold]
        infer_instance
    | multi _ keys | multi_a _ keys =>
        letI := allKeysValidDecidable ctx keys
        simp only [WellFormed, ScriptContext.permitsLegacyMulti,
          ScriptContext.permitsCheckSigAddMulti, validThreshold,
          validLegacyMultiKeyCount]
        cases ctx <;> infer_instance
end

instance (ctx : ScriptContext) (fragment : CoreFragment) :
    Decidable (WellFormed ctx fragment) :=
  wellFormedDecidable ctx fragment

end CoreFragment

namespace SurfaceFragment

instance (ctx : ScriptContext) (fragment : SurfaceFragment) :
    Decidable (WellFormed ctx fragment) :=
  CoreFragment.wellFormedDecidable ctx (desugar fragment)

end SurfaceFragment

end LeanMiniscript.Miniscript
