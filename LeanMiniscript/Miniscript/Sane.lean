import LeanMiniscript.Miniscript.Checked
import LeanMiniscript.Miniscript.Soundness
import LeanMiniscript.Miniscript.MalleabilityInference
import LeanMiniscript.Properties.ResourceBounds

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Properties
open LeanMiniscript.Script

/-!
# Integrated Miniscript sanity boundary

`SaneFragment` combines the structural, typing, malleability, key-uniqueness,
and context-specific resource checks used by Bitcoin Core's static `IsSane`
boundary. Satisfiability with a particular signing environment remains a
separate operation: the malleability `m` and `s` properties are vacuous when a
fragment has no satisfaction.
-/

/-- Failure returned while constructing a statically sane Miniscript. -/
inductive SaneError where
  | notWellFormed
  | notTyped
  | notTopLevel
  | duplicateKeys
  | malleabilityUnavailable
  | malleable
  | signatureNotRequired
  | resourceLimitsExceeded
  deriving Repr, DecidableEq, BEq

/-- A top-level Miniscript carrying all evidence required by the static sane
    compilation boundary. -/
structure SaneFragment (ctx : ScriptContext) where
  checked : CheckedFragment ctx
  malleability : MalleabilityModifiers
  topLevel : checked.ty.base = .B
  hasMalleability : HasMalleability ctx checked.fragment malleability
  noDuplicateKeys : checked.fragment.NoDuplicateKeys
  nonMalleable : malleability.nonMalleable = true
  needsSignature : malleability.s = true
  withinResourceLimits : WithinResourceLimits ctx checked.fragment

namespace SaneFragment

/-- Static sanity includes the existing top-level validity boundary. -/
theorem validMiniscript {ctx : ScriptContext} (sane : SaneFragment ctx) :
    ValidMiniscript ctx sane.checked.fragment := by
  refine ⟨sane.checked.ty.mods, sane.checked.wellFormed, ?_⟩
  cases typeEq : sane.checked.ty with
  | mk base mods =>
      have top := sane.topLevel
      simp only [typeEq] at top
      subst base
      simpa [typeEq] using sane.checked.hasType

/-- Compile a fragment only after the integrated static sanity check. -/
def compile {ctx : ScriptContext} (sane : SaneFragment ctx) : Script :=
  compileChecked sane.checked

end SaneFragment

/-- Check every static condition required by the sane compilation boundary.
    The ordering preserves specific duplicate-key and top-level diagnostics
    before running recursive malleability inference. -/
def checkSane (ctx : ScriptContext) (fragment : CoreFragment) :
    Except SaneError (SaneFragment ctx) :=
  if wellFormed : fragment.WellFormed ctx then
    match inferTyped ctx fragment with
    | none => .error .notTyped
    | some typed =>
        let checked : CheckedFragment ctx := {
          fragment
          ty := typed.val
          wellFormed
          hasType := typed.property
        }
        if topLevel : checked.ty.base = .B then
          if unique : fragment.NoDuplicateKeys then
            match inferMalleabilityTyped ctx fragment with
            | none => .error .malleabilityUnavailable
            | some analyzed =>
                if nonMalleable : analyzed.val.nonMalleable = true then
                  if needsSignature : analyzed.val.s = true then
                    if resources : WithinResourceLimits ctx fragment then
                      .ok {
                        checked
                        malleability := analyzed.val
                        topLevel
                        hasMalleability := analyzed.property.1
                        noDuplicateKeys := unique
                        nonMalleable
                        needsSignature
                        withinResourceLimits := resources
                      }
                    else .error .resourceLimitsExceeded
                  else .error .signatureNotRequired
                else .error .malleable
          else .error .duplicateKeys
        else .error .notTopLevel
  else .error .notWellFormed

/-- Check a surface fragment through its single core desugaring boundary. -/
def checkSaneSurface (ctx : ScriptContext) (fragment : SurfaceFragment) :
    Except SaneError (SaneFragment ctx) :=
  checkSane ctx (desugar fragment)

end LeanMiniscript.Miniscript
