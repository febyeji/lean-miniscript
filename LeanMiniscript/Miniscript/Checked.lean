import LeanMiniscript.Miniscript.ValidationDecidable
import LeanMiniscript.Miniscript.TypeInference
import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A core fragment accompanied by the context and typing evidence required at
    the public compilation boundary. The raw AST remains available for
    structural recursion and theorem statements. -/
structure CheckedFragment (ctx : ScriptContext) where
  fragment : CoreFragment
  ty : MiniType
  wellFormed : fragment.WellFormed ctx
  hasType : HasType ctx fragment ty

namespace CheckedFragment

/-- Check a raw core fragment at runtime and retain the resulting evidence. -/
def ofRaw? (ctx : ScriptContext) (fragment : CoreFragment) :
    Option (CheckedFragment ctx) :=
  if wellFormed : fragment.WellFormed ctx then
    match inferTyped ctx fragment with
    | some typed =>
        some {
          fragment
          ty := typed.val
          wellFormed
          hasType := typed.property
        }
    | none => none
  else none

end CheckedFragment

/-- Compile a checked core fragment with an explicit key-HASH160 resolver. -/
def compileCheckedWithKeyHash {ctx : ScriptContext}
    (keyHash : PubKey → Hash160) (checked : CheckedFragment ctx) : Script :=
  compileWithKeyHash keyHash checked.fragment

/-- Compile a checked core fragment with the formal HASH160 boundary. -/
def compileChecked {ctx : ScriptContext} (checked : CheckedFragment ctx) : Script :=
  compile checked.fragment

/-- A surface fragment whose desugared core is well-formed and typed. -/
structure CheckedSurfaceFragment (ctx : ScriptContext) where
  fragment : SurfaceFragment
  ty : MiniType
  wellFormed : fragment.WellFormed ctx
  hasType : HasType ctx (desugar fragment) ty

namespace CheckedSurfaceFragment

/-- Check a raw surface fragment after desugaring and retain the evidence. -/
def ofRaw? (ctx : ScriptContext) (fragment : SurfaceFragment) :
    Option (CheckedSurfaceFragment ctx) :=
  if wellFormed : fragment.WellFormed ctx then
    match inferTyped ctx (desugar fragment) with
    | some typed =>
        some {
          fragment
          ty := typed.val
          wellFormed
          hasType := typed.property
        }
    | none => none
  else none

end CheckedSurfaceFragment

/-- Compile a checked surface fragment with an explicit key-HASH160 resolver. -/
def compileCheckedSurfaceWithKeyHash {ctx : ScriptContext}
    (keyHash : PubKey → Hash160) (checked : CheckedSurfaceFragment ctx) : Script :=
  compileSurfaceWithKeyHash keyHash checked.fragment

/-- Compile a checked surface fragment with the formal HASH160 boundary. -/
def compileCheckedSurface {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) : Script :=
  compileSurface checked.fragment

end LeanMiniscript.Miniscript
