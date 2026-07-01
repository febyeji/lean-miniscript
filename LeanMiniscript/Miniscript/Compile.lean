import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State
import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/- Compile a core Miniscript AST fragment to Bitcoin Script.
   Each core constructor has a fixed compilation scheme defined in BIP 379. -/
mutual
/-- Compile a core Miniscript AST fragment to Bitcoin Script. -/
def compile : CoreFragment → Script
  -- Leaves
  | .zero => [.pushNum 0]
  | .one => [.pushNum 1]
  | .pk_k key => [.pushData key]
  | .pk_h key =>
      [.op .OP_DUP, .op .OP_HASH160, .pushData (hash160 key), .op .OP_EQUALVERIFY]
  | .older n => [.pushNum n, .op .OP_CHECKSEQUENCEVERIFY]
  | .after n => [.pushNum n, .op .OP_CHECKLOCKTIMEVERIFY]
  | .sha256 h =>
      [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
       .op .OP_SHA256, .pushData h, .op .OP_EQUAL]
  | .hash256 h =>
      [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
       .op .OP_HASH256, .pushData h, .op .OP_EQUAL]
  | .ripemd160 h =>
      [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
       .op .OP_RIPEMD160, .pushData h, .op .OP_EQUAL]
  | .hash160 h =>
      [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
       .op .OP_HASH160, .pushData h, .op .OP_EQUAL]
  -- Connectives
  | .and_v x y => compile x ++ compile y
  | .and_b x y => compile x ++ compile y ++ [.op .OP_BOOLAND]
  | .or_b x y => compile x ++ compile y ++ [.op .OP_BOOLOR]
  | .or_c x y =>
      compile x ++ [.op .OP_NOTIF] ++ compile y ++ [.op .OP_ENDIF]
  | .or_d x y =>
      compile x ++ [.op .OP_IFDUP, .op .OP_NOTIF] ++ compile y ++ [.op .OP_ENDIF]
  | .or_i x y =>
      [.op .OP_IF] ++ compile x ++ [.op .OP_ELSE] ++ compile y ++ [.op .OP_ENDIF]
  | .andor x y z =>
      compile x ++ [.op .OP_NOTIF] ++ compile z ++ [.op .OP_ELSE] ++
      compile y ++ [.op .OP_ENDIF]
  -- Wrappers
  | .a x => [.op .OP_TOALTSTACK] ++ compile x ++ [.op .OP_FROMALTSTACK]
  | .s x => [.op .OP_SWAP] ++ compile x
  | .c x => compile x ++ [.op .OP_CHECKSIG]
  | .d x => [.op .OP_DUP, .op .OP_IF] ++ compile x ++ [.op .OP_ENDIF]
  | .v x => compile x ++ [.op .OP_VERIFY]
      -- Note: in practice, OP_CHECKSIG→OP_CHECKSIGVERIFY optimization exists
      -- but we model the general case
  | .j x =>
      [.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++ compile x ++ [.op .OP_ENDIF]
  | .n x => compile x ++ [.op .OP_0NOTEQUAL]
  -- Threshold
  | .thresh k fragments => compileThresh fragments ++ [.pushNum k, .op .OP_EQUAL]
  | .multi _ _ => []   -- TODO
  | .multi_a _ _ => [] -- TODO

/-- Compile `thresh` children as `[X1] [X2] OP_ADD ... [Xn] OP_ADD`. -/
def compileThresh : List CoreFragment → Script
  | [] => []
  | fragment :: fragments => compile fragment ++ compileThreshTail fragments

/-- Compile every threshold child after the first with a following `OP_ADD`. -/
def compileThreshTail : List CoreFragment → Script
  | [] => []
  | fragment :: fragments => compile fragment ++ [.op .OP_ADD] ++ compileThreshTail fragments
end

/-- Compile surface Miniscript by first lowering syntactic sugar to core. -/
def compileSurface (fragment : SurfaceFragment) : Script :=
  compile (desugar fragment)

/-- Compile a Policy to a core Miniscript AST fragment.
    Policy lowering is a later phase: it should target `CoreFragment` after the
    AST, typing, and compilation layers are fixed. -/
def compilePolicy : Policy → CoreFragment
  -- TODO: This is significantly more complex than fragment compilation.
  -- It involves an optimization search over possible Miniscript encodings.
  -- For now, a naive (non-optimizing) translation:
  | _ => .pk_k ByteArray.empty  -- Placeholder

-- TODO: Prove that compile is injective (different fragments produce different scripts)
-- TODO: Prove compilation preserves semantics (Theorem 4 in briefing)

end LeanMiniscript.Miniscript
