import LeanMiniscript.Script.Syntax
import LeanMiniscript.Script.State
import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Push every key in order. -/
def compileKeyPushes : List PubKey → Script
  | [] => []
  | key :: keys => .pushData key :: compileKeyPushes keys

/-- Compile every key after the first with CHECKSIGADD. This helper is named
    explicitly so structural compiler proofs can refer to it. -/
def compileCheckSigAddTail : List PubKey → Script
  | [] => []
  | key :: keys =>
      [.pushData key, .op .OP_CHECKSIGADD] ++ compileCheckSigAddTail keys

/-- Compile the first key with CHECKSIG and every following key with
    CHECKSIGADD. -/
def compileCheckSigAdd : List PubKey → Script
  | [] => [.pushNum 0]
  | key :: keys =>
      [.pushData key, .op .OP_CHECKSIG] ++ compileCheckSigAddTail keys

/- Compile a core Miniscript AST fragment to Bitcoin Script.
   Each core constructor has a fixed compilation scheme defined in BIP 379. -/
mutual
/-- Compile a core Miniscript AST fragment with an explicit public-key HASH160
    resolver. Formal semantics can supply the opaque `Script.hash160`; an
    executable compiler or conformance harness can supply a concrete
    implementation without changing the fragment AST. -/
def compileWithKeyHash (keyHash : PubKey → Hash160) : CoreFragment → Script
  -- Leaves
  | .zero => [.pushNum 0]
  | .one => [.pushNum 1]
  | .pk_k key => [.pushData key]
  | .pk_h key =>
      [.op .OP_DUP, .op .OP_HASH160, .pushData (keyHash key), .op .OP_EQUALVERIFY]
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
  | .and_v x y => compileWithKeyHash keyHash x ++ compileWithKeyHash keyHash y
  | .and_b x y =>
      compileWithKeyHash keyHash x ++ compileWithKeyHash keyHash y ++ [.op .OP_BOOLAND]
  | .or_b x y =>
      compileWithKeyHash keyHash x ++ compileWithKeyHash keyHash y ++ [.op .OP_BOOLOR]
  | .or_c x y =>
      compileWithKeyHash keyHash x ++ [.op .OP_NOTIF] ++
        compileWithKeyHash keyHash y ++ [.op .OP_ENDIF]
  | .or_d x y =>
      compileWithKeyHash keyHash x ++ [.op .OP_IFDUP, .op .OP_NOTIF] ++
        compileWithKeyHash keyHash y ++ [.op .OP_ENDIF]
  | .or_i x y =>
      [.op .OP_IF] ++ compileWithKeyHash keyHash x ++ [.op .OP_ELSE] ++
        compileWithKeyHash keyHash y ++ [.op .OP_ENDIF]
  | .andor x y z =>
      compileWithKeyHash keyHash x ++ [.op .OP_NOTIF] ++
        compileWithKeyHash keyHash z ++ [.op .OP_ELSE] ++
        compileWithKeyHash keyHash y ++ [.op .OP_ENDIF]
  -- Wrappers
  | .a x =>
      [.op .OP_TOALTSTACK] ++ compileWithKeyHash keyHash x ++ [.op .OP_FROMALTSTACK]
  | .s x => [.op .OP_SWAP] ++ compileWithKeyHash keyHash x
  | .c x => compileWithKeyHash keyHash x ++ [.op .OP_CHECKSIG]
  | .d x =>
      [.op .OP_DUP, .op .OP_IF] ++ compileWithKeyHash keyHash x ++ [.op .OP_ENDIF]
  | .v x => compileWithKeyHash keyHash x ++ [.op .OP_VERIFY]
      -- Note: in practice, OP_CHECKSIG→OP_CHECKSIGVERIFY optimization exists
      -- but we model the general case
  | .j x =>
      [.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++
        compileWithKeyHash keyHash x ++ [.op .OP_ENDIF]
  | .n x => compileWithKeyHash keyHash x ++ [.op .OP_0NOTEQUAL]
  -- Threshold and multisig
  | .thresh k fragments =>
      compileThreshWithKeyHash keyHash fragments ++ [.pushNum k, .op .OP_EQUAL]
  | .multi k keys =>
      [.pushNum k] ++ compileKeyPushes keys ++
        [.pushNum keys.length, .op .OP_CHECKMULTISIG]
  | .multi_a k keys => compileCheckSigAdd keys ++ [.pushNum k, .op .OP_NUMEQUAL]

/-- Compile `thresh` children as `[X1] [X2] OP_ADD ... [Xn] OP_ADD`. -/
def compileThreshWithKeyHash
    (keyHash : PubKey → Hash160) : List CoreFragment → Script
  | [] => []
  | fragment :: fragments =>
      compileWithKeyHash keyHash fragment ++
        compileThreshTailWithKeyHash keyHash fragments

/-- Compile every threshold child after the first with a following `OP_ADD`. -/
def compileThreshTailWithKeyHash
    (keyHash : PubKey → Hash160) : List CoreFragment → Script
  | [] => []
  | fragment :: fragments =>
      compileWithKeyHash keyHash fragment ++ [.op .OP_ADD] ++
        compileThreshTailWithKeyHash keyHash fragments
end

/-- Formal compiler instantiated with the model's abstract HASH160 operation. -/
def compile : CoreFragment → Script :=
  compileWithKeyHash hash160

/-- Compile threshold children with the model's abstract HASH160 operation. -/
def compileThresh : List CoreFragment → Script :=
  compileThreshWithKeyHash hash160

/-- Compile threshold tails with the model's abstract HASH160 operation. -/
def compileThreshTail : List CoreFragment → Script :=
  compileThreshTailWithKeyHash hash160

/-- Compile surface Miniscript with an explicit public-key HASH160 resolver. -/
def compileSurfaceWithKeyHash
    (keyHash : PubKey → Hash160) (fragment : SurfaceFragment) : Script :=
  compileWithKeyHash keyHash (desugar fragment)

/-- Compile surface Miniscript by first lowering syntactic sugar to core. -/
def compileSurface (fragment : SurfaceFragment) : Script :=
  compileSurfaceWithKeyHash hash160 fragment

/-- Compile a Policy to a core Miniscript AST fragment.
    Policy lowering is a later phase: it should target `CoreFragment` after the
    AST, typing, and compilation layers are fixed. -/
def compilePolicy : Policy → CoreFragment
  -- TODO(policy): This is significantly more complex than fragment compilation.
  -- It involves an optimization search over possible Miniscript encodings.
  -- For now, a naive (non-optimizing) translation:
  | _ => .pk_k ByteArray.empty  -- Placeholder

-- Raw compiler injectivity is intentionally not a target: compilation erases
-- AST grouping, so distinct fragments can produce the same Script.
-- TODO(theorem): Prove that compilation preserves execution semantics.

end LeanMiniscript.Miniscript
