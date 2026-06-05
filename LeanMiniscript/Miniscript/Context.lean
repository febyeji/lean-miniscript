import LeanMiniscript.Miniscript.KeyExpr
import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

/-- Script contexts covered by BIP 379. -/
inductive ScriptContext where
  | p2wsh
  | tapscript
  deriving Repr, DecidableEq, BEq

/-- Resolved public keys allowed by the target script context.

    P2WSH keys must resolve to compressed public keys. Tapscript keys resolve to
    x-only public keys; compressed keys may be converted by the descriptor layer,
    so both 32-byte x-only and 33-byte compressed representations are accepted
    at this boundary. -/
def validResolvedPubKey (ctx : ScriptContext) (key : PubKey) : Prop :=
  match ctx with
  | .p2wsh => key.size = 33
  | .tapscript => key.size = 32 ∨ key.size = 33

/-- Context compatibility for unresolved descriptor key expressions. -/
def KeyMaterial.CompatibleWith : KeyMaterial → ScriptContext → Prop
  | .publicKey bytes, .p2wsh => bytes.size = 33
  | .publicKey bytes, .tapscript => bytes.size = 33
  | .xOnlyPublicKey _, .p2wsh => False
  | .xOnlyPublicKey bytes, .tapscript => bytes.size = 32
  | .privateKey bytes, .p2wsh => 0 < bytes.size
  | .privateKey bytes, .tapscript => 0 < bytes.size
  | .xpub bytes, _ => 0 < bytes.size
  | .xprv bytes, _ => 0 < bytes.size

/-- A key expression is usable in a given script context. -/
def KeyExpression.CompatibleWith (key : KeyExpression) (ctx : ScriptContext) : Prop :=
  key.WellFormed ∧ key.material.CompatibleWith ctx

/-- Legacy `multi` is P2WSH-only in BIP 379. -/
def ScriptContext.permitsLegacyMulti : ScriptContext → Prop
  | .p2wsh => True
  | .tapscript => False

/-- `multi_a` is Tapscript-only in BIP 379. -/
def ScriptContext.permitsCheckSigAddMulti : ScriptContext → Prop
  | .p2wsh => False
  | .tapscript => True

end LeanMiniscript.Miniscript
