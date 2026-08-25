import LeanMiniscript.Miniscript.KeyExpr
import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Script contexts covered by BIP 379. -/
inductive ScriptContext where
  | p2wsh
  | tapscript
  deriving Repr, DecidableEq, BEq

/-- The `u` modifier contributed by `d:X` in the BIP 379 correctness table.
    P2WSH policy applies MINIMALIF too, but the table grants this type property
    only to Tapscript, where MINIMALIF is consensus-enforced. -/
def ScriptContext.dWrapperUnit : ScriptContext → Bool
  | .p2wsh => false
  | .tapscript => true

/-- Whether bytes have the serialized shape of a compressed secp256k1 public
    key. Curve-point validation remains the responsibility of the key resolver. -/
def validCompressedPubKeyBytes (bytes : ByteArray) : Prop :=
  bytes.size = 33 ∧
    (bytes.get! 0 = 0x02 ∨ bytes.get! 0 = 0x03)

instance instDecidableValidCompressedPubKeyBytes (bytes : ByteArray) :
    Decidable (validCompressedPubKeyBytes bytes) := by
  unfold validCompressedPubKeyBytes
  infer_instance

/-- Resolved public keys allowed by the target script context.

    P2WSH keys resolve to compressed public keys. Tapscript keys must already be
    normalized to x-only public keys before entering the core AST; descriptor
    layers may accept compressed key expressions, but must convert them first. -/
def validResolvedPubKey (ctx : ScriptContext) (key : PubKey) : Prop :=
  match ctx with
  | .p2wsh => validCompressedPubKeyBytes key.bytes
  | .tapscript => key.size = 32

/-- Context compatibility for unresolved descriptor key expressions. -/
def KeyMaterial.CompatibleWith : KeyMaterial → ScriptContext → Prop
  | .publicKey bytes, .p2wsh => validCompressedPubKeyBytes bytes
  | .publicKey bytes, .tapscript => validCompressedPubKeyBytes bytes
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

/-- Whether an opcode belongs to the generated Script subset for a context.

    The compiler's modeled opcode universe is shared between P2WSH and
    Tapscript except for the two multisig encodings: legacy
    `OP_CHECKMULTISIG` is P2WSH-only, while `OP_CHECKSIGADD` is
    Tapscript-only. -/
def OpcodeAllowed : ScriptContext → Opcode → Prop
  | .tapscript, .OP_CHECKMULTISIG => False
  | .p2wsh, .OP_CHECKSIGADD => False
  | _, _ => True

instance instDecidableOpcodeAllowed
    (ctx : ScriptContext) (opcode : Opcode) :
    Decidable (OpcodeAllowed ctx opcode) := by
  cases ctx <;> cases opcode <;> simp only [OpcodeAllowed] <;> infer_instance

/-- Context safety for one generated Script element. Data and numeric pushes
    are valid in both modeled contexts; opcode restrictions are delegated to
    `OpcodeAllowed`. -/
def ScriptElementAllowed (ctx : ScriptContext) : ScriptElement → Prop
  | .op opcode => OpcodeAllowed ctx opcode
  | .pushData _ => True
  | .pushNum _ => True

instance instDecidableScriptElementAllowed
    (ctx : ScriptContext) (element : ScriptElement) :
    Decidable (ScriptElementAllowed ctx element) := by
  cases element <;> simp only [ScriptElementAllowed] <;> infer_instance

/-- Every element in a generated Script is allowed by the selected context. -/
def ScriptAllowed (ctx : ScriptContext) : Script → Prop
  | [] => True
  | element :: script =>
      ScriptElementAllowed ctx element ∧ ScriptAllowed ctx script

instance instDecidableScriptAllowed (ctx : ScriptContext) :
    (script : Script) → Decidable (ScriptAllowed ctx script)
  | [] => isTrue trivial
  | element :: script =>
      match instDecidableScriptElementAllowed ctx element,
          instDecidableScriptAllowed ctx script with
      | isTrue headAllowed, isTrue tailAllowed =>
          isTrue ⟨headAllowed, tailAllowed⟩
      | isFalse headForbidden, _ =>
          isFalse (fun allowed => headForbidden allowed.1)
      | _, isFalse tailForbidden =>
          isFalse (fun allowed => tailForbidden allowed.2)

end LeanMiniscript.Miniscript
