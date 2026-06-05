import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Miniscript

/-- One step in a BIP32 derivation path. -/
inductive DerivationStep where
  | normal : Nat → DerivationStep
  | hardened : Nat → DerivationStep
  deriving Repr, DecidableEq, BEq

/-- Optional final wildcard derivation step in a descriptor key expression. -/
inductive ChildWildcard where
  | none
  | normal
  | hardened
  deriving Repr, DecidableEq, BEq

/-- Optional key origin information from BIP 380. -/
structure KeyOrigin where
  fingerprint : ByteArray
  path : List DerivationStep := []
  deriving Repr

/-- The key material accepted by descriptor key expressions.

    Base58/WIF/xpub parsing is intentionally outside this AST layer; the bytes
    here stand for already parsed key material. -/
inductive KeyMaterial where
  | publicKey : ByteArray → KeyMaterial
  | privateKey : ByteArray → KeyMaterial
  | xpub : ByteArray → KeyMaterial
  | xprv : ByteArray → KeyMaterial
  | xOnlyPublicKey : ByteArray → KeyMaterial
  deriving Repr

/-- BIP 380 key-expression syntax, before resolving it to concrete public keys. -/
structure KeyExpression where
  origin : Option KeyOrigin := none
  material : KeyMaterial
  derivation : List DerivationStep := []
  wildcard : ChildWildcard := .none
  deriving Repr

/-- Key-origin fingerprints are 4 bytes. -/
def KeyOrigin.WellFormed (origin : KeyOrigin) : Prop :=
  origin.fingerprint.size = 4

/-- A coarse AST-level check for parsed key material.

    Prefix/base58 checksum validation belongs to the parser. This predicate
    captures only the byte-length distinctions needed by the Miniscript layer. -/
def KeyMaterial.WellFormed : KeyMaterial → Prop
  | .publicKey bytes => bytes.size = 33 ∨ bytes.size = 65
  | .privateKey bytes => 0 < bytes.size
  | .xpub bytes => 0 < bytes.size
  | .xprv bytes => 0 < bytes.size
  | .xOnlyPublicKey bytes => bytes.size = 32

/-- Only extended keys can carry post-key derivation or child wildcards. -/
def KeyMaterial.allowsDerivation : KeyMaterial → Prop
  | .xpub _ => True
  | .xprv _ => True
  | _ => False

/-- Well-formedness for descriptor key expressions independent of script
    context. P2WSH/Tapscript key restrictions are modeled in `Context.lean`. -/
def KeyExpression.WellFormed (key : KeyExpression) : Prop :=
  (match key.origin with
    | none => True
    | some origin => origin.WellFormed) ∧
  key.material.WellFormed ∧
  ((key.derivation = [] ∧ key.wildcard = .none) ∨ key.material.allowsDerivation)

end LeanMiniscript.Miniscript
