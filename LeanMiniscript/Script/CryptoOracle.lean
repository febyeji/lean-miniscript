import LeanHash160
import LeanMiniscript.Bitcoin.Schnorr
import LeanMiniscript.Script.SignatureChecks

/-! Cryptographic callbacks and their abstract-model agreement contract. -/

namespace LeanMiniscript.Script

/-- Cryptographic operations needed by the executable Script evaluator.

    The model oracle below preserves the abstract functions used by `Eval`.
    Executable callers can instead use `pureLeanHashes`, supplying separate ECDSA and Schnorr
    signature verification at the application boundary. Legacy
    multisignature matching and byte-error precedence stay in the evaluator. -/
structure CryptoOracle where
  sha256 : StackElement → StackElement
  hash256 : StackElement → StackElement
  ripemd160 : StackElement → StackElement
  hash160 : StackElement → StackElement
  checkSig : StackElement → StackElement → ByteArray → Bool
  checkSchnorrSig : StackElement → StackElement → ByteArray → Bool

namespace CryptoOracle

/-- The oracle whose operations are definitionally the abstract cryptographic
    functions used by the relational big-step semantics. -/
def model : CryptoOracle where
  sha256 := LeanMiniscript.Script.sha256
  hash256 := LeanMiniscript.Script.hash256
  ripemd160 := LeanMiniscript.Script.ripemd160
  hash160 := LeanMiniscript.Script.hash160
  checkSig := LeanMiniscript.Script.checkSig
  checkSchnorrSig := LeanMiniscript.Script.checkSchnorrSig

/-- Executable pure-Lean hashes paired with caller-supplied signature checks.

    A production signature implementation can be supplied through an FFI
    without coupling the proof-facing evaluator to one native library. -/
def pureLeanHashes
    (verifySignature : StackElement → StackElement → ByteArray → Bool)
    (verifySchnorrSignature : StackElement → StackElement → ByteArray → Bool :=
      fun _ _ _ => false) :
    CryptoOracle where
  sha256 := LeanHash160.SHA256.hash
  hash256 := fun bytes =>
    LeanHash160.SHA256.hash (LeanHash160.SHA256.hash bytes)
  ripemd160 := LeanHash160.RIPEMD160.hash
  hash160 := LeanHash160.hash160
  checkSig := verifySignature
  checkSchnorrSig := verifySchnorrSignature

/-- Pure-Lean hashes and executable BIP340 verification. ECDSA remains
caller-supplied and defaults to rejection. No unconditional `RefinesModel`
claim is made for this concrete cryptographic implementation. -/
def pureLeanSchnorr
    (verifyECDSA : StackElement → StackElement → ByteArray → Bool :=
      fun _ _ _ => false) : CryptoOracle :=
  pureLeanHashes verifyECDSA Bitcoin.Schnorr.verify

/-- Pointwise agreement with the abstract cryptographic boundary of `Eval`. -/
def RefinesModel (oracle : CryptoOracle) : Prop :=
  (∀ bytes, oracle.sha256 bytes = LeanMiniscript.Script.sha256 bytes) ∧
  (∀ bytes, oracle.hash256 bytes = LeanMiniscript.Script.hash256 bytes) ∧
  (∀ bytes, oracle.ripemd160 bytes = LeanMiniscript.Script.ripemd160 bytes) ∧
  (∀ bytes, oracle.hash160 bytes = LeanMiniscript.Script.hash160 bytes) ∧
  (∀ sig pubkey sigHash,
    oracle.checkSig sig pubkey sigHash =
      LeanMiniscript.Script.checkSig sig pubkey sigHash) ∧
  (∀ sig pubkey sigHash,
    oracle.checkSchnorrSig sig pubkey sigHash =
      LeanMiniscript.Script.checkSchnorrSig sig pubkey sigHash)

theorem model_refines : model.RefinesModel := by
  simp [RefinesModel, model]

end CryptoOracle

end LeanMiniscript.Script
