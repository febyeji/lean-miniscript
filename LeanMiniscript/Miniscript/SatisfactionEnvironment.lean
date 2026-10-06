import LeanMiniscript.Miniscript.Syntax
import LeanMiniscript.Script.SignatureChecks

/-! Hashlock targets and the signatures, preimages and transaction data supplied to satisfaction generation. -/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A typed hashlock target for preimage lookup. -/
inductive HashLock where
  | sha256 : Hash256 → HashLock
  | hash256 : Hash256 → HashLock
  | ripemd160 : Hash160 → HashLock
  | hash160 : Hash160 → HashLock

namespace HashLock

/-- Apply the hash operation selected by a typed hashlock. Hash functions
    remain opaque at the formal boundary. -/
def digest : HashLock → StackElement → StackElement
  | .sha256 _, preimage => LeanMiniscript.Script.sha256 preimage
  | .hash256 _, preimage => LeanMiniscript.Script.hash256 preimage
  | .ripemd160 _, preimage => LeanMiniscript.Script.ripemd160 preimage
  | .hash160 _, preimage => LeanMiniscript.Script.hash160 preimage

/-- The digest committed to by a typed hashlock. -/
def expected : HashLock → StackElement
  | .sha256 hash | .hash256 hash => hash.bytes
  | .ripemd160 hash | .hash160 hash => hash.bytes

/-- The core fragment represented by a typed hashlock. -/
def fragment : HashLock → CoreFragment
  | .sha256 hash => .sha256 hash
  | .hash256 hash => .hash256 hash
  | .ripemd160 hash => .ripemd160 hash
  | .hash160 hash => .hash160 hash

/-- The complete BIP 379 preimage relation, including the mandatory 32-byte
    input length enforced by the compiled `SIZE 32 EQUALVERIFY` prefix. -/
def Matches (lock : HashLock) (preimage : StackElement) : Prop :=
  preimage.size = 32 ∧ lock.digest preimage = lock.expected

/-- A 32-byte value which executes a hashlock to false rather than aborting. -/
def Mismatches (lock : HashLock) (nonPreimage : StackElement) : Prop :=
  nonPreimage.size = 32 ∧ lock.digest nonPreimage ≠ lock.expected

end HashLock

/-- An environment provides the "real-world" data needed for satisfaction:
    concrete signatures, preimages, and the transaction context. -/
structure SatEnv where
  /-- Return the exact stack element to use as a signature, when available. -/
  signatureFor : PubKey → Option StackElement
  /-- Return the exact preimage stack element for a typed hashlock. -/
  preimageFor : HashLock → Option StackElement
  /-- Return a 32-byte nonpreimage used for the hashlock's unconditional
      semantic dissatisfaction. The soundness predicate records its relation
      to each target. -/
  nonPreimageFor : HashLock → StackElement
  /-- Transaction data used by signature and timelock checks. -/
  txCtx : TxContext

namespace SatEnv

/-- Every piece of material returned by an environment satisfies the abstract
    cryptographic boundary used by `Eval`. -/
def Sound (env : SatEnv) : Prop :=
  (∀ key signature,
      env.signatureFor key = some signature →
      verifySigFor checkSig checkSchnorrSig env.txCtx signature key.bytes = true) ∧
  (∀ key : PubKey,
      verifySigFor checkSig checkSchnorrSig env.txCtx falseElement key.bytes = false) ∧
  (∀ lock preimage,
      env.preimageFor lock = some preimage →
      lock.Matches preimage) ∧
  (∀ lock : HashLock, lock.Mismatches (env.nonPreimageFor lock))

/-- A returned signature verifies under the environment transaction. -/
theorem Sound.signatureValid {env : SatEnv} (sound : env.Sound)
    {key : PubKey} {signature : StackElement}
    (selected : env.signatureFor key = some signature) :
    verifySigFor checkSig checkSchnorrSig env.txCtx signature key.bytes = true :=
  sound.1 key signature selected

/-- The canonical empty signature is rejected for every key. -/
theorem Sound.emptySignatureInvalid {env : SatEnv} (sound : env.Sound)
    (key : PubKey) :
    verifySigFor checkSig checkSchnorrSig env.txCtx falseElement key.bytes = false :=
  sound.2.1 key

/-- Every returned hash preimage has the exact size and digest required by its
    target. -/
theorem Sound.preimageMatches {env : SatEnv} (sound : env.Sound)
    {lock : HashLock} {preimage : StackElement}
    (selected : env.preimageFor lock = some preimage) :
    lock.Matches preimage :=
  sound.2.2.1 lock preimage selected

/-- Every hash dissatisfaction supplied by the environment is a 32-byte
    nonpreimage. -/
theorem Sound.nonPreimageMismatches {env : SatEnv} (sound : env.Sound)
    (lock : HashLock) :
    lock.Mismatches (env.nonPreimageFor lock) :=
  sound.2.2.2 lock

/-- Supplied signatures and their keys pass the version-specific byte checks selected by
    the execution flags. Cryptographic soundness alone does not imply this. -/
def EncodingSound (env : SatEnv) (flags : ScriptFlags) : Prop :=
  ∀ key signature,
    env.signatureFor key = some signature →
    checkSigEncodingFor flags env.txCtx.sigVersion signature key.bytes = .ok ()

end SatEnv

end LeanMiniscript.Miniscript
