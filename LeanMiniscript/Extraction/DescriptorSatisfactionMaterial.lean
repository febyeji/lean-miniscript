import LeanMiniscript.Miniscript.SatisfactionEnvironment
import LeanMiniscript.Script.CryptoOracle

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Miniscript

/-- Supplied signatures and hashlock material. The transaction context is
derived separately from the selected descriptor leaf and transaction. -/
structure DescriptorSatisfactionMaterial where
  signatureFor : PubKey → Option StackElement
  preimageFor : HashLock → Option StackElement
  nonPreimageFor : HashLock → StackElement

def DescriptorSatisfactionMaterial.toEnv (material : DescriptorSatisfactionMaterial)
    (context : TxContext) : SatEnv :=
  { signatureFor := material.signatureFor
    preimageFor := material.preimageFor
    nonPreimageFor := material.nonPreimageFor
    txCtx := context }

namespace DescriptorSatisfactionMaterial

/-- Hash a preimage with the same callback used during script execution. -/
def hashDigest (oracle : CryptoOracle) : HashLock → StackElement → StackElement
  | .sha256 _, bytes => oracle.sha256 bytes
  | .hash256 _, bytes => oracle.hash256 bytes
  | .ripemd160 _, bytes => oracle.ripemd160 bytes
  | .hash160 _, bytes => oracle.hash160 bytes

/-- Filter supplied satisfactions before candidate selection. Signatures must
pass encoding and transaction-specific verification; preimages must have the
required length and digest. Rejected material becomes unavailable. The caller's
nonpreimage callback still supplies hashlock dissatisfaction material. -/
def validated (material : DescriptorSatisfactionMaterial) (oracle : CryptoOracle)
    (flags : ScriptFlags) (context : TxContext) : DescriptorSatisfactionMaterial :=
  { material with
    signatureFor := fun key => (material.signatureFor key).filter fun signature =>
      match checkSigEncodingFor flags context.sigVersion signature key.bytes with
      | .error _ => false
      | .ok () => verifySigFor oracle.checkSig oracle.checkSchnorrSig context signature key.bytes
    preimageFor := fun lock => (material.preimageFor lock).filter fun preimage =>
      preimage.size == 32 && (hashDigest oracle lock preimage).data == lock.expected.data }

end DescriptorSatisfactionMaterial

end LeanMiniscript.Extraction
