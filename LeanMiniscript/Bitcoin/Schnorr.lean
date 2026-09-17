import LeanMiniscript.Bitcoin.Secp256k1
import LeanMiniscript.Bitcoin.TaggedHash

namespace LeanMiniscript.Bitcoin.Schnorr
open Secp256k1

/-- Executable BIP340 verification, accepting arbitrary-length messages.
The Script boundary passes a 32-byte transaction digest and removes any
sighash byte first. This implementation has vector coverage, not a proof of
cryptographic correctness or of refinement of the abstract signature oracle. -/
def verify (signature publicKey message : ByteArray) : Bool :=
  if signature.size ≠ 64 || publicKey.size ≠ 32 then false
  else
    let r := decodeBE (signature.extract 0 32)
    let s := decodeBE (signature.extract 32 64)
    if r ≥ field || s ≥ order then false
    else match liftX (decodeBE publicKey) with
    | none => false
    | some point =>
        let challenge := decodeBE (taggedHash "BIP0340/challenge"
          (signature.extract 0 32 ++ publicKey ++ message)) % order
        match pointAdd (pointMul generator s) (pointMul (some point) (order - challenge)) with
        | none => false
        | some (x, y) => y % 2 == 0 && x == r

end LeanMiniscript.Bitcoin.Schnorr
