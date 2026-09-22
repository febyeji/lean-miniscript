import LeanMiniscript.Extraction.Taproot
import LeanMiniscript.Script.Codec.Deserialization

namespace LeanMiniscript.Extraction

open Script Bitcoin

/-- Errors for canonical wire-witness verification. Decoding an unsupported
    opcode and rejecting a non-canonical encoding describe this API's support
    boundary; neither is a claim that Bitcoin consensus rejects that script. -/
inductive CanonicalTapscriptVerificationError where
  | setup (error : TaprootScriptPathError)
  | decode (error : DeserializationError)
  | nonCanonicalScript
  | script (error : ScriptError)
  deriving Repr, DecidableEq

/-- Embed the existing AST verifier's errors without losing their category. -/
def CanonicalTapscriptVerificationError.ofVerification :
    TaprootVerificationError → CanonicalTapscriptVerificationError
  | .setup error => .setup error
  | .script error => .script error

/-- Decode the modeled opcode subset and require its canonical serialization
    to equal the original bytes. In particular, this API does not silently
    rewrite non-minimal pushes before witness binding or signature hashing. -/
def decodeCanonicalTapscript (bytes : ByteArray) :
    Except CanonicalTapscriptVerificationError Script := do
  let script ← (deserializeScript bytes).mapError CanonicalTapscriptVerificationError.decode
  match serializeScript script with
  | .error _ => throw .nonCanonicalScript
  | .ok encoded =>
      if encoded.data = bytes.data then return script
      else throw .nonCanonicalScript

/-- Verify a native P2TR script-path witness without a caller-supplied AST.
    Setup and commitment checks precede decoding and the canonical-encoding
    boundary, followed by the existing flag, initial/runtime resource, and
    final acceptance checks. Success returns the unused signature budget.

    This API supports canonical encodings of the modeled opcode subset.
    OP_SUCCESSx, arbitrary raw scripts, key paths and future leaf versions are
    outside its scope. Transaction validity and prevout provenance retain the
    existing extraction boundary's assumptions. -/
def verifyCanonicalTapscriptTransaction (oracle : CryptoOracle)
    (fullWitness : List ByteArray) (flags : ScriptFlags)
    (transaction : Transaction) (spentOutputs : Array TxOutput) (inputIndex : Nat) :
    Except CanonicalTapscriptVerificationError Nat := do
  let prepared ← (prepareCommittedTapscriptTransaction
    fullWitness transaction spentOutputs inputIndex).mapError
      CanonicalTapscriptVerificationError.setup
  let script ← decodeCanonicalTapscript prepared.witness.scriptBytes
  (Miniscript.checkTapscriptAcceptance oracle script prepared.witness flags
    prepared.context).mapError CanonicalTapscriptVerificationError.script

end LeanMiniscript.Extraction
