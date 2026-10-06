import LeanMiniscript.Extraction.BitcoinCoreScriptExecution
import LeanMiniscript.Extraction.CoreFixtureTransaction
import LeanMiniscript.Bitcoin.ECDSA
import LeanMiniscript.Bitcoin.Schnorr

/-!
Transaction-backed signature callbacks for Bitcoin Core fixtures.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

private def fixtureSignatureOracle (fixture : CoreFixtureTransaction)
    (version : SignatureVersion) (scriptCode : ByteArray) : CryptoOracle :=
  CryptoOracle.pureLeanHashes
    (fun signature publicKey _ =>
      if signature.size == 0 then false
      else
        let hashType := UInt32.ofNat signature[signature.size - 1]!.toNat
        let digest := if version == .witnessV0 then
            Bitcoin.witnessV0SignatureHash fixture.spend fixture.inputIndex scriptCode
              fixture.amount hashType
          else Bitcoin.legacySignatureHash fixture.spend fixture.inputIndex scriptCode hashType
        match digest with
        | .error _ => false
        | .ok digest => Bitcoin.ECDSA.verify
            (signature.extract 0 (signature.size - 1)) publicKey digest)
    Bitcoin.Schnorr.verify

/-- Concrete fixture execution computes each reached signature's transaction
hash from its own hash-type byte and the retained original scriptCode. -/
def executeCoreFixtureScript (fixture : CoreFixtureTransaction)
    (flags : CoreVerificationFlags) : CoreScriptExecutor :=
  let ctx : TxContext := {
    version := fixture.spend.signedVersion
    locktime := fixture.spend.locktime.toNat
    sequence := (fixture.spend.inputs[fixture.inputIndex]!).sequence.toNat
    sigHash := ByteArray.empty
    taproot := some {
      transaction := fixture.spend
      spentOutputs := fixture.spentOutputs
      inputIndex := fixture.inputIndex } }
  executeCoreScript flags ctx (fixtureSignatureOracle fixture)

/-- Concrete BIP341 key-path verification shares the exact fixture transaction
and amount with script-path and witness-v0 execution. -/
def checkCoreFixtureKeyPath (fixture : CoreFixtureTransaction) : CoreKeyPathChecker :=
  fun signature publicKey annex => do
    (checkSchnorrSignatureEncoding signature).mapError .script
    let context : Bitcoin.TaprootSigHashContext := {
      transaction := fixture.spend
      spentOutputs := fixture.spentOutputs
      inputIndex := fixture.inputIndex
      annex := annex }
    let digest ← (Bitcoin.taprootSignatureHash context
      (if signature.size == 65 then signature[64]! else 0)).mapError
        (fun _ => CoreVerificationError.script .schnorrSigHashType)
    if Bitcoin.Schnorr.verify (signature.extract 0 64) publicKey digest then return ()
    else throw (.script .schnorrSig)

end LeanMiniscript.Extraction
