import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Miniscript.OutputDescriptor
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Script.RuntimeCompletenessProofs
import LeanMiniscript.Extraction.DescriptorSatisfaction

namespace LeanMiniscript.Extraction.BitcoinCoreSatisfactionExamples

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

open LeanMiniscript.TestSupport (hex)

-- The real transaction signature also used by TaprootExamples. Here the
-- descriptor compiler supplies the output, script and control block, and
-- satisfyFinal supplies the arguments before the complete Core verifier runs.
private def key : PubKey := PubKey.ofBytes
  (hex "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9")
private def internalKey : PubKey := PubKey.ofBytes
  (hex "2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4")
private def signature := hex
  "8c05c0ee555979c2de9025bc3664cb322783a198339d3d458c3d73b4364f235444e98c7661e6010ac1ffbb07a2c68f87a407ac4f089a5dd1ff88574524a53a48"
private def flags : CoreVerificationFlags :=
  { witness := true, taproot := true, cleanStack := true, sigPushOnly := true
    checkLockTimeVerify := true, checkSequenceVerify := true
    discourageOpSuccess := true, discourageUpgradableTaprootVersion := true }

private def material : DescriptorSatisfactionMaterial :=
  { signatureFor := fun selected => if selected.bytes == key.bytes then some signature else none
    preimageFor := fun _ => none
    nonPreimageFor := fun _ => ByteArray.empty }

private def prepare (transaction : Transaction) :
    Except String (CompiledDescriptor × TaprootLeafSpendInfo × Witness × TxContext) := do
  let descriptor ← compileOutputDescriptor (.tr internalKey (some (.leaf (.pk key))))
  let spentOutputs := sighashFixtureSpentOutputs.modify 0
    (fun output => { output with scriptPubKey := descriptor.scriptPubKey })
  let prepared ← (prepareDescriptorSatisfaction CryptoOracle.pureLeanSchnorr flags.script descriptor 0 material transaction spentOutputs 0).mapError
    (fun error => reprStr error)
  return (descriptor, prepared.leaf, prepared.arguments, prepared.context)

private def run (mutate : Witness → Witness := id)
    (transaction : Transaction := sighashFixtureTransaction)
    (scriptSig : ByteArray := ByteArray.empty) :
    Except String (Except CoreVerificationError Unit) := do
  let (descriptor, leaf, arguments, ctx) ← prepare transaction
  let execute := executeCoreScript flags ctx (fun _ _ => CryptoOracle.pureLeanSchnorr)
  return verifyCoreScripts execute (fun witness version program isP2SH =>
    verifyCoreWitnessProgram execute flags witness version program isP2SH)
    flags scriptSig descriptor.scriptPubKey (mutate (arguments ++ [leaf.script, leaf.controlBlock]))

private def flip (bytes : ByteArray) (index : Nat) : ByteArray :=
  ⟨bytes.data.set! index (bytes[index]! ^^^ 1)⟩

example : (match prepare sighashFixtureTransaction with
  | .ok (descriptor, leaf, arguments, _) =>
      descriptor.scriptPubKey == hex "5120bf6cf4c0026f57cab510d2014e34e8bad549e5370ed343b1e333fc5a3b066413" &&
      leaf.controlBlock == hex "c02f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4" &&
      arguments == [signature]
  | .error _ => false) = true := by native_decide

example : (run).toOption = some (.ok ()) := by native_decide

-- The generated descriptor spend satisfies the push and witness item limits.
-- Its active signature debit is funded by the serialized witness.
example : (match prepare sighashFixtureTransaction with
  | .ok (_, leaf, arguments, _) => match checkSaneSurface .tapscript leaf.fragment with
    | .ok sane =>
        sane.compile.all (fun element => element.pushSize ≤ maxScriptElementSize) &&
        arguments.all (fun item => item.size ≤ maxScriptElementSize)
    | .error _ => false
  | .error _ => false) = true := by native_decide

example : (run (fun witness => witness.modify 0 (fun sig => flip sig 40))).toOption =
    some (.error (.script .schnorrSig)) := by native_decide

example : (run (fun witness => witness.modify 1 (· ++ hex "00"))).toOption =
    some (.error .witnessProgramMismatch) := by native_decide

example : (run (fun witness => witness.modify 2 (fun control => flip control 0))).toOption =
    some (.error .witnessProgramMismatch) := by native_decide

example : (run (fun witness => witness.modify 0 (fun _ => ByteArray.empty))).toOption =
    some (.error (.script .evalFalse)) := by native_decide

example : (run (ByteArray.empty :: ·)).toOption =
    some (.error (.script .cleanStack)) := by native_decide

-- The initial 1000 arguments fit; pushing the committed key exceeds the
-- runtime stack limit before the signature can be consumed.
example : (run (List.replicate 999 ByteArray.empty ++ ·)).toOption =
    some (.error (.script .stackSize)) := by native_decide

example : (run id sighashFixtureTransaction (hex "51")).toOption =
    some (.error .witnessMalleated) := by native_decide

-- Exercise the complete generation/verification entry with the same real
-- signature, including setup failures before cryptographic verification.
private def verified
    (supplied : DescriptorSatisfactionMaterial := material)
    (transaction : Transaction := sighashFixtureTransaction)
    (leafIndex : Nat := 0) (inputIndex : Nat := 0)
    (mutateOutputs : Array TxOutput → Array TxOutput := id)
    (verifyFlags : CoreVerificationFlags := flags)
    (tree : Option DescriptorTree := some (.leaf (.pk key))) :
    Except String (Except DescriptorSatisfactionError Witness) := do
  let descriptor ← compileOutputDescriptor (.tr internalKey tree)
  let spentOutputs := mutateOutputs (sighashFixtureSpentOutputs.modify 0
    (fun output => { output with scriptPubKey := descriptor.scriptPubKey }))
  return (satisfyDescriptorTransaction CryptoOracle.pureLeanSchnorr verifyFlags
    descriptor leafIndex supplied transaction spentOutputs inputIndex).map (·.witness)

private def hasError (result : Except String (Except DescriptorSatisfactionError Witness))
    (expected : DescriptorSatisfactionError) : Bool :=
  match result with
  | .ok (.error actual) => decide (actual = expected)
  | _ => false

example : (match verified with
  | .ok (.ok witness) => witness == [signature,
      hex "20f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9ac",
      hex "c02f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"]
  | _ => false) = true := by native_decide

example : hasError (verified { material with signatureFor := fun _ => none })
    .unavailable = true := by native_decide

example : hasError (verified { material with
    signatureFor := fun _ => some (flip signature 40) })
    .unavailable = true := by native_decide

example : hasError (verified material { sighashFixtureTransaction with
    locktime := sighashFixtureTransaction.locktime + 1 })
    .unavailable = true := by native_decide

example : hasError (verified (leafIndex := 1)) .leafIndex = true := by native_decide

example : hasError (verified (inputIndex := sighashFixtureTransaction.inputs.size))
    (.context .inputIndex) = true := by native_decide

example : hasError (verified (mutateOutputs := fun _ => #[]))
    (.context .spentOutputCount) = true := by native_decide

example : hasError (verified (mutateOutputs := fun outputs => outputs.modify 0
    (fun output => { output with scriptPubKey := ByteArray.empty })))
    .spentOutputMismatch = true := by native_decide

example : hasError (verified (transaction := { sighashFixtureTransaction with
    inputs := sighashFixtureTransaction.inputs.modify 0
      (fun input => { input with scriptSig := hex "51" }) }))
    .nonemptyScriptSig = true := by native_decide

example : hasError (verified (verifyFlags := { flags with witness := false }))
    .witnessDisabled = true := by native_decide

example : hasError (verified (verifyFlags := { flags with taproot := false }))
    .taprootDisabled = true := by native_decide

example : hasError (verified (tree := none)) .leafIndex = true := by native_decide

example : hasError (verified (tree := some (.leaf (.core .one))))
    (.notSane .signatureNotRequired) = true := by native_decide

-- The selected occurrence supplies the source, script and control path even
-- when it is not the first leaf. This setup test uses an accepting signature
-- callback; the full transaction tests above use concrete Schnorr verification.
-- Only the second key has supplied material.
private def prepareSecondLeaf (index : Nat) :
    Except String (Except DescriptorSatisfactionError Bool) := do
  let descriptor ← compileOutputDescriptor (.tr internalKey (some
    (.branch (.leaf (.pk internalKey)) (.leaf (.pk key)))))
  let spentOutputs := sighashFixtureSpentOutputs.modify 0
    (fun output => { output with scriptPubKey := descriptor.scriptPubKey })
  return (prepareDescriptorSatisfaction
    (CryptoOracle.pureLeanHashes (fun _ _ _ => false) (fun _ _ _ => true)) flags.script
    descriptor index material
    sighashFixtureTransaction spentOutputs 0).map fun prepared =>
      match descriptor.taprootLeaves[1]? with
      | none => false
      | some leaf => prepared.leaf.script == leaf.script &&
          prepared.leaf.controlBlock == leaf.controlBlock &&
          prepared.witness == [signature, leaf.script, leaf.controlBlock] &&
          leaf.controlBlock.size == 65

example : (match prepareSecondLeaf 1 with
  | .ok (.ok result) => result
  | _ => false) = true := by native_decide

example : (match prepareSecondLeaf 0 with
  | .ok (.error .unavailable) => true
  | _ => false) = true := by native_decide

end LeanMiniscript.Extraction.BitcoinCoreSatisfactionExamples
