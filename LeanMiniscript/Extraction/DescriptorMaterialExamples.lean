import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Extraction.DescriptorSatisfaction
import LeanMiniscript.Extraction.DescriptorMaterialFixtures

namespace LeanMiniscript.Extraction.DescriptorMaterialExamples

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript
open DescriptorMaterialFixtures

private def flags : CoreVerificationFlags :=
  { witness := true, taproot := true, cleanStack := true
    checkLockTimeVerify := true, checkSequenceVerify := true }

private def keyA := PubKey.ofBytes key3
private def keyB := PubKey.ofBytes key7
private def keyC := PubKey.ofBytes key11
private def branch : CoreFragment := .or_i (.c (.pk_k keyA)) (.c (.pk_k keyB))
private def multi : CoreFragment := .multi_a 2 [keyA, keyB, keyC]
private def hashBranch : CoreFragment := .or_i
  (.and_v (.v (.c (.pk_k keyA))) (.sha256 (Hash256.ofBytes hash0)))
  (.and_v (.v (.c (.pk_k keyB))) (.sha256 (Hash256.ofBytes hash1)))

private def flip (bytes : ByteArray) : ByteArray :=
  ⟨bytes.data.set! 40 (bytes[40]! ^^^ 1)⟩

private def material (signatures : List (PubKey × ByteArray))
    (preimages : HashLock → Option ByteArray := fun _ => none) : DescriptorSatisfactionMaterial :=
  { signatureFor := fun key => (signatures.find? (fun entry => entry.1.bytes == key.bytes)).map (·.2)
    preimageFor := preimages
    nonPreimageFor := fun _ => ⟨Array.replicate 32 0⟩ }

private def setup (fragment : CoreFragment) :
    Except String (CompiledDescriptor × TaprootLeafSpendInfo × Array TxOutput × TxContext) := do
  let descriptor ← compileOutputDescriptor
    (.tr (PubKey.ofBytes internalKey) (some (.leaf (.core fragment))))
  let leaf ← match descriptor.taprootLeaves with
    | [leaf] => pure leaf
    | _ => throw "Expected one leaf"
  let spentOutputs := sighashFixtureSpentOutputs.modify 0
    (fun output => { output with scriptPubKey := descriptor.scriptPubKey })
  let context ← (TxContext.fromTaproot
    { transaction := sighashFixtureTransaction, spentOutputs, inputIndex := 0
      spendPath := .scriptPath leaf.script 0xc0 0xffffffff }).mapError (fun error => reprStr error)
  return (descriptor, leaf, spentOutputs, context)

private def generate (fragment : CoreFragment) (supplied : DescriptorSatisfactionMaterial) :
    Except String (Except DescriptorSatisfactionError PreparedDescriptorSatisfaction) := do
  let (descriptor, _, spentOutputs, _) ← setup fragment
  return satisfyDescriptorTransaction CryptoOracle.pureLeanSchnorr flags descriptor 0 supplied
    sighashFixtureTransaction spentOutputs 0

-- Check independently generated Core scripts and outputs before testing the
-- signatures produced by the pinned BIP340 reference implementation.
example : [(branch, branchScript, branchOutput), (multi, multiScript, multiOutput),
    (hashBranch, hashBranchScript, hashBranchOutput)].all (fun (fragment, script, output) =>
      match setup fragment with
      | .ok (descriptor, leaf, _, _) => leaf.script == script && descriptor.scriptPubKey == output
      | .error _ => false) = true := by native_decide

/-- Exhibit the original choice and its Core failure, then require the
validated entry to return the alternative witness after complete verification. -/
private def recovers (fragment : CoreFragment) (supplied : DescriptorSatisfactionMaterial)
    (before after : Witness) (error : CoreVerificationError) : Bool :=
  match setup fragment with
  | .error _ => false
  | .ok (descriptor, leaf, spentOutputs, context) =>
    let execute := executeCoreScript flags context (fun _ _ => CryptoOracle.pureLeanSchnorr)
    let checked := verifyCoreScripts execute (fun witness version program isP2SH =>
      verifyCoreWitnessProgram execute flags witness version program isP2SH)
      flags ByteArray.empty descriptor.scriptPubKey (before ++ [leaf.script, leaf.controlBlock])
    satisfyFinal fragment (supplied.toEnv context) == some before &&
      (match checked with | .error actual => actual == error | .ok _ => false) &&
      (match satisfyDescriptorTransaction CryptoOracle.pureLeanSchnorr flags descriptor 0 supplied
          sighashFixtureTransaction spentOutputs 0 with
       | .error _ => false
       | .ok prepared => prepared.arguments == after)

private def branchMaterial := material [(keyA, branchSig3Mode1), (keyB, flip branchSig7Mode0)]

-- The bad 64-byte right signature is cheaper than the valid explicit-ALL
-- signature on the left. Filtering permits the left branch to be selected.
example : recovers branch branchMaterial
    [flip branchSig7Mode0, falseElement] [branchSig3Mode1, trueElement]
    (.script .schnorrSig) = true := by native_decide

private def multiMaterial := material
  [(keyA, flip multiSig3Mode0), (keyB, multiSig7Mode0), (keyC, multiSig11Mode1)]

-- A failed first key becomes the empty slot; the two valid later keys fund
-- the exact two-of-three witness in reverse key order.
example : recovers multi multiMaterial
    [falseElement, multiSig7Mode0, flip multiSig3Mode0]
    [multiSig11Mode1, multiSig7Mode0, falseElement]
    (.script .schnorrSig) = true := by native_decide

private def wrongPreimage : ByteArray := ⟨Array.replicate 32 0⟩
private def hashMaterial := material [(keyA, hashBranchSig3Mode0), (keyB, hashBranchSig7Mode0)]
  (fun lock => if lock.expected == hash0 then some preimage0 else some wrongPreimage)

-- Both signatures verify. The cheaper right branch has an incorrect digest;
-- preimage filtering selects the left branch and its valid 32-byte preimage.
example : recovers hashBranch hashMaterial
    [wrongPreimage, hashBranchSig7Mode0, falseElement]
    [preimage0, hashBranchSig3Mode0, trueElement]
    (.script .evalFalse) = true := by native_decide

private def unavailable (fragment : CoreFragment) (supplied : DescriptorSatisfactionMaterial) : Bool :=
  match generate fragment supplied with
  | .ok (.error .unavailable) => true
  | _ => false

example : unavailable branch (material
    [(keyA, flip branchSig3Mode1), (keyB, flip branchSig7Mode0)]) = true := by native_decide

example : unavailable multi (material
    [(keyA, flip multiSig3Mode0), (keyB, multiSig7Mode0)]) = true := by native_decide

-- With valid material on both sides, the existing cost rule selects the
-- cheaper right witness, including its false selector.
example : (match generate branch (material [(keyA, branchSig3Mode1), (keyB, branchSig7Mode0)]) with
  | .ok (.ok prepared) => prepared.arguments == [branchSig7Mode0, falseElement]
  | _ => false) = true := by native_decide

example : (match generate hashBranch
    (material [(keyA, hashBranchSig3Mode0), (keyB, hashBranchSig7Mode0)]
      (fun lock => if lock.expected == hash0 then some preimage0 else some preimage1)) with
  | .ok (.ok prepared) => prepared.arguments == [preimage1, hashBranchSig7Mode0, falseElement]
  | _ => false) = true := by native_decide

-- Encoding rejection also removes a cheaper candidate. An explicit zero
-- sighash suffix is invalid; empty and truncated signatures are unavailable.
example : [ByteArray.empty, branchSig7Mode0.extract 0 63,
    branchSig7Mode0 ++ ⟨#[0]⟩].all (fun bad =>
      match generate branch (material [(keyA, branchSig3Mode1), (keyB, bad)]) with
      | .ok (.ok prepared) => prepared.arguments == [branchSig3Mode1, trueElement]
      | _ => false) = true := by native_decide

-- Exercise every hash callback and the independent 32-byte preimage limit.
private def locks : List HashLock :=
  [.sha256 (Hash256.ofBytes (CryptoOracle.pureLeanSchnorr.sha256 preimage0)),
   .hash256 (Hash256.ofBytes (CryptoOracle.pureLeanSchnorr.hash256 preimage0)),
   .ripemd160 (Hash160.ofBytes (CryptoOracle.pureLeanSchnorr.ripemd160 preimage0)),
   .hash160 (Hash160.ofBytes (CryptoOracle.pureLeanSchnorr.hash160 preimage0))]

example : (match setup hashBranch with
  | .error _ => false
  | .ok (_, _, _, context) => locks.all fun lock =>
      let filter := fun bytes =>
        ((material [] (fun _ => some bytes)).validated CryptoOracle.pureLeanSchnorr
          flags.script context).preimageFor lock
      filter preimage0 == some preimage0 && filter wrongPreimage == none &&
        filter (preimage0.extract 0 31) == none) = true := by native_decide

-- Correct hashing cannot make a 31-byte value usable for a hashlock.
example : (match setup hashBranch with
  | .error _ => false
  | .ok (_, _, _, context) =>
      let short := preimage0.extract 0 31
      let lock := HashLock.sha256 (Hash256.ofBytes (CryptoOracle.pureLeanSchnorr.sha256 short))
      ((material [] (fun _ => some short)).validated CryptoOracle.pureLeanSchnorr
        flags.script context).preimageFor lock == none) = true := by native_decide

end LeanMiniscript.Extraction.DescriptorMaterialExamples
