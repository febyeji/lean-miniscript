import LeanMiniscript.Extraction.BitcoinCoreVerification
import LeanMiniscript.Miniscript.OutputDescriptor
import LeanMiniscript.Miniscript.Satisfaction
import LeanMiniscript.Bitcoin.TaprootSighashExamples
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Script.RuntimeCompletenessProofs

namespace LeanMiniscript.Extraction.BitcoinCoreSatisfactionExamples

open LeanMiniscript.Script LeanMiniscript.Bitcoin LeanMiniscript.Miniscript

private instance : DecidableEq (Except CoreVerificationError Unit) := by
  intro a b
  cases a <;> cases b
  · rename_i first second
    exact decidable_of_iff (first = second) (by simp)
  · exact isFalse (by intro same; cases same)
  · exact isFalse (by intro same; cases same)
  · exact isTrue (by congr)

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩

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

private def prepare (transaction : Transaction) :
    Except String (CompiledDescriptor × TaprootLeafSpendInfo × Witness × TxContext) := do
  let descriptor ← compileOutputDescriptor (.tr internalKey (some (.leaf (.pk key))))
  let leaf ← match descriptor.taprootLeaves with
    | [leaf] => pure leaf
    | _ => throw "Expected one descriptor leaf"
  let spentOutputs := sighashFixtureSpentOutputs.modify 0
    (fun output => { output with scriptPubKey := descriptor.scriptPubKey })
  let ctx ← (TxContext.fromTaproot
    { transaction, spentOutputs, inputIndex := 0
      spendPath := .scriptPath leaf.script 0xc0 0xffffffff }).mapError
        (fun _ => "Invalid transaction context")
  let env : SatEnv :=
    { signatureFor := fun selected => if selected.bytes == key.bytes then some signature else none
      preimageFor := fun _ => none
      nonPreimageFor := fun _ => ByteArray.empty
      txCtx := ctx }
  let arguments ← match satisfyFinal (desugar leaf.fragment) env with
    | some arguments => pure arguments
    | none => throw "No generated satisfaction"
  return (descriptor, leaf, arguments, ctx)

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

-- This generated descriptor spend meets the new theorem's static resource
-- premises, with the actual wire witness supplying the signature budget.
example : (match prepare sighashFixtureTransaction with
  | .ok (_, leaf, arguments, _) => match checkSaneSurface .tapscript leaf.fragment with
    | .ok sane =>
        sane.compile.all (fun element => element.pushSize ≤ maxScriptElementSize) &&
        arguments.all (fun item => item.size ≤ maxScriptElementSize) &&
        staticValidationWeight sane.compile ≤
          (serializeWitness (arguments ++ [leaf.script, leaf.controlBlock])).size + 50
    | .error _ => false
  | .error _ => false) = true := by native_decide

example : (run (fun witness => witness.modify 0 (fun sig => flip sig 40))).toOption =
    some (.error (.script .schnorrSig)) := by native_decide

example : (run id { sighashFixtureTransaction with
    locktime := sighashFixtureTransaction.locktime + 1 }).toOption =
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

end LeanMiniscript.Extraction.BitcoinCoreSatisfactionExamples
